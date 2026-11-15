// parse.js — a fast drop-in for marked 18.1.3 (default options: GFM on,
// breaks off, pedantic off, async off). parse(markdown) returns exactly the
// HTML marked.parse(markdown) returns, byte for byte.
//
// Written from scratch for markdown-render-speed-02. The matching grammar
// (the regular expressions that define marked's exact edge-case behaviour)
// is adapted from marked 18.1.3 (MIT, Copyright (c) 2018-2026 MarkedJS;
// see kit baselines/vendor/marked/). Everything else — the single-pass
// block scanner, the inline tokenizer that renders straight to a string,
// and the renderer — is original code written for this entry.
//
// Design: one parse() call is fully self-contained (no state is kept
// between calls, nothing is cached across cases). Blocks are scanned once
// into a small token list; inline sources are queued while block lexing
// runs (link definitions may appear after their uses), then each queued
// inline source is rendered directly to an HTML string. Emphasis and
// strikethrough use marked's masking pass so delimiter search sees the
// same masked source marked does.

const BLOCK_TAGS =
  'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

// Indent-parameterised block-start regexes, cached per indent (0..3) the
// same way marked caches them: slot = max(0, min(3, indent - 1)).
function cachedRx(cache, make) {
  return (indent) => {
    const slot = Math.max(0, Math.min(3, indent - 1));
    return cache[slot] || (cache[slot] = make(slot));
  };
}
const listItemRx = (bullet) => new RegExp(`^( {0,3}${bullet})((?:[ \t][^\\n]*)?(?:\\n|$))`);
const nextBulletRxCache = [];
const nextBulletRx = cachedRx(nextBulletRxCache, (a) => new RegExp(`^ {0,${a}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`));
const hrRxCache = [];
const hrRx = cachedRx(hrRxCache, (a) => new RegExp(`^ {0,${a}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fencesBeginRxCache = [];
const fencesBeginRx = cachedRx(fencesBeginRxCache, (a) => new RegExp(`^ {0,${a}}(?:\`\`\`|~~~)`));
const headingBeginRxCache = [];
const headingBeginRx = cachedRx(headingBeginRxCache, (a) => new RegExp(`^ {0,${a}}#{1,6}(?:\\s|$)`));
const htmlBeginRxCache = [];
const htmlBeginRx = cachedRx(htmlBeginRxCache, (a) => new RegExp(`^ {0,${a}}(?:</?(?:${BLOCK_TAGS})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRxCache = [];
const blockquoteBeginRx = cachedRx(blockquoteBeginRxCache, (a) => new RegExp(`^ {0,${a}}>`));

// ---- small helpers (same semantics as marked's) ----

const ESC_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
// Escape HTML. encode=true escapes all five characters; otherwise an
// ampersand that starts a valid entity / numeric reference is left alone.
function esc(s, encode) {
  if (encode) {
    if (T_ESC_TEST.test(s)) return s.replace(T_ESC_REP, (ch) => ESC_MAP[ch]);
  } else if (T_ESC_TEST_NE.test(s)) {
    return s.replace(T_ESC_REP_NE, (ch) => ESC_MAP[ch]);
  }
  return s;
}

// Decode numeric character references (&#65; &#x41;), as marked does:
// 0, > 0x10FFFF or a surrogate becomes U+FFFD; 38 becomes "&amp;".
function decodeEntities(s) {
  if (!T_NUM_REF.test(s)) return s;
  return s.replace(T_NUM_REF_AMP, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = hex === undefined ? parseInt(dec, 10) : parseInt(hex, 16);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}

// Strip trailing characters equal to `ch` from `s` (or, when `not` is
// set, trailing characters NOT equal to `ch`).
function stripTrail(s, ch, not) {
  let n = s.length, k = 0;
  while (k < n) {
    const c = s.charAt(n - k - 1);
    if (c === ch && !not) k++;
    else if (c !== ch && not) k++;
    else break;
  }
  return s.slice(0, n - k);
}

// Expand tabs to spaces starting at column `col`.
function expandTabs(s, col = 0) {
  let out = '', c = col;
  for (const ch of s) {
    if (ch === '\t') {
      const r = 4 - (c % 4);
      out += ' '.repeat(r);
      c += r;
    } else {
      out += ch;
      c++;
    }
  }
  return out;
}

// Indented code blocks: drop at most one trailing blank line's worth of
// blank lines (marked keeps the raw text when there is at most one).
function trimCodeBlock(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  while (t >= 0 && T_BLANK.test(lines[t])) t--;
  if (lines.length - t <= 2) return s;
  return lines.slice(0, t + 1).join('\n');
}

// Normalise a link label for lookup: trim, collapse whitespace, fold case.
function normLabel(s) {
  return s.trim().replace(T_MULTI_SPACE, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Parenthesis/bracket balance: index of an unmatched closer, -2 when an
// opener is left unmatched, -1 when balanced.
function parenBalance(s, pair) {
  if (s.indexOf(pair[0]) === -1 && s.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') { i++; continue; }
    if (s[i] === pair[0]) depth++;
    else if (s[i] === pair[1]) { depth--; if (depth < 0) return i; }
  }
  return depth > 0 ? -2 : -1;
}

// Split a table row on unescaped pipes, honouring the header count.
function splitTableRow(s, count) {
  const t = s.replace(T_FIND_PIPE, (m, off, str) => {
    let escaped = false, p = off;
    while (--p >= 0 && str[p] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = t.split(T_SPLIT_PIPE);
  let i = 0;
  if (cells[0].trim() || cells.shift(), cells.length > 0 && !cells.at(-1)?.trim() && cells.pop(), count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(T_SLASH_PIPE, '|');
  return cells;
}

// Fenced-code indent compensation: strip the fence's own indent from the
// body lines that carry at least that much leading space.
function fenceIndentComp(fenceRaw, body, rules) {
  const m = fenceRaw.match(T_INDENT_COMP);
  if (m === null) return body;
  const indent = m[1];
  return body.split('\n').map((line) => {
    const sp = line.match(T_BEGIN_SPACE);
    if (sp === null) return line;
    const [w] = sp;
    return line.slice(Math.min(w.length, indent.length));
  }).join('\n');
}

// Column of the first non-space character, counting each tab as 4
// (marked's `m.replace(/\t/g, "    ").search(/[^ ]/)`), or -1 if none.
function firstNonSpaceCol(s) {
  let col = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 9) col += 4;
    else if (c === 32) col++;
    else return col;
  }
  return -1;
}

// encodeURI for link/image hrefs, with %25 put back to %.
function encodeHref(s) {
  try {
    return encodeURI(s).replace(T_PCT_DECODE, '%');
  } catch {
    return null;
  }
}
const RX_NEWLINE = new RegExp("^(?:[ \\t]*(?:\\n|$))+", "");
const RX_CODE = new RegExp("^((?: {4}| {0,3}\\t)[^\\n]+(?:\\n(?:[ \\t]*(?:\\n|$))*)?)+", "");
const RX_FENCES = new RegExp("^ {0,3}(`{3,}(?=[^`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)(?:|([\\s\\S]*?)(?:\\n|$))(?: {0,3}(?:(?=`)\\1`*|(?=~)\\1~*) *(?=\\n|$)|$)", "");
const RX_HEADING = new RegExp("^ {0,3}(#{1,6})(?=\\s|$)(.*)(?:\\n+|$)", "");
const RX_HR = new RegExp("^ {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)", "");
const RX_BLOCKQUOTE = new RegExp("^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(([^\\n]+(?:\\n(?! {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)|[ \\t]+\\n)[^\\n]+)*))|[^\\n]*)(?:\\n|$))+", "");
const RX_LIST = new RegExp("^( {0,3}(?:[*+-]|\\d{1,9}[.)]))([ \\t][^\\n]*?)?(?:\\n|$)", "");
const RX_HTML = new RegExp("^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:<\\/\\1>[^\\n]*\\n*|$)|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|<\\/?(address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \\t]+|\\n|\\/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\\w.:-]*(?: *= *\"[^\"\\n]*\"| *= *'[^'\\n]*'| *= *[^\\s\"'=<>`]+)?)*? *\\/?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<\\/[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))", "i");
const RX_DEF = new RegExp("^ {0,3}\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)((?:\"(?:\\\\[\\s\\S]|[^\"\\\\])*\"|'(?:\\\\[\\s\\S]|[^'\\\\\\n]|\\n(?!\\n))*'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))))? *(?:\\n+|$)", "");
const RX_TABLE = new RegExp("^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n| {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\\n]| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)).*(?:\\n|$))*)\\n*|$)", "");
const RX_LHEADING = new RegExp("^(?! {0,3}(?:[*+-]|\\d{1,9}[.)]) |(?: {4}| {0,3}\\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n)((?:.|\\n(?!\\s*?\\n| {0,3}(?:[*+-]|\\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)", "");
const RX_PARAGRAPH = new RegExp("^([^\\n]+(?:\\n(?! {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)| *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n| {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\\n]| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)).*(?:\\n|$))*)\\n*|$)|[ \\t]+\\n)[^\\n]+)*)", "");
const RX_TEXT = new RegExp("^[^\\n]+", "");
const IX_ESCAPE = new RegExp("^\\\\([!\"#$%&'()*+,\\-./:;<=>?@\\[\\]\\\\^_`{|}~])", "");
const IX_CODE = new RegExp("^(`+)([^`]|[^`][\\s\\S]*?[^`])\\1(?!`)", "");
const IX_BR = new RegExp("^( {2,}|\\\\)\\n(?!\\s*$)[ \\t]*", "");
const IX_TEXT = new RegExp("^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@)|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\\/\\/|(?<![^\\s*_~(])www\\.|$)|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-](?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@))))", "");
const IX_PUNCT = new RegExp("^((?![*_])[\\s\\p{P}\\p{S}])", "u");
const IX_EM_L = new RegExp("^(?:\\*+(?:((?!\\*)(?!~)[\\p{P}\\p{S}])|([^\\s*]))?)|^_+(?:((?!_)(?!~)[\\p{P}\\p{S}])|([^\\s_]))?", "u");
const IX_EM_R_AST = new RegExp("^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?=[\\s]|$)|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?!\\*)(?=(?!~)[\\s\\p{P}\\p{S}]|$)|(?!\\*)(?!~)[\\s\\p{P}\\p{S}](\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))|[\\s](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))", "gu");
const IX_EM_R_UND = new RegExp("^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)[\\p{P}\\p{S}](_+)(?=[\\s]|$)|[^\\s\\p{P}\\p{S}](_+)(?!_)(?=[\\s\\p{P}\\p{S}]|$)|(?!_)[\\s\\p{P}\\p{S}](_+)(?=[^\\s\\p{P}\\p{S}])|[\\s](_+)(?!_)(?=[\\p{P}\\p{S}])|(?!_)[\\p{P}\\p{S}](_+)(?!_)(?=[\\p{P}\\p{S}])", "gu");
const IX_DEL_L = new RegExp("^~~?(?:((?!~)[\\p{P}\\p{S}])|[^\\s~])", "u");
const IX_DEL_R = new RegExp("^[^~]+(?=[^~])|(?!~)[\\p{P}\\p{S}](~~?)(?=[\\s]|$)|[^\\s\\p{P}\\p{S}](~~?)(?!~)(?=[\\s\\p{P}\\p{S}]|$)|(?!~)[\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])|[\\s](~~?)(?!~)(?=[\\p{P}\\p{S}])|(?!~)[\\p{P}\\p{S}](~~?)(?!~)(?=[\\p{P}\\p{S}])|[^\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])", "gu");
const IX_DEL = new RegExp("^(~~?)(?=[^\\s~])((?:\\\\[\\s\\S]|[^\\\\])*?(?:\\\\[\\s\\S]|[^\\s~\\\\]))\\1(?=[^~]|$)", "");
const IX_AUTOLINK = new RegExp("^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\\s\\x00-\\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>", "");
const IX_URL = new RegExp("^(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])(?:\\/[A-Za-z0-9@.]+)?)|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])", "");
const IX_BACKPEDAL = new RegExp("(?:[^?!.,:;*_'\"~()&]+|\\([^)]*\\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'\"~)]+(?!$))+", "");
const IX_LINK = new RegExp("^!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\([ \\t\\n]*(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(\"(?:\\\\[\\s\\S]|[^\"\\\\])*\"|'(?:\\\\[\\s\\S]|[^'\\\\])*'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)))?[ \\t\\n]*\\)", "");
const IX_REFLINK = new RegExp("^!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\]", "");
const IX_NOLINK = new RegExp("^!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\](?:\\[\\])?", "");
const IX_REFLINK_SEARCH = new RegExp("!?\\[((?:[^\\[\\]\\\\`]*(?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\]|!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\](?:\\[\\])?(?!\\()", "g");
const IX_BLOCK_SKIP = new RegExp("\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>", "g");
const IX_ANY_PUNCT = new RegExp("\\\\([\\p{P}\\p{S}])", "gu");
const IX_ANY_PUNCT_CODE = new RegExp("(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\([\\p{P}\\p{S}])", "gu");
const IX_TAG = new RegExp("^<!--(?:-?>|[\\s\\S]*?-->)|^<\\/[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*\"[^\"]*\"|\\s*=\\s*'[^']*'|\\s*=\\s*[^\\s\"'=<>`]+)?)*?\\s*\\/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>", "");
const T_CODE_INDENT = new RegExp("^(?: {0,3}\\t| {1,4})", "gm");
const T_OUT_LINK = new RegExp("\\\\([\\[\\]])", "g");
const T_INDENT_COMP = new RegExp("^(\\s+)(?:```)", "");
const T_BEGIN_SPACE = new RegExp("^\\s+", "");
const T_END_HASH = new RegExp("#$", "");
const T_START_SPACE = new RegExp("^ ", "");
const T_END_SPACE = new RegExp(" $", "");
const T_END_SPACE_TAB = new RegExp("[ \\t]$", "");
const T_NON_SPACE = new RegExp("[^ ]", "");
const T_NL_GLOBAL = new RegExp("\\n", "g");
const T_TAB_GLOBAL = new RegExp("\\t", "g");
const T_LEAD_SPACE_TAB = new RegExp("^[ \\t]+", "");
const T_MULTI_SPACE = new RegExp("\\s+", "g");
const T_BLANK = new RegExp("^[ \\t]*$", "");
const T_DOUBLE_BLANK = new RegExp("\\n[ \\t]*\\n[ \\t]*$", "");
const T_BQ_START = new RegExp("^ {0,3}>", "");
const T_BQ_SETEXT = new RegExp("\\n {0,3}((?:=+|-+)[ \\t]*)(?=\\n|$)", "g");
const T_BQ_SETEXT2 = new RegExp("^ {0,3}>[ \\t]?", "gm");
const T_BQ_MARKER_WS = new RegExp("^( {0,3}>)([ \\t]+)", "gm");
const T_LIST_NEST = new RegExp("^ {1,4}(?=( {4})*[^ ])", "g");
const T_LIST_TASK = new RegExp("^\\[[ xX]\\][ \\t]+\\S", "");
const T_LIST_TASK_REP = new RegExp("^\\[[ xX]\\][ \\t]+", "");
const T_LIST_CHECKBOX = new RegExp("\\[[ xX]\\]", "");
const T_ANY_LINE = new RegExp("\\n.*\\n", "");
const T_HREF_BRACKETS = new RegExp("^<(.*)>$", "");
const T_TABLE_DELIM = new RegExp("[:|]", "");
const T_TABLE_ALIGN_CHARS = new RegExp("^\\||\\| *$", "g");
const T_TABLE_ROW_BLANK = new RegExp("\\n[ \\t]*$", "");
const T_TABLE_ALIGN_R = new RegExp("^ *-+: *$", "");
const T_TABLE_ALIGN_C = new RegExp("^ *:-+: *$", "");
const T_TABLE_ALIGN_L = new RegExp("^ *:-+ *$", "");
const T_START_A = new RegExp("^<a ", "i");
const T_END_A = new RegExp("^<\\/a>", "i");
const T_START_PRE = new RegExp("^<(pre|code|kbd|script)(\\s|>)", "i");
const T_END_PRE = new RegExp("^<\\/(pre|code|kbd|script)(\\s|>)", "i");
const T_START_ANGLE = new RegExp("^<", "");
const T_END_ANGLE = new RegExp(">$", "");
const T_UNICODE_ALNUM = new RegExp("[\\p{L}\\p{N}]", "u");
const T_NUM_REF = new RegExp("&#(?:(\\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));", "");
const T_NUM_REF_AMP = new RegExp("&#(?:(\\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\\w+);)", "g");
const T_ESC_TEST = new RegExp("[&<>\"']", "");
const T_ESC_REP = new RegExp("[&<>\"']", "g");
const T_ESC_TEST_NE = new RegExp("[<>\"']|&(?!(#\\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\\w+);)", "");
const T_ESC_REP_NE = new RegExp("[<>\"']|&(?!(#\\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\\w+);)", "g");
const T_CARET = new RegExp("(^|[^\\[])\\^", "g");
const T_PCT_DECODE = new RegExp("%25", "g");
const T_FIND_PIPE = new RegExp("\\|", "g");
const T_SPLIT_PIPE = new RegExp(" \\|", "");
const T_SLASH_PIPE = new RegExp("\\\\\\|", "g");
const T_CR = new RegExp("\\r\\n|\\r", "g");
const T_NOT_SPACE_START = new RegExp("^\\S*", "");
const T_END_NL = new RegExp("\\n$", "");

// ---- per-parse state (reset at the start of every parse() call) ----
let LINKS = null; // link reference definitions, keyed by normalised label
let QUEUE = null; // inline sources queued by block lexing: {src, html}
let IN_LINK = false; // inside a link label or an <a> tag
let IN_RAW = false; // inside a <pre>/<code>/<kbd>/<script> raw block
let LINK_EMITTED = false; // a link was emitted while lexing the current label
let LINK_PAREN = true; // current inline source contains ')'
let TOP = true; // block lexer is at the top level

// ---- inline masking (marked's emStrongMask) ----

// Whether a bracketed span in `s` contains a link (used by the masking pass).
function linkInText(s) {
  if (!s.includes('[')) return false;
  for (const m of s.matchAll(IX_BLOCK_SKIP)) {
    if (IX_LINK.test(m[0]) && s.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of s.matchAll(IX_REFLINK_SEARCH)) {
    const t = m[0], r = t.lastIndexOf('[');
    if (!(t.charAt(0) === '!' || !Object.hasOwn(LINKS, normLabel(t.slice(r + 1, -1)))) &&
        !(r > 1 && linkInText(t.slice(1, r - 1)))) return true;
  }
  return false;
}

// Mask an inline source for delimiter search: reference links become
// "[aaa...]", links/code spans/HTML become "[aaa...]", and punctuation
// outside code spans becomes "+". Length-preserving, so indices in the
// masked string match indices in the original.
function maskInline(src) {
  let t = src;
  if (src.includes('[')) {
    const re = IX_REFLINK_SEARCH;
    const sub = (r) => {
      const o = r.lastIndexOf('[');
      if (!Object.hasOwn(LINKS, normLabel(r.slice(o + 1, -1)))) return r;
      if (o > 1 && r.charAt(0) !== '!') {
        const inner = r.slice(1, o - 1);
        if (linkInText(inner)) return '[' + inner.replace(re, sub) + '][' + 'a'.repeat(r.length - o - 2) + ']';
      }
      return '[' + 'a'.repeat(r.length - 2) + ']';
    };
    t = t.replace(re, sub);
  }
  if (t.includes('`') || t.includes('\\')) {
    t = t.replace(IX_ANY_PUNCT_CODE, (n, s, r) =>
      r ? '+'.repeat(n.length)
        : s ? s + n.slice(s.length, -s.length).replace(/`/g, '+') + s
        : n);
  }
  if (t.includes('[') || t.includes('`') || t.includes('<')) {
    t = t.replace(IX_BLOCK_SKIP, (n) => '[' + 'a'.repeat(n.length - 2) + ']');
  }
  return t;
}

// Last index in `masked` where each delimiter could close emphasis
// (a run whose preceding character is not whitespace), and for '~'.
function computeClosers(masked) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const r = masked[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const prev = s === 0 ? '\n' : masked[s - 1];
    let i = s + 1;
    while (i < n && masked[i] === r) i++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (r === '~') del = s;
      else em[r] = s;
    }
    s = i - 1;
  }
  return { em, del };
}

// Does the link label contain an HTML tag or autolink that runs past the
// label's end (in which case the link is invalid)?
function labelHasOpenTag(src, label, off) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') { s++; continue; }
    if (label[s] === '`') {
      const m = IX_CODE.exec(label.slice(s));
      if (m) { s += m[0].length - 1; continue; }
    }
    if (label[s] !== '<') continue;
    const o = IX_TAG.exec(src.slice(off + s)) || IX_AUTOLINK.exec(src.slice(off + s));
    if (o) {
      if (o[0].length > label.length - s) return true;
      s += o[0].length - 1;
    }
  }
  return false;
}

// Shared link/image creation (marked's De): renders the label with
// inLink set, suppresses a non-image link whose label itself contains a
// link, and returns the HTML (or plain text in text mode).
function makeLink(m, href, title, raw, textMode) {
  const isImage = m[0].charAt(0) === '!';
  const label = m[1].replace(T_OUT_LINK, '$1');
  const savedLink = IN_LINK, savedEmitted = LINK_EMITTED, savedRaw = IN_RAW;
  IN_LINK = true;
  LINK_EMITTED = false;
  const inner = renderInline(label, textMode || isImage);
  const emitted = LINK_EMITTED;
  LINK_EMITTED = savedEmitted;
  IN_LINK = savedLink;
  if (!isImage) {
    if (emitted) { IN_RAW = savedRaw; return null; }
    LINK_EMITTED = true;
  }
  if (textMode) return { html: inner, len: raw.length };
  if (isImage) {
    const enc = encodeHref(href);
    if (enc === null) return { html: esc(inner), len: raw.length };
    let o = `<img src="${esc(enc)}" alt="${esc(inner)}"`;
    if (title) o += ` title="${esc(title)}"`;
    return { html: o + '>', len: raw.length };
  }
  const enc = encodeHref(href);
  if (enc === null) return { html: inner, len: raw.length };
  let o = `<a href="${esc(enc)}"`;
  if (title) o += ` title="${esc(title)}"`;
  return { html: o + '>' + inner + '</a>', len: raw.length };
}

// Inline link [label](href "title").
function tryLink(src, i, textMode) {
  if (!LINK_PAREN) return null;
  const m = IX_LINK.exec(src.slice(i));
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(src.slice(i), m[1], off)) return null;
  const s = m[2].trim();
  if (T_START_ANGLE.test(s)) {
    if (!T_END_ANGLE.test(s)) return null;
    const stripped = stripTrail(s.slice(0, -1), '\\');
    if ((s.length - stripped.length) % 2 === 0) return null;
  } else {
    const bal = parenBalance(m[2], '()');
    if (bal === -2) return null;
    if (bal > -1) {
      const h = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + bal;
      m[2] = m[2].substring(0, bal);
      m[0] = m[0].substring(0, h).trim();
      m[3] = '';
    }
  }
  const r = stripTrail(m[0].slice(0, -1), '\\');
  if ((m[0].length - r.length) % 2 === 0) return null;
  let href = m[2].trim();
  if (T_START_ANGLE.test(href)) href = href.slice(1, -1);
  const title = m[3] ? m[3].slice(1, -1) : '';
  return makeLink(m, href.replace(IX_ANY_PUNCT, '$1'), title.replace(IX_ANY_PUNCT, '$1'), m[0], textMode);
}

// Reference / shortcut link [label][ref] or [label].
function tryReflink(src, i, textMode) {
  let m = IX_REFLINK.exec(src.slice(i));
  if (!m) m = IX_NOLINK.exec(src.slice(i));
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(src.slice(i), m[1], off)) return null;
  const ref = LINKS[normLabel(m[2] || m[1])];
  if (!ref) {
    const first = m[0].charAt(0);
    return { html: textMode ? first : esc(first), len: 1 };
  }
  return makeLink(m, ref.href, ref.title, m[0], textMode);
}

// <scheme:...> and <email> autolinks.
function autolinkOut(m, textMode) {
  let text, href;
  if (m[2] === '@') { text = m[1]; href = 'mailto:' + text; }
  else { text = m[1]; href = text; }
  if (textMode) return text;
  const enc = encodeHref(href);
  if (enc === null) return esc(text, true);
  return '<a href="' + esc(enc, true) + '">' + esc(text, true) + '</a>';
}

// Extended autolinks: www., http(s)://, ftp://, bare emails, mailto:/xmpp:.
function tryUrl(src, i, textMode) {
  const m = IX_URL.exec(src.slice(i));
  if (!m) return null;
  let text, href;
  if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + text;
  } else {
    let t0 = m[0], prev;
    do {
      prev = t0;
      const b = IX_BACKPEDAL.exec(t0);
      t0 = b ? b[0] : '';
    } while (prev !== t0);
    text = t0;
    href = m[1] === 'www.' ? 'http://' + t0 : t0;
  }
  if (textMode) return { html: text, len: text.length };
  const enc = encodeHref(href);
  if (enc === null) return { html: esc(text, true), len: text.length };
  return { html: '<a href="' + esc(enc, true) + '">' + esc(text, true) + '</a>', len: text.length };
}

// Emphasis / strong emphasis (marked's emStrong), searching the masked
// source for a closer run.
function tryEmStrong(src, i, masked, closers, textMode, prevChar) {
  const m = IX_EM_L.exec(src.slice(i));
  if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return null;
  const delim = m[0][0];
  const openLeft = prevChar === delim;
  const pos = i;
  let l = pos;
  while (l > 0 && masked[l - 1] === delim) l--;
  const p = [...masked.slice(Math.max(0, l - 2), l)].at(-1) ?? '';
  const h = p === '*' || p === '_' || !!IX_PUNCT.exec(p);
  let n = prevChar;
  if (l < pos) n = p;
  const u = l < pos ? h : !!IX_PUNCT.exec(n);
  if (m[4] && T_UNICODE_ALNUM.test(n)) return null;
  const d = m[1] || m[3] || '';
  if (!d || !n || u) {
    const k = [...m[0]].length - 1;
    const y = pos - l + k;
    const R = !!p.trim() && (!!d || (delim === '*' && !h));
    if (delim !== '*' && delim !== '_') return null;
    const A = delim === '*' ? IX_EM_R_AST : IX_EM_R_UND;
    const v = closers.em[delim];
    const Q = pos + k;
    if (v < Q) return null;
    const sub = masked.slice(pos + k);
    const ee = v - Q;
    if (sub.indexOf(delim) === -1) return null;
    let mm = k, f = 0, s2;
    A.lastIndex = 0;
    while ((s2 = A.exec(sub)) !== null && !(s2.index > ee)) {
      const g = s2[1] || s2[2] || s2[3] || s2[4] || s2[5] || s2[6];
      if (!g) continue;
      const b = [...g].length;
      if (s2[3] || s2[4]) { mm += b; continue; }
      if (s2[5] || s2[6] || R) {
        if (openLeft && (s2[5] || s2[6])) break;
        if (y % 3 && !((y + b) % 3)) { f += b; continue; }
      }
      mm -= b;
      if (mm > 0) continue;
      const bb = Math.min(b, b + mm + f);
      const te = [...s2[0]][0].length;
      const M = src.slice(i, i + k + s2.index + te + bb);
      if (Math.min(k, bb) % 2) {
        const inner = M.slice(1, -1);
        return { html: textMode ? renderInline(inner, true) : '<em>' + renderInline(inner, false) + '</em>', len: M.length };
      }
      const inner = M.slice(2, -2);
      return { html: textMode ? renderInline(inner, true) : '<strong>' + renderInline(inner, false) + '</strong>', len: M.length };
    }
  }
  return null;
}

// Strikethrough (marked's del).
function tryDel(src, i, masked, closers, textMode, prevChar) {
  const m = IX_DEL_L.exec(src.slice(i));
  if (!m) return null;
  if (!((m[1] || '') === '' || !prevChar || IX_PUNCT.exec(prevChar))) return null;
  const o = [...m[0]].length - 1;
  const pos = i;
  const u = closers.del;
  const d = pos + o;
  if (u < d) return null;
  const sub = masked.slice(pos + o);
  const kk = u - d;
  if (sub.indexOf('~') === -1) return null;
  let p = o, s2;
  IX_DEL_R.lastIndex = 0;
  while ((s2 = IX_DEL_R.exec(sub)) !== null && !(s2.index > kk)) {
    const g = s2[1] || s2[2] || s2[3] || s2[4] || s2[5] || s2[6];
    if (!g) continue;
    const l = [...g].length;
    if (l !== o) continue;
    if (s2[3] || s2[4]) { p += l; continue; }
    p -= l;
    if (p > 0) continue;
    const ll = Math.min(l, l + p);
    const te = [...s2[0]][0].length;
    const raw = src.slice(i, i + o + s2.index + te + ll);
    const inner = raw.slice(o, -o);
    return { html: textMode ? renderInline(inner, true) : '<del>' + renderInline(inner, false) + '</del>', len: raw.length };
  }
  return null;
}

// Render one inline source to HTML (textMode: plain text, as marked's
// TextRenderer does for image alt text).
function renderInline(src, textMode) {
  const savedParen = LINK_PAREN;
  LINK_PAREN = savedParen && src.includes(')');
  try {
    return inlineLoop(src, textMode);
  } finally {
    LINK_PAREN = savedParen;
  }
}

function inlineLoop(src, textMode) {
  const hasMarkers = src.includes('*') || src.includes('_') || src.includes('~');
  const masked = hasMarkers ? maskInline(src) : src;
  const closers = hasMarkers ? computeClosers(masked) : { em: { '*': -1, '_': -1 }, del: -1 };
  let out = '';
  let i = 0;
  const n = src.length;
  let prevTextEnd = '';
  let wasText = false;
  while (i < n) {
    const r = wasText ? prevTextEnd : '';
    wasText = false;
    const ch = src[i];
    const rest = src.slice(i);
    if (ch === '\\') {
      const m = IX_ESCAPE.exec(rest);
      if (m) {
        out += textMode ? m[1] : esc(m[1]);
        i += m[0].length;
        continue;
      }
      const b = IX_BR.exec(rest);
      if (b) {
        if (!textMode) out += '<br>';
        i += b[0].length;
        continue;
      }
    } else if (ch === '<') {
      const m = IX_TAG.exec(rest);
      if (m) {
        const tag = m[0];
        if (!IN_LINK && T_START_A.test(tag)) IN_LINK = true;
        else if (IN_LINK && T_END_A.test(tag)) IN_LINK = false;
        if (!IN_RAW && T_START_PRE.test(tag)) IN_RAW = true;
        else if (IN_RAW && T_END_PRE.test(tag)) IN_RAW = false;
        out += tag;
        i += tag.length;
        continue;
      }
      const a = IX_AUTOLINK.exec(rest);
      if (a) {
        out += autolinkOut(a, textMode);
        i += a[0].length;
        continue;
      }
    } else if (ch === '[' || ch === '!') {
      const l = tryLink(src, i, textMode);
      if (l) { out += l.html; i += l.len; continue; }
      const rl = tryReflink(src, i, textMode);
      if (rl) { out += rl.html; i += rl.len; continue; }
    } else if (ch === '*' || ch === '_') {
      const em = tryEmStrong(src, i, masked, closers, textMode, r);
      if (em) { out += em.html; i += em.len; continue; }
      if (ch === '_') {
        const u = !IN_LINK ? tryUrl(src, i, textMode) : null;
        if (u) { out += u.html; i += u.len; continue; }
      }
    } else if (ch === '`') {
      const c = IX_CODE.exec(rest);
      if (c) {
        let text = c[2].replace(T_NL_GLOBAL, ' ');
        if (T_NON_SPACE.test(text) && T_START_SPACE.test(text) && T_END_SPACE.test(text)) {
          text = text.substring(1, text.length - 1);
        }
        out += textMode ? text : '<code>' + esc(text, true) + '</code>';
        i += c[0].length;
        continue;
      }
    } else if (ch === ' ') {
      const b = IX_BR.exec(rest);
      if (b) {
        if (!textMode) out += '<br>';
        i += b[0].length;
        continue;
      }
    } else if (ch === '~') {
      const d = tryDel(src, i, masked, closers, textMode, r);
      if (d) { out += d.html; i += d.len; continue; }
    } else if (!IN_LINK) {
      const u = tryUrl(src, i, textMode);
      if (u) { out += u.html; i += u.len; continue; }
    }
    const m = IX_TEXT.exec(rest);
    if (!m) throw new Error('Infinite loop on byte: ' + src.charCodeAt(i));
    const raw = m[0];
    const text = IN_RAW ? raw : decodeEntities(raw);
    out += textMode ? text : IN_RAW ? text : esc(text);
    prevTextEnd = raw.slice(-1) !== '_' ? raw.slice(-1) : '';
    wasText = true;
    i += raw.length;
  }
  return out;
}

// ---- block lexer ----

// Queue an inline source for rendering after block lexing (link
// definitions may appear after their uses).
function queueInline(src) {
  const q = { src, html: '', pre: '' };
  QUEUE.push(q);
  return q;
}

// Blockquote token, or null. Port of marked's blockquote tokenizer.
function blockquoteTok(src) {
  const m = RX_BLOCKQUOTE.exec(src);
  if (!m) return null;
  let lines = stripTrail(m[0], '\n').split('\n');
  let raw = '', text = '';
  const toks = [];
  while (lines.length > 0) {
    let seenMarker = false;
    const chunk = [];
    let p;
    for (p = 0; p < lines.length; p++) {
      if (T_BQ_START.test(lines[p])) { chunk.push(lines[p]); seenMarker = true; }
      else if (!seenMarker) chunk.push(lines[p]);
      else break;
    }
    lines = lines.slice(p);
    const h = chunk.join('\n');
    const u = h
      .replace(T_BQ_MARKER_WS, (g, b, mm) => b + expandTabs(mm, b.length))
      .replace(T_BQ_SETEXT, '\n    $1')
      .replace(T_BQ_SETEXT2, '');
    raw = raw ? raw + '\n' + h : h;
    text = text ? text + '\n' + u : u;
    const savedTop = TOP;
    TOP = true;
    lexBlocks(u, toks, true);
    TOP = savedTop;
    if (lines.length === 0) break;
    const k = toks.at(-1);
    if (k && (k.t === 'code' || k.t === 'heading' || k.t === 'hr' || k.t === 'html' || k.t === 'table')) break;
    if (k && k.t === 'blockquote') {
      const rest = lines.join('\n');
      const joined = k.raw + '\n' + rest.replace(T_BQ_SETEXT2, '');
      const f = blockquoteTok(joined);
      toks[toks.length - 1] = f;
      const y = joined.substring(f.raw.length).replace(/^\n/, '');
      const r2 = y ? y.split('\n').length : 0;
      const extra = r2 ? lines.slice(0, -r2) : lines;
      if (extra.length > 0) raw = raw + '\n' + extra.join('\n');
      text = text.substring(0, text.length - k.text.length) + f.text;
      lines = lines.slice(extra.length);
      if (lines.length > 0 && T_BQ_START.test(lines[0])) continue;
      break;
    } else if (k && k.t === 'list') {
      const rest = lines.join('\n');
      const joined = k.raw + '\n' + rest;
      const f = listTok(joined);
      toks[toks.length - 1] = f;
      const cnt = f.raw.length > k.raw.length ? joined.slice(k.raw.length + 1, f.raw.length).split('\n').length : 0;
      if (cnt > 0) {
        const y = lines.slice(0, cnt).join('\n');
        raw = raw + '\n' + y;
        text = text + '\n' + y;
      }
      lines = lines.slice(cnt);
      continue;
    }
  }
  return { t: 'blockquote', raw, text, toks };
}

// List token, or null. Port of marked's list tokenizer.
function listTok(src) {
  const first = RX_LIST.exec(src);
  if (!first) return null;
  let e = src;
  const n0 = e;
  const consumed = () => n0.length - e.length;
  let bullet = first[1].trim();
  const ordered = bullet.length > 1;
  const list = { t: 'list', raw: '', ordered, start: ordered ? +bullet.slice(0, -1) : '', loose: false, items: [] };
  bullet = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = listItemRx(bullet);
  let prevDoubleBlank = false;
  while (e) {
    let emptyItem = false, d = '';
    const t = itemRe.exec(e);
    if (!t || RX_HR.test(e)) break;
    const k = consumed();
    e = e.substring(t[0].length);
    const g = t[2].split('\n', 1)[0];
    const b = t[1].length;
    const mm = g.replace(T_LEAD_SPACE_TAB, (v) => expandTabs(v, b));
    let f = e.split('\n', 1)[0];
    const y = !mm.trim();
    let R = 0;
    if (y) R = b + 1;
    else {
      R = mm.search(T_NON_SPACE);
      if (R > 4) R = 1;
      d = mm.slice(R);
      R += b;
    }
    if (y && T_BLANK.test(f)) {
      e = e.substring(f.length + 1);
      emptyItem = true;
    }
    if (!emptyItem) {
      const vRe = nextBulletRx(R), qRe = hrRx(R), eeRe = fencesBeginRx(R),
        teRe = headingBeginRx(R), mRe = htmlBeginRx(R), neRe = blockquoteBeginRx(R);
      // Test the block-start regexes on a line, dispatching on its first
      // non-space character (all six are anchored `^ {0,R}` + trigger).
      // `prev` selects the set marked tests on the previous line
      // (fences, heading, HTML, hr — no blockquote or bullet).
      const startsBlock = (line, prev) => {
        let sp = 0;
        while (sp < line.length && line.charCodeAt(sp) === 32) sp++;
        if (sp > R) return false;
        const ch = sp < line.length ? line.charCodeAt(sp) : -1;
        if (ch === 96 || ch === 126) return eeRe.test(line);
        if (ch === 35) return teRe.test(line);
        if (ch === 60) return mRe.test(line);
        if (ch === 62) return !prev && neRe.test(line);
        if (ch === 45 || ch === 42) return prev ? qRe.test(line) : (vRe.test(line) || qRe.test(line));
        if (ch === 43 || (ch >= 48 && ch <= 57)) return !prev && vRe.test(line);
        if (ch === 95) return qRe.test(line);
        return false;
      };
      let mLine = mm;
      let yFlag = y;
      while (e) {
        const nl = e.indexOf('\n');
        const U = nl === -1 ? e : e.slice(0, nl);
        f = U;
        if (startsBlock(U)) break;
        const Z = U.replace(T_LEAD_SPACE_TAB, (v) => expandTabs(v));
        let zns = 0;
        while (zns < Z.length && Z.charCodeAt(zns) === 32) zns++;
        const fBlank = !U.trim();
        if (zns >= R || fBlank) {
          d += '\n' + Z.slice(R);
        } else {
          if (yFlag || firstNonSpaceCol(mLine) >= 4 || startsBlock(mLine, true)) break;
          const qe = /^ {0,3}(?:=+|-+) *$/.test(U) && RX_LHEADING.test(`${mLine}\n${U}`)
            ? `    ${Z.replace(/^ {0,3}/, '')}` : U;
          d += '\n' + qe;
        }
        yFlag = fBlank;
        e = nl === -1 ? '' : e.substring(nl + 1);
        mLine = Z.slice(R);
      }
    }
    const itemRaw = n0.slice(k, consumed());
    if (!list.loose) {
      if (prevDoubleBlank) list.loose = true;
      else if (T_DOUBLE_BLANK.test(itemRaw)) prevDoubleBlank = true;
    }
    list.items.push({ t: 'list_item', raw: itemRaw, task: T_LIST_TASK.test(d), loose: false, text: d, toks: [] });
  }
  const last = list.items.at(-1);
  if (!last) return null;
  last.raw = last.raw.trimEnd();
  last.text = last.text.trimEnd();
  list.raw = n0.slice(0, consumed()).trimEnd();
  for (const item of list.items) {
    TOP = false;
    item.toks = lexBlocks(item.text, [], false);
    if (!list.loose) {
      const spaces = item.toks.filter((g) => g.t === 'space');
      if (spaces.length > 0 && spaces.some((g) => T_ANY_LINE.test(g.raw))) list.loose = true;
    }
  }
  for (const item of list.items) {
    const firstTok = item.toks[0];
    if (item.task && firstTok && (firstTok.t === 'text' || firstTok.t === 'paragraph')) {
      item.text = item.text.replace(T_LIST_TASK_REP, '');
      firstTok.raw = firstTok.raw.replace(T_LIST_TASK_REP, '');
      firstTok.text = firstTok.text.replace(T_LIST_TASK_REP, '');
      for (let g = QUEUE.length - 1; g >= 0; g--) {
        if (T_LIST_TASK.test(QUEUE[g].src)) {
          QUEUE[g].src = QUEUE[g].src.replace(T_LIST_TASK_REP, '');
          break;
        }
      }
      const ck = T_LIST_CHECKBOX.exec(item.raw);
      if (ck) {
        const box = { t: 'checkbox', raw: ck[0] + ' ', checked: ck[0] !== '[ ]' };
        item.checked = box.checked;
        const boxHtml = `<input ${box.checked ? 'checked="" ' : ''}disabled="" type="checkbox"> `;
        if (list.loose && firstTok.q) {
          firstTok.raw = box.raw + firstTok.raw;
          firstTok.text = box.raw + firstTok.text;
          firstTok.q.pre = boxHtml;
        } else if (list.loose) {
          const q = queueInline('');
          q.pre = boxHtml;
          item.toks.unshift({ t: 'paragraph', raw: box.raw, text: box.raw, q });
        } else {
          item.toks.unshift(box);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const tk of item.toks) if (tk.t === 'text') tk.t = 'paragraph';
    }
  }
  return list;
}

// Single-line interrupt tests for the paragraph scan (the same patterns
// marked's paragraph regex uses in its per-line lookaheads).
const P_INT_HEADING = /^ {0,3}#{1,6}(?:\s|$)/;
const P_INT_BQ = /^ {0,3}>/;
const P_INT_FENCE = /^ {0,3}(?:`{3,}(?=[^`]*$)|~~~)/;
const P_INT_LIST = /^ {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t]/;
const P_SETEXT = /^ {0,3}(=+|-+)[ \t]*$/;
const P_TABLE_DELIM = /^ {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)$/;
const P_BLANK = /^[ \t]*$/;
const P_TABLE_HEADER = /^ *[^ ]/;

// Scan a paragraph-like block starting at src[0] line by line, returning
// a table token (header + delimiter on the first two lines), a setext
// heading token (paragraph lines + an underline), or a paragraph token —
// the same results marked's table / lheading / paragraph regexes give,
// without re-scanning the whole remainder for each. When `top` is false
// (inside a list item) no paragraph token is returned, so the caller
// falls through to the single-line text token.
function paraScan(src, top) {
  const lines = [];
  const hasNl = [];
  let p = 0;
  const line = (k) => {
    while (lines.length <= k) {
      if (p >= src.length) return null;
      const nl = src.indexOf('\n', p);
      if (nl === -1) { lines.push(src.slice(p)); hasNl.push(false); p = src.length; }
      else { lines.push(src.slice(p, nl)); hasNl.push(true); p = nl + 1; }
    }
    return lines[k];
  };
  const l1 = line(1);
  // Table: header line + delimiter row on the next line.
  if (l1 !== null && P_TABLE_DELIM.test(l1) && /[:|]/.test(l1)) {
    const m = RX_TABLE.exec(src);
    if (m) {
      const headerCells = splitTableRow(m[1]);
      const aligns = m[2].replace(T_TABLE_ALIGN_CHARS, '').split('|');
      if (headerCells.length === aligns.length) {
        const rowsRaw = m[3] && m[3].trim() ? m[3].replace(T_TABLE_ROW_BLANK, '').split('\n') : [];
        const raw = stripTrail(m[0], '\n');
        const align = aligns.map((a) =>
          T_TABLE_ALIGN_R.test(a) ? 'right'
            : T_TABLE_ALIGN_C.test(a) ? 'center'
            : T_TABLE_ALIGN_L.test(a) ? 'left' : null);
        const header = headerCells.map((c, idx) => ({ text: c, align: align[idx], q: queueInline(c) }));
        const rows = rowsRaw.map((r) =>
          splitTableRow(r, header.length).map((c, idx) => ({ text: c, align: align[idx], q: queueInline(c) })));
        return { tok: { t: 'table', raw, header, align, rows }, len: raw.length };
      }
    }
    // Table regex failed or header/align lengths differ: the paragraph
    // still stops before line 1 (the table lookahead matched), so fall
    // into the paragraph scan below.
  }
  let end = 1;
  for (let i = 1; ; i++) {
    const ln = line(i);
    // A whitespace-only line ends the paragraph only when a newline
    // follows it; at end of input it is a paragraph line (cm-241).
    if (ln === null || (P_BLANK.test(ln) && hasNl[i])) break;
    if (P_SETEXT.test(ln)) {
      const m = RX_LHEADING.exec(src);
      if (m) {
        const text = m[1].trim();
        const raw = stripTrail(m[0], '\n');
        return { tok: { t: 'heading', raw, depth: m[2].charAt(0) === '=' ? 1 : 2, text, q: queueInline(text) }, len: raw.length };
      }
      // Not a setext heading after all: the underline is an ordinary line.
      end = i + 1;
      continue;
    }
    if (RX_HR.test(ln) || P_INT_HEADING.test(ln) || P_INT_BQ.test(ln) || P_INT_FENCE.test(ln) ||
        P_INT_LIST.test(ln) || htmlBeginRx(4).test(ln)) break;
    const nx = line(i + 1);
    if (nx !== null && P_TABLE_HEADER.test(ln) && P_TABLE_DELIM.test(nx)) {
      // A table interrupts the paragraph — unless the delimiter line is
      // itself a setext underline, in which case the whole block is a
      // setext heading (cm-095).
      if (P_SETEXT.test(nx)) {
        const m = RX_LHEADING.exec(src);
        if (m) {
          const text = m[1].trim();
          const raw = stripTrail(m[0], '\n');
          return { tok: { t: 'heading', raw, depth: m[2].charAt(0) === '=' ? 1 : 2, text, q: queueInline(text) }, len: raw.length };
        }
      }
      break;
    }
    end = i + 1;
  }
  if (!top) return null;
  const text = lines.slice(0, end).join('\n');
  return { tok: { t: 'paragraph', raw: text, text, q: queueInline(text) }, len: text.length };
}

// Lex blocks of `src` into `toks` (appended). `nested` is true when called
// for blockquote/list content, where a leading paragraph merges with a
// preceding paragraph token. Returns the token array.
function lexBlocks(src, toks, nested) {
  let guard = Infinity;
  while (src) {
    if (src.length < guard) guard = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    let m;
    // blank lines / space
    m = RX_NEWLINE.exec(src);
    if (m && m[0].length > 0) {
      src = src.substring(m[0].length);
      const prev = toks.at(-1);
      if (m[0].length === 1 && prev !== undefined) prev.raw += '\n';
      else toks.push({ t: 'space', raw: m[0] });
      continue;
    }
    // indented code
    m = RX_CODE.exec(src);
    if (m) {
      const raw = trimCodeBlock(m[0]);
      const text = raw.replace(T_CODE_INDENT, '');
      src = src.substring(raw.length);
      const prev = toks.at(-1);
      if (prev && (prev.t === 'paragraph' || prev.t === 'text')) {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + raw;
        prev.text += '\n' + text;
        QUEUE.at(-1).src = prev.text;
      } else {
        toks.push({ t: 'code', raw, text });
      }
      continue;
    }
    // fenced code
    m = RX_FENCES.exec(src);
    if (m) {
      const lang = m[2] ? m[2].trim().replace(IX_ANY_PUNCT, '$1') : m[2];
      const text = fenceIndentComp(m[0], m[3] || '');
      src = src.substring(m[0].length);
      toks.push({ t: 'code', raw: m[0], text, lang });
      continue;
    }
    // ATX heading
    m = RX_HEADING.exec(src);
    if (m) {
      let text = m[2].trim();
      if (T_END_HASH.test(text)) {
        const stripped = stripTrail(text, '#');
        if (!stripped || T_END_SPACE_TAB.test(stripped)) text = stripped.trim();
      }
      const raw = stripTrail(m[0], '\n');
      src = src.substring(raw.length);
      toks.push({ t: 'heading', raw, depth: m[1].length, text, q: queueInline(text) });
      continue;
    }
    // thematic break
    m = RX_HR.exec(src);
    if (m) {
      const raw = stripTrail(m[0], '\n');
      src = src.substring(raw.length);
      toks.push({ t: 'hr', raw });
      continue;
    }
    // blockquote
    {
      const bq = blockquoteTok(src);
      if (bq) {
        src = src.substring(bq.raw.length);
        toks.push(bq);
        continue;
      }
    }
    // list
    {
      const li = listTok(src);
      if (li) {
        src = src.substring(li.raw.length);
        toks.push(li);
        continue;
      }
    }
    // raw HTML block
    m = RX_HTML.exec(src);
    if (m) {
      const raw = trimCodeBlock(m[0]);
      src = src.substring(raw.length);
      toks.push({ t: 'html', raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text: raw });
      continue;
    }
    // link reference definition
    m = RX_DEF.exec(src);
    if (m) {
      if (T_START_ANGLE.test(m[2]) || parenBalance(m[2], '()') === -1) {
        const tag = normLabel(m[1]);
        const href = m[2] ? m[2].replace(T_HREF_BRACKETS, '$1').replace(IX_ANY_PUNCT, '$1') : '';
        const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(IX_ANY_PUNCT, '$1') : m[3];
        const raw = stripTrail(m[0], '\n');
        src = src.substring(raw.length);
        const prev = toks.at(-1);
        if (prev && (prev.t === 'paragraph' || prev.t === 'text')) {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + raw;
          prev.text += '\n' + raw;
          QUEUE.at(-1).src = prev.text;
        } else {
          if (!Object.hasOwn(LINKS, tag)) LINKS[tag] = { href, title };
          toks.push({ t: 'def', raw });
        }
        continue;
      }
      // not a valid definition: fall through to table / setext / paragraph
    }
    // table / setext heading / paragraph (manual line scan)
    {
      const sc = paraScan(src, TOP);
      if (sc) {
        src = src.substring(sc.len);
        if (sc.tok.t === 'paragraph') {
          const prev = toks.at(-1);
          if (nested && prev && prev.t === 'paragraph') {
            prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + sc.tok.raw;
            prev.text += '\n' + sc.tok.text;
            QUEUE.pop();
            QUEUE.at(-1).src = prev.text;
          } else {
            toks.push(sc.tok);
          }
          nested = false;
        } else {
          toks.push(sc.tok);
        }
        continue;
      }
    }
    // plain text (one line)
    m = RX_TEXT.exec(src);
    if (m) {
      const tok = { t: 'text', raw: m[0], text: m[0], q: queueInline(m[0]) };
      src = src.substring(m[0].length);
      const prev = toks.at(-1);
      if (prev && prev.t === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
        QUEUE.pop();
        QUEUE.at(-1).src = prev.text;
      } else {
        toks.push(tok);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  TOP = true;
  return toks;
}

// ---- block renderer (same HTML as marked's Renderer) ----

function renderTableCell(cell, isHeader) {
  const tag = isHeader ? 'th' : 'td';
  return (cell.align ? `<${tag} align="${cell.align}">` : `<${tag}>`) + cell.q.html + `</${tag}>\n`;
}

function renderBlocks(toks) {
  let out = '';
  for (const tk of toks) {
    switch (tk.t) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += `<h${tk.depth}>${tk.q.html}</h${tk.depth}>\n`;
        break;
      case 'code': {
        const lang = (tk.lang || '').match(T_NOT_SPACE_START)?.[0];
        const text = tk.text ? tk.text.replace(T_END_NL, '') + '\n' : '';
        const body = esc(text, true);
        out += lang
          ? `<pre><code class="language-${esc(lang)}">${body}</code></pre>\n`
          : `<pre><code>${body}</code></pre>\n`;
        break;
      }
      case 'table': {
        let head = '';
        for (const c of tk.header) head += renderTableCell(c, true);
        head = `<tr>\n${head}</tr>\n`;
        let body = '';
        for (const row of tk.rows) {
          let cells = '';
          for (const c of row) cells += renderTableCell(c, false);
          body += `<tr>\n${cells}</tr>\n`;
        }
        if (body) body = `<tbody>${body}</tbody>`;
        out += `<table>\n<thead>\n${head}</thead>\n${body}</table>\n`;
        break;
      }
      case 'blockquote':
        out += `<blockquote>\n${renderBlocks(tk.toks)}</blockquote>\n`;
        break;
      case 'list': {
        const tag = tk.ordered ? 'ol' : 'ul';
        const start = tk.ordered && tk.start !== 1 ? ` start="${tk.start}"` : '';
        let items = '';
        for (const item of tk.items) items += `<li>${renderBlocks(item.toks)}</li>\n`;
        out += `<${tag}${start}>\n${items}</${tag}>\n`;
        break;
      }
      case 'checkbox':
        out += `<input ${tk.checked ? 'checked="" ' : ''}disabled="" type="checkbox"> `;
        break;
      case 'html':
        out += tk.text;
        break;
      case 'def':
        break;
      case 'paragraph':
        out += `<p>${tk.q.html}</p>\n`;
        break;
      case 'text':
        out += tk.q.html;
        break;
      default:
        throw new Error(`Token with "${tk.t}" type was not found.`);
    }
  }
  return out;
}

// ---- entry point ----

// Render `markdown` to exactly the HTML marked 18.1.3 renders with its
// default options. Fully self-contained: no state is kept between calls.
export function parse(markdown) {
  LINKS = Object.create(null);
  QUEUE = [];
  IN_LINK = false;
  IN_RAW = false;
  LINK_EMITTED = false;
  LINK_PAREN = true;
  TOP = true;
  const src = markdown.replace(T_CR, '\n');
  const toks = lexBlocks(src, [], false);
  for (const q of QUEUE) {
    IN_RAW = false;
    q.html = (q.pre || '') + renderInline(q.src, false);
  }
  return renderBlocks(toks);
}
