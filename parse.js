// parse.js — a fast drop-in for marked 18.1.3 with its default options
// (gfm on, breaks off, pedantic off, async off).
//
// Own implementation, written from the CommonMark 0.31.2 / GFM 0.29 grammar
// and marked's published behaviour. No dependencies, no network, no cache
// across cases: every parse() call starts from fresh state.
//
// Speed comes from the architecture, not from shortcuts:
//  - the block scan runs on the source string by index, with sticky regexes,
//    so it never copies the remaining input after each block (marked's
//    substring loop is quadratic on long documents);
//  - the first character of a block dispatches to only the tokenizers that
//    can match there, instead of trying all of them in order;
//  - plain paragraphs and headings (no inline markup at all) render through
//    a fast path that skips inline tokenization entirely;
//  - tokens render straight to strings; there is no separate parse walk.

export function parse(markdown) {
  const S = freshState();
  let src = String(markdown);
  if (src.includes('\r')) src = src.replace(/\r\n|\r/g, '\n');
  const tokens = blockTokensInto(S, src, [], false);
  for (let i = 0; i < S.queue.length; i++) {
    S.inRawBlock = false;
    inlineTokens(S, S.queue[i].src, S.queue[i].tokens);
  }
  return renderTokens(S, tokens);
}

function freshState() {
  return {
    links: Object.create(null),
    inLink: false,
    inRawBlock: false,
    linkEmitted: false,
    linkParenPossible: true,
    top: true,
    queue: [],
    closerStack: [],
  };
}

// ---------------------------------------------------------------- helpers

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

function escapeHtml(html, encode) {
  if (encode) {
    return /[&<>"']/.test(html) ? html.replace(/[&<>"']/g, (ch) => ESCAPES[ch]) : html;
  }
  return /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/.test(html)
    ? html.replace(/[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g, (ch) => ESCAPES[ch])
    : html;
}

const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function decodeNumericRefs(text) {
  if (!NUM_REF.test(text)) return text;
  return text.replace(NUM_REF_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
  return href;
}

function splitCells(tableRow, count) {
  const row = tableRow.replace(/\|/g, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(/ \|/);
  let i = 0;
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// Remove trailing 'c's (or, with invert, trailing non-'c's). /c*$/ is REDOS-prone.
function rtrim(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let suffLen = 0;
  while (suffLen < l) {
    const currChar = str.charAt(l - suffLen - 1);
    if (currChar === c && !invert) suffLen++;
    else if (currChar !== c && invert) suffLen++;
    else break;
  }
  return str.slice(0, l - suffLen);
}

const BLANK_LINE = /^[ \t]*$/;
function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && BLANK_LINE.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

// Unicode case fold by round-tripping through upper case (commonmark.js
// trick: toLowerCase alone never folds ẞ to SS).
function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the closing bracket that drops the level below zero, -1 when the
// brackets balance, -2 when more open than close.
function findClosingBracket(str, b) {
  if (str.indexOf(b[0]) === -1 && str.indexOf(b[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === b[0]) level++;
    else if (str[i] === b[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

function expandTabs(line, indent = 0) {
  let col = indent;
  let expanded = '';
  for (const char of line) {
    if (char === '\t') {
      const added = 4 - (col % 4);
      expanded += ' '.repeat(added);
      col += added;
    } else {
      expanded += char;
      col++;
    }
  }
  return expanded;
}

// One scan of a masked inline source for the last delimiter runs that can
// close emphasis/strong/del, so emStrong/del can bail out early when no
// closer exists. Frames stack across nested inline runs.
function scanClosers(src) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') del = i;
      else em[ch] = i;
    }
    i = j - 1;
  }
  return { maskedSrc: src, em, del };
}

function lastEmCloser(S, maskedSrc, delim) {
  const frame = S.closerStack.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) return frame.em[delim];
  return scanClosers(maskedSrc).em[delim];
}

function lastDelCloser(S, maskedSrc) {
  const frame = S.closerStack.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) return frame.del;
  return scanClosers(maskedSrc).del;
}

// ------------------------------------------------------- regex construction

// Tiny builder: compose a regex from a base pattern by textual substitution,
// as a grammar is written. `^` at the head of an inserted source is dropped
// when it lands mid-pattern.
const CARET = /(^|[^\[])\^/g;
function edit(regex, opt = '') {
  let source = typeof regex === 'string' ? regex : regex.source;
  const obj = {
    replace(name, val) {
      let valSource = typeof val === 'string' ? val : val.source;
      valSource = valSource.replace(CARET, '$1');
      source = source.replace(name, valSource);
      return obj;
    },
    getRegex() {
      return new RegExp(source, opt);
    },
  };
  return obj;
}

// Sticky twin of a ^-anchored regex: the leading ^ is dropped and the match
// is pinned to lastIndex, so the block scan needs no substring copies.
// All block regexes below carry their ^ only at the very start.
function sticky(re) {
  let s = re.source;
  if (s.charCodeAt(0) === 94) s = s.slice(1); // '^'
  const flags = re.flags.replace('g', '') + 'y';
  return new RegExp(s, flags);
}

function execAt(re, str, pos) {
  re.lastIndex = pos;
  return re.exec(str);
}

const supportsLookbehind = (() => {
  try {
    return !!new RegExp('(?<=1)(?<!1)');
  } catch {
    return false;
  }
})();

const TAG = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';
const COMMENT = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;

const newlineRe = /^(?:[ \t]*(?:\n|$))+/;
const blockCodeRe = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const fencesRe = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const hrRe = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const headingRe = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const bulletRe = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
const lheadingCore = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
const lheadingRe = edit(lheadingCore)
  .replace(/bull/g, bulletRe)
  .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
  .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
  .replace(/blockquote/g, / {0,3}>/)
  .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
  .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
  .replace(/html/g, / {0,3}<[^\n>]+>\n/)
  .replace(/\|table/g, '')
  .getRegex();
const lheadingGfmRe = edit(lheadingCore)
  .replace(/bull/g, bulletRe)
  .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
  .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
  .replace(/blockquote/g, / {0,3}>/)
  .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
  .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
  .replace(/html/g, / {0,3}<[^\n>]+>\n/)
  .replace(/table/g, / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/)
  .getRegex();
const paragraphCore = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;
const blockLabelRe = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const defRe = edit(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
  .replace('label', blockLabelRe)
  .replace('title', /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/)
  .getRegex();
const listRe = edit(/^(bull)([ \t][^\n]*?)?(?:\n|$)/)
  .replace(/bull/g, bulletRe)
  .getRegex();
const htmlRe = edit(
  '^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|comment[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)'
  + ')', 'i')
  .replace('comment', COMMENT)
  .replace('tag', TAG)
  .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/)
  .getRegex();
const blockTextRe = /^[^\n]+/;

function makeParagraph(listInterrupt) {
  return edit(paragraphCore)
    .replace('hr', hrRe)
    .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
    .replace('|lheading', '')
    .replace('table', gfmTableRe)
    .replace('blockquote', ' {0,3}>')
    .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
    .replace('list', listInterrupt)
    .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
    .replace('tag', TAG)
    .getRegex();
}
const gfmTableRe = edit(
  '^ *([^\\n ].*)\\n'
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
  + '(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
  .replace('hr', hrRe)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('blockquote', ' {0,3}>')
  .replace('code', '(?: {4}| {0,3}\t)[^\\n]')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', TAG)
  .getRegex();
const paragraphRe = makeParagraph(/ {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]/);
const blockquoteParagraphRe = makeParagraph(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/);
const blockquoteRe = edit(/^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(paragraph)|[^\n]*)(?:\n|$))+/)
  .replace('paragraph', blockquoteParagraphRe)
  .getRegex();

// Sticky twins for the block scan (match pinned at lastIndex, no ^ needed).
const S_NEWLINE = sticky(newlineRe);
const S_CODE = sticky(blockCodeRe);
const S_FENCES = sticky(fencesRe);
const S_HEADING = sticky(headingRe);
const S_HR = sticky(hrRe);
const S_BLOCKQUOTE = sticky(blockquoteRe);
const S_LIST = sticky(listRe);
const S_HTML = sticky(htmlRe);
const S_DEF = sticky(defRe);
const S_TABLE = sticky(gfmTableRe);
const S_LHEADING = sticky(lheadingGfmRe);
const S_PARAGRAPH = sticky(paragraphRe);
const S_TEXT = sticky(blockTextRe);

// Per-indent cached regexes used inside list items.
function cachedIndentRegex(create) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) {
      re = create(idx);
      cache[idx] = re;
    }
    return re;
  };
}
const nextBulletRe = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`));
const hrReAt = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fencesBeginRe = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`));
const headingBeginRe = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`));
const htmlBeginRe = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:</?(?:${TAG})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRe = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}>`));

const listItemRe = (bull) => new RegExp(`^( {0,3}${bull})((?:[\t ][^\\n]*)?(?:\\n|$))`);

// First line of `str` at or after `p` (up to the next '\n').
function lineAt(str, p) {
  const nl = str.indexOf('\n', p);
  return nl === -1 ? str.slice(p) : str.slice(p, nl);
}

// Manual equivalents of the per-indent list-item break patterns, keyed on
// the line's first non-space character so plain text lines skip them.
// `lead` is the count of leading spaces, already capped at the indent.
function listLineIsFence(line, lead) {
  return line.startsWith('```', lead) || line.startsWith('~~~', lead);
}
function listLineIsHeading(line, lead) {
  let j = lead;
  while (j < line.length && line[j] === '#' && j - lead < 6) j++;
  if (j === lead) return false;
  if (j === line.length) return true;
  const c = line[j];
  return c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\r';
}
function listLineIsBullet(line, lead) {
  if (lead >= line.length) return false;
  const c = line[lead];
  if (c === '*' || c === '+' || c === '-') {
    const n = line[lead + 1];
    return n === undefined || n === ' ' || n === '\t';
  }
  if (c >= '0' && c <= '9') {
    let j = lead;
    while (j < line.length && line[j] >= '0' && line[j] <= '9' && j - lead < 9) j++;
    const d = line[j];
    if (d !== '.' && d !== ')') return false;
    const n = line[j + 1];
    return n === undefined || n === ' ' || n === '\t';
  }
  return false;
}
function listLineIsHr(line, lead) {
  if (lead >= line.length) return false;
  const c = line[lead];
  if (c !== '-' && c !== '_' && c !== '*') return false;
  let n = 0;
  for (let i = lead; i < line.length; i++) {
    if (line[i] === c) n++;
    else if (line[i] === ' ' || line[i] === '\t') continue;
    else return false;
  }
  return n >= 3;
}

// ------------------------------------------------------------ inline rules

const escapeRe = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const inlineCodeRe = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const brRe = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const punctRe = /[\p{P}\p{S}]/u;
const punctOrSpaceRe = /[\s\p{P}\p{S}]/u;
const notPunctOrSpaceRe = /[^\s\p{P}\p{S}]/u;
const punctuationRe = edit(/^((?![*_])punctSpace)/, 'u')
  .replace(/punctSpace/g, punctOrSpaceRe).getRegex();
const punctGfmStrongEmRe = /(?!~)[\p{P}\p{S}]/u;
const punctOrSpaceGfmStrongEmRe = /(?!~)[\s\p{P}\p{S}]/u;
const notPunctOrSpaceGfmStrongEmRe = /(?:[^\s\p{P}\p{S}]|~)/u;

const blockSkipRe = edit(/link|precode-code|html/, 'g')
  .replace('link', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/)
  .replace('precode-', supportsLookbehind ? '(?<!`)()' : '(^^|[^`])')
  .replace('code', /(?<b>`+)[^`]+\k<b>(?!`)/)
  .replace('html', /<(?! )[^<>]*?>/)
  .getRegex();

const emStrongLDelimCore = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?)|^_+(?:((?!_)punct)|([^\s_]))?/;
const emStrongLDelimRe = edit(emStrongLDelimCore, 'u')
  .replace(/punct/g, punctGfmStrongEmRe)
  .getRegex();
const emStrongRDelimAstCore =
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)' // skip orphan inside strong
  + '|[^*]+(?=[^*])' // consume to delim
  + '|(?!\\*)punct(\\*+)(?=[\\s]|$)' // (1) #*** right only
  + '|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)' // (2) a***# right only
  + '|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)' // (3) #***a left only
  + '|[\\s](\\*+)(?!\\*)(?=punct)' // (4) ***# left only
  + '|(?!\\*)punct(\\*+)(?!\\*)(?=punct)' // (5) #***# either
  + '|notPunctSpace(\\*+)(?=notPunctSpace)'; // (6) a***a either
const emStrongRDelimAstRe = edit(emStrongRDelimAstCore, 'gu')
  .replace(/notPunctSpace/g, notPunctOrSpaceGfmStrongEmRe)
  .replace(/punctSpace/g, punctOrSpaceGfmStrongEmRe)
  .replace(/punct/g, punctGfmStrongEmRe)
  .getRegex();
const emStrongRDelimUndRe = edit(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
  + '|[^_]+(?=[^_])'
  + '|(?!_)punct(_+)(?=[\\s]|$)'
  + '|notPunctSpace(_+)(?!_)(?=punctSpace|$)'
  + '|(?!_)punctSpace(_+)(?=notPunctSpace)'
  + '|[\\s](_+)(?!_)(?=punct)'
  + '|(?!_)punct(_+)(?!_)(?=punct)', 'gu')
  .replace(/notPunctSpace/g, notPunctOrSpaceRe)
  .replace(/punctSpace/g, punctOrSpaceRe)
  .replace(/punct/g, punctRe)
  .getRegex();
const delLDelimRe = edit(/^~~?(?:((?!~)punct)|[^\s~])/, 'u')
  .replace(/punct/g, punctRe)
  .getRegex();
const delRDelimCore =
  '^[^~]+(?=[^~])'
  + '|(?!~)punct(~~?)(?=[\\s]|$)'
  + '|notPunctSpace(~~?)(?!~)(?=punctSpace|$)'
  + '|(?!~)punctSpace(~~?)(?=notPunctSpace)'
  + '|[\\s](~~?)(?!~)(?=punct)'
  + '|(?!~)punct(~~?)(?!~)(?=punct)'
  + '|notPunctSpace(~~?)(?=notPunctSpace)';
const delRDelimRe = edit(delRDelimCore, 'gu')
  .replace(/notPunctSpace/g, notPunctOrSpaceRe)
  .replace(/punctSpace/g, punctOrSpaceRe)
  .replace(/punct/g, punctRe)
  .getRegex();
const anyPunctRe = edit(/\\(punct)/, 'gu')
  .replace(/punct/g, punctRe)
  .getRegex();
const anyPunctOutsideCodeRe = edit(/(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\(punct)/, 'gu')
  .replace(/punct/g, punctRe)
  .getRegex();

const autolinkRe = edit(/^<(scheme:[^\s\x00-\x1f<>]*|email)>/)
  .replace('scheme', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/)
  .replace('email', /[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/)
  .getRegex();
const inlineCommentRe = edit(COMMENT).replace('(?:-->|$)', '-->').getRegex();
const tagRe = edit(
  '^comment'
  + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>'
  + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>'
  + '|^<\\?[\\s\\S]*?\\?>'
  + '|^<![a-zA-Z]+\\s[\\s\\S]*?>'
  + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>')
  .replace('comment', inlineCommentRe)
  .replace('attribute', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/)
  .getRegex();

const inlineLabelBracketsRe = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
const inlineLabelRe = edit(/(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/)
  .replace('brackets', inlineLabelBracketsRe)
  .getRegex();
const linkRe = edit(/^!?\[(label)\]\([ \t\n]*(href)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(title))?[ \t\n]*\)/)
  .replace('label', inlineLabelRe)
  .replace('href', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/)
  .replace('title', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/)
  .getRegex();
const reflinkRe = edit(/^!?\[(label)\]\[(ref)\]/)
  .replace('label', inlineLabelRe)
  .replace('ref', blockLabelRe)
  .getRegex();
const nolinkRe = edit(/^!?\[(ref)\](?:\[\])?/)
  .replace('ref', blockLabelRe)
  .getRegex();
const boundedBlockLabelRe = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const boundedInlineLabelRe = edit(/(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/)
  .replace('brackets', inlineLabelBracketsRe)
  .getRegex();
const reflinkSearchRe = edit('reflink|nolink(?!\\()', 'g')
  .replace('reflink', edit(/^!?\[(label)\]\[(ref)\]/)
    .replace('label', boundedInlineLabelRe)
    .replace('ref', boundedBlockLabelRe)
    .getRegex())
  .replace('nolink', edit(/^!?\[(ref)\](?:\[\])?/)
    .replace('ref', boundedBlockLabelRe)
    .getRegex())
  .getRegex();

const urlRe = edit(/^emailProtocol|^((?:protocol):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^email/)
  .replace('emailProtocol', /(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)/)
  .replace('protocol', /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/)
  .replace('email', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/)
  .getRegex();
const backpedalRe = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const delRe = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;
const inlineTextRe = edit(/^(?:[^a-zA-Z0-9](?=emailProtocol)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|protocol:\/\/|wwwStart|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=emailProtocol)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/)
  .replace('protocol', /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/)
  .replace(/emailProtocol/g, /(?:mailto|xmpp):/)
  .replace('wwwStart', supportsLookbehind ? '(?<![^\\s*_~(])www\\.' : 'www\\.')
  .getRegex();

// Shared small patterns (mirrors the grammar's `other` table).
const CODE_REMOVE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const OUTPUT_LINK_REPLACE = /\\([\[\]])/g;
const INDENT_CODE_COMP = /^(\s+)(?:```)/;
const BEGIN_SPACE = /^\s+/;
const END_HASH = /#$/;
const END_SPACE_TAB = /[ \t]$/;
const NON_SPACE = /[^ ]/;
const LEADING_SPACE_TAB = /^[ \t]+/;
const TAB_GLOBAL = /\t/g;
const BLOCKQUOTE_START = /^ {0,3}>/;
const BLOCKQUOTE_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const BLOCKQUOTE_SETEXT2 = /^ {0,3}>[ \t]?/gm;
const BLOCKQUOTE_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const LIST_NESTING = /^ {1,4}(?=( {4})*[^ ])/g;
const LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const LIST_TASK_CHECKBOX = /\[[ xX]\]/;
const ANY_LINE = /\n.*\n/;
const HREF_BRACKETS = /^<(.*)>$/;
const TABLE_DELIM = /[:|]/;
const TABLE_ALIGN_CHARS = /^\||\| *$/g;
const TABLE_ROW_BLANK = /\n[ \t]*$/;
const TABLE_ALIGN_RIGHT = /^ *-+: *$/;
const TABLE_ALIGN_CENTER = /^ *:-+: *$/;
const TABLE_ALIGN_LEFT = /^ *:-+ *$/;
const START_A_TAG = /^<a /i;
const END_A_TAG = /^<\/a>/i;
const START_PRE_TAG = /^<(pre|code|kbd|script)(\s|>)/i;
const END_PRE_TAG = /^<\/(pre|code|kbd|script)(\s|>)/i;
const START_ANGLE = /^</;
const END_ANGLE = />$/;
const UNICODE_ALNUM = /[\p{L}\p{N}]/u;

// ---------------------------------------------------------- block tokenizers
// Each takes (S, src, pos) and returns a token with `raw` plus `end` (the
// position after the token), or null. `raw` is the slice the token consumed.

function tokSpace(S, src, pos) {
  const cap = execAt(S_NEWLINE, src, pos);
  if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0], end: pos + cap[0].length };
  return null;
}

function tokCode(S, src, pos) {
  const cap = execAt(S_CODE, src, pos);
  if (!cap) return null;
  const raw = trimTrailingBlankLines(cap[0]);
  return { type: 'code', raw, codeBlockStyle: 'indented', text: raw.replace(CODE_REMOVE_INDENT, ''), end: pos + cap[0].length };
}

function indentCodeCompensation(raw, text) {
  const m = raw.match(INDENT_CODE_COMP);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map((node) => {
    const mi = node.match(BEGIN_SPACE);
    if (mi === null) return node;
    const indentInNode = mi[0];
    return node.slice(Math.min(indentInNode.length, indentToCode.length));
  }).join('\n');
}

function tokFences(S, src, pos) {
  const cap = execAt(S_FENCES, src, pos);
  if (!cap) return null;
  const raw = cap[0];
  return {
    type: 'code', raw,
    lang: cap[2] ? cap[2].trim().replace(anyPunctRe, '$1') : cap[2],
    text: indentCodeCompensation(raw, cap[3] || ''),
    end: pos + raw.length,
  };
}

function tokHeading(S, src, pos) {
  const cap = execAt(S_HEADING, src, pos);
  if (!cap) return null;
  let text = cap[2].trim();
  if (END_HASH.test(text)) {
    const trimmed = rtrim(text, '#');
    if (!trimmed || /[ \t]$/.test(trimmed)) text = trimmed.trim();
  }
  const tokens = [];
  S.queue.push({ src: text, tokens });
  return { type: 'heading', raw: rtrim(cap[0], '\n'), depth: cap[1].length, text, tokens, end: pos + cap[0].length };
}

function tokHr(S, src, pos) {
  const cap = execAt(S_HR, src, pos);
  if (!cap) return null;
  return { type: 'hr', raw: rtrim(cap[0], '\n'), end: pos + cap[0].length };
}

function tokBlockquote(S, src, pos) {
  const cap = execAt(S_BLOCKQUOTE, src, pos);
  if (!cap) return null;
  let lines = rtrim(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];
  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (BLOCKQUOTE_START.test(lines[i])) {
        currentLines.push(lines[i]);
        inBlockquote = true;
      } else if (!inBlockquote) {
        currentLines.push(lines[i]);
      } else break;
    }
    lines = lines.slice(i);
    const currentRaw = currentLines.join('\n');
    const currentText = currentRaw
      .replace(BLOCKQUOTE_MARKER_WS, (_, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(BLOCKQUOTE_SETEXT, '\n    $1')
      .replace(BLOCKQUOTE_SETEXT2, '');
    raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
    text = text ? `${text}\n${currentText}` : currentText;
    const top = S.top;
    S.top = true;
    blockTokensInto(S, currentText, tokens, true);
    S.top = top;
    if (lines.length === 0) break;
    const lastToken = tokens.at(-1);
    if (lastToken?.type === 'code' || lastToken?.type === 'heading' || lastToken?.type === 'hr' || lastToken?.type === 'html' || lastToken?.type === 'table') {
      break;
    } else if (lastToken?.type === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(BLOCKQUOTE_SETEXT2, '');
      const newToken = tokBlockquote(S, newText, 0);
      tokens[tokens.length - 1] = newToken;
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && BLOCKQUOTE_START.test(lines[0])) continue;
      break;
    } else if (lastToken?.type === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = tokList(S, newText, 0);
      tokens[tokens.length - 1] = newToken;
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = `${raw}\n${consumed}`;
        text = `${text}\n${consumed}`;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }
  return { type: 'blockquote', raw, tokens, text, end: pos + raw.length };
}

function tokList(S, src, pos) {
  let cap = execAt(S_LIST, src, pos);
  if (!cap) return null;
  const listSrc = src.slice(pos);
  let bull = cap[1].trim();
  const isordered = bull.length > 1;
  const list = {
    type: 'list', raw: '', ordered: isordered,
    start: isordered ? +bull.slice(0, -1) : '', loose: false, items: [],
  };
  bull = isordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
  const itemRegex = sticky(listItemRe(bull));
  let endsWithBlankLine = false;
  let taken = 0; // offset into listSrc consumed so far
  let p = 0;
  while (p < listSrc.length) {
    let endEarly = false;
    let itemContents = '';
    if (!(cap = execAt(itemRegex, listSrc, p))) break;
    if (execAt(S_HR, listSrc, p)) break;
    const itemStart = p;
    p += cap[0].length;
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(LEADING_SPACE_TAB, (ws) => expandTabs(ws, bulletIndent));
    let nextLine = lineAt(listSrc, p);
    let blankLine = !line.trim();
    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && BLANK_LINE.test(nextLine)) {
      p = Math.min(listSrc.length, p + nextLine.length + 1);
      endEarly = true;
    }
    if (!endEarly) {
      const htmlBeginRegex = htmlBeginRe(indent);
      const fencesBeginRegex = fencesBeginRe(indent);
      const headingBeginRegex = headingBeginRe(indent);
      const hrRegex = hrReAt(indent);
      // The per-indent patterns allow at most min(3, indent-1) spaces.
      const maxLead = Math.max(0, Math.min(3, indent - 1));
      while (p < listSrc.length) {
        const nl = listSrc.indexOf('\n', p);
        const rawLine = nl === -1 ? listSrc.slice(p) : listSrc.slice(p, nl);
        const nextLine2 = rawLine;
        // Leading spaces of the raw line (spaces only: the break patterns
        // allow no tabs there), and its first non-space character within
        // the indent the patterns allow.
        let lead = 0;
        while (lead < rawLine.length && rawLine[lead] === ' ') lead++;
        const leadCapped = Math.min(lead, maxLead);
        const fc = leadCapped < rawLine.length ? rawLine[leadCapped] : '';
        if (fc === '`' || fc === '~') {
          if (listLineIsFence(rawLine, leadCapped)) break;
        } else if (fc === '#') {
          if (listLineIsHeading(rawLine, leadCapped)) break;
        } else if (fc === '<') {
          if (htmlBeginRegex.test(nextLine2)) break;
        } else if (fc === '>') {
          break;
        } else if (fc === '*' || fc === '+' || fc === '-' || (fc >= '0' && fc <= '9')) {
          if (listLineIsBullet(rawLine, leadCapped)) break;
          if (listLineIsHr(rawLine, leadCapped)) break;
        }
        // Re-align to follow commonmark nesting rules.
        const nextLineWithoutTabs = (rawLine[0] === ' ' || rawLine[0] === '\t')
          ? nextLine2.replace(LEADING_SPACE_TAB, (ws) => expandTabs(ws))
          : nextLine2;
        let nwLead = 0;
        while (nwLead < nextLineWithoutTabs.length && nextLineWithoutTabs[nwLead] === ' ') nwLead++;
        const isBlankLine = nwLead === nextLineWithoutTabs.length;
        if (nwLead >= indent || isBlankLine) { // Dedent if possible
          itemContents += '\n' + nextLineWithoutTabs.slice(indent);
        } else {
          // not enough indentation
          if (blankLine) break;
          if ((line.includes('\t') ? line.replace(TAB_GLOBAL, '    ') : line).search(NON_SPACE) >= 4) break; // indented code block
          if (fencesBeginRegex.test(line)) break;
          if (headingBeginRegex.test(line)) break;
          if (htmlBeginRegex.test(line)) break;
          if (hrRegex.test(line)) break;
          const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine2)
            && lheadingGfmRe.test(`${line}\n${nextLine2}`);
          const continuation = setextContinuation
            ? `    ${nextLineWithoutTabs.replace(/^ {0,3}/, '')}`
            : nextLine2;
          itemContents += '\n' + continuation;
        }
        blankLine = isBlankLine;
        p = nl === -1 ? listSrc.length : nl + 1;
        line = nextLineWithoutTabs.slice(indent);
      }
    }
    const raw = listSrc.slice(itemStart, p);
    if (!list.loose) {
      if (endsWithBlankLine) list.loose = true;
      else if (/\n[ \t]*\n[ \t]*$/.test(raw)) endsWithBlankLine = true;
    }
    list.items.push({
      type: 'list_item', raw,
      task: LIST_IS_TASK.test(itemContents),
      loose: false, text: itemContents, tokens: [],
    });
    taken = p;
  }
  const lastItem = list.items.at(-1);
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    return null;
  }
  list.raw = listSrc.slice(0, taken).trimEnd();
  for (const item of list.items) {
    S.top = false;
    item.tokens = blockTokensInto(S, item.text, [], false);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.type === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => ANY_LINE.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken?.type === 'text' || itemToken?.type === 'paragraph')) {
      item.text = item.text.replace(LIST_REPLACE_TASK, '');
      itemToken.raw = itemToken.raw.replace(LIST_REPLACE_TASK, '');
      itemToken.text = itemToken.text.replace(LIST_REPLACE_TASK, '');
      for (let i = S.queue.length - 1; i >= 0; i--) {
        if (LIST_IS_TASK.test(S.queue[i].src)) {
          S.queue[i].src = S.queue[i].src.replace(LIST_REPLACE_TASK, '');
          break;
        }
      }
      const taskRaw = LIST_TASK_CHECKBOX.exec(item.raw);
      if (taskRaw) {
        const checkboxToken = { type: 'checkbox', raw: taskRaw[0] + ' ', checked: taskRaw[0] !== '[ ]' };
        item.checked = checkboxToken.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
            item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkboxToken);
          } else {
            item.tokens.unshift({ type: 'paragraph', raw: checkboxToken.raw, text: checkboxToken.raw, tokens: [checkboxToken] });
          }
        } else {
          item.tokens.unshift(checkboxToken);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const token of item.tokens) {
        if (token.type === 'text') token.type = 'paragraph';
      }
    }
  }
  // The lexer advances by the trimmed raw, so trailing blank lines are
  // re-lexed as space tokens (that is what makes a list loose).
  return { ...list, end: pos + list.raw.length };
}

function tokHtml(S, src, pos) {
  const cap = execAt(S_HTML, src, pos);
  if (!cap) return null;
  const raw = trimTrailingBlankLines(cap[0]);
  return {
    type: 'html', block: true, raw,
    pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
    text: raw, end: pos + cap[0].length,
  };
}

function tokDef(S, src, pos) {
  const cap = execAt(S_DEF, src, pos);
  if (!cap) return null;
  if (!START_ANGLE.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return null;
  const tag = normalizeLabel(cap[1]);
  const href = cap[2] ? cap[2].replace(HREF_BRACKETS, '$1').replace(anyPunctRe, '$1') : '';
  const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(anyPunctRe, '$1') : cap[3];
  return { type: 'def', tag, raw: rtrim(cap[0], '\n'), href, title, end: pos + cap[0].length };
}

function tokTable(S, src, pos) {
  const cap = execAt(S_TABLE, src, pos);
  if (!cap) return null;
  if (!TABLE_DELIM.test(cap[2])) return null;
  const headers = splitCells(cap[1]);
  const aligns = cap[2].replace(TABLE_ALIGN_CHARS, '').split('|');
  const rows = cap[3]?.trim() ? cap[3].replace(TABLE_ROW_BLANK, '').split('\n') : [];
  const item = { type: 'table', raw: rtrim(cap[0], '\n'), header: [], align: [], rows: [] };
  if (headers.length !== aligns.length) return null;
  for (const align of aligns) {
    if (TABLE_ALIGN_RIGHT.test(align)) item.align.push('right');
    else if (TABLE_ALIGN_CENTER.test(align)) item.align.push('center');
    else if (TABLE_ALIGN_LEFT.test(align)) item.align.push('left');
    else item.align.push(null);
  }
  for (let i = 0; i < headers.length; i++) {
    const tokens = [];
    S.queue.push({ src: headers[i], tokens });
    item.header.push({ text: headers[i], tokens, header: true, align: item.align[i] });
  }
  for (const row of rows) {
    item.rows.push(splitCells(row, item.header.length).map((cell, i) => {
      const tokens = [];
      S.queue.push({ src: cell, tokens });
      return { text: cell, tokens, header: false, align: item.align[i] };
    }));
  }
  return { ...item, end: pos + cap[0].length };
}

function tokLheading(S, src, pos) {
  const cap = execAt(S_LHEADING, src, pos);
  if (!cap) return null;
  const text = cap[1].trim();
  const tokens = [];
  S.queue.push({ src: text, tokens });
  return {
    type: 'heading', raw: rtrim(cap[0], '\n'),
    depth: cap[2].charAt(0) === '=' ? 1 : 2, text, tokens,
    end: pos + cap[0].length,
  };
}

function tokParagraph(S, src, pos) {
  const cap = execAt(S_PARAGRAPH, src, pos);
  if (!cap) return null;
  const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
  const tokens = [];
  S.queue.push({ src: text, tokens });
  return { type: 'paragraph', raw: cap[0], text, tokens, end: pos + cap[0].length };
}

function tokText(S, src, pos) {
  const cap = execAt(S_TEXT, src, pos);
  if (!cap) return null;
  const tokens = [];
  S.queue.push({ src: cap[0], tokens });
  return { type: 'text', raw: cap[0], text: cap[0], tokens, end: pos + cap[0].length };
}

// ------------------------------------------------------------ the block loop
// Walks src by index. First character dispatches to the tokenizers that can
// match there, in marked's order; the loop body mirrors marked's merging of
// paragraph / text / code / def continuations into the previous token.

function blockTokensInto(S, src, tokens, lastParagraphClipped) {
  let pos = 0;
  const len = src.length;
  let srcLength = Infinity;
  while (pos < len) {
    if (len - pos < srcLength) srcLength = len - pos;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    const ch = src[pos];
    let token = null;
    let kind = -1; // which tokenizer matched, for the merge rules below
    // Cheap dispatch on the first character (spaces skipped up to 3 for the
    // lookahead char); every candidate still runs in marked's order.
    let c1 = ch;
    if (ch === ' ' || ch === '\t') {
      let j = pos;
      while (j < len && j - pos < 3 && (src[j] === ' ')) j++;
      c1 = src[j] ?? '';
    }
    if (ch === '\n' || ch === ' ' || ch === '\t') {
      if ((token = tokSpace(S, src, pos))) kind = 0;
    }
    if (!token && (ch === ' ' || ch === '\t') && (token = tokCode(S, src, pos))) kind = 1;
    if (!token && (c1 === '`' || c1 === '~' || ch === ' ') && (token = tokFences(S, src, pos))) kind = 2;
    if (!token && (c1 === '#' || ch === ' ') && (token = tokHeading(S, src, pos))) kind = 3;
    if (!token && (c1 === '-' || c1 === '_' || c1 === '*' || ch === ' ') && (token = tokHr(S, src, pos))) kind = 4;
    if (!token && (c1 === '>' || ch === ' ') && (token = tokBlockquote(S, src, pos))) kind = 5;
    if (!token && (c1 === '*' || c1 === '+' || c1 === '-' || (c1 >= '0' && c1 <= '9') || ch === ' ') && (token = tokList(S, src, pos))) kind = 6;
    if (!token && (c1 === '<' || ch === ' ') && (token = tokHtml(S, src, pos))) kind = 7;
    if (!token && (c1 === '[' || ch === ' ') && (token = tokDef(S, src, pos))) kind = 8;
    if (!token && (token = tokTable(S, src, pos))) kind = 9;
    if (!token && (token = tokLheading(S, src, pos))) kind = 10;
    if (!token && S.top && (token = tokParagraph(S, src, pos))) kind = 11;
    if (!token && (token = tokText(S, src, pos))) kind = 12;

    if (!token) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));

    if (kind === 0) { // space
      const lastToken = tokens.at(-1);
      if (token.raw.length === 1 && lastToken !== undefined) lastToken.raw += '\n';
      else tokens.push(token);
      pos = token.end;
      continue;
    }
    if (kind === 1) { // indented code: cannot interrupt a paragraph
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.queue.at(-1).src = lastToken.text;
      } else tokens.push(token);
      pos = token.end;
      continue;
    }
    if (kind === 8) { // def
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.raw;
        S.queue.at(-1).src = lastToken.text;
      } else {
        if (!S.links[token.tag]) S.links[token.tag] = { href: token.href, title: token.title };
        tokens.push(token);
      }
      pos = token.end;
      continue;
    }
    if (kind === 11) { // paragraph
      const lastToken = tokens.at(-1);
      if (lastParagraphClipped && lastToken?.type === 'paragraph') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.queue.pop();
        S.queue.at(-1).src = lastToken.text;
      } else tokens.push(token);
      // No extensions: a paragraph is never clipped, so only the first
      // paragraph of a blockquote continuation chunk can merge.
      lastParagraphClipped = false;
      pos = token.end;
      continue;
    }
    if (kind === 12) { // text
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.queue.pop();
        S.queue.at(-1).src = lastToken.text;
      } else tokens.push(token);
      pos = token.end;
      continue;
    }
    tokens.push(token);
    pos = token.end;
  }
  S.top = true;
  return tokens;
}

// -------------------------------------------------------- inline tokenizers

function linkInText(S, text) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(blockSkipRe)) {
    if (linkRe.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
  }
  for (const match of text.matchAll(reflinkSearchRe)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(S.links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(S, match0.slice(1, refStart - 1))) continue;
    return true;
  }
  return false;
}

// Mask links, code, html and escapes so emStrong and del do not see their
// delimiters inside them. Every mask keeps the length it replaces.
// This mirrors marked's three .replace() scans, in the same order, but as
// three cheap manual walks instead of global regex scans: each walk jumps
// between trigger characters with a native regex and tries the span regexes
// anchored there, so they never scan plain text.
//  - pass A (reflinks): a defined reflink/nolink is masked to '[aaa...]'
//    (or, when its text holds a link, the text stays visible and only the
//    inner links and the ref are masked). The walk advances past every
//    match, defined or not, exactly like a global replace.
//  - pass B (escapes and code spans): an escape becomes '+'s (punctuation,
//    so flanking is preserved); a code span keeps its backticks but its
//    inner backticks become '+'. A failed code span consumes the whole
//    backtick run, so a later backtick in the run can never start one.
//  - pass C (links, code spans, html tags): each becomes '[aaa...]'. A
//    code span here must not be preceded by a backtick (the block-skip
//    pass's (?<!`) lookbehind). Running B before C matters: normalising a
//    code span's inner backtick is what lets a link label containing it
//    match at all.
const PUNCT_1 = /[\p{P}\p{S}]/u;
const NEXT_A = /[![]/g;
const NEXT_B = /[\\`]/g;
const NEXT_C = /[`\[<]/g;
const BS_LINK_STICKY = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/y;
const BS_HTML_STICKY = /<(?! )[^<>]*?>/y;
const REFLINK_STICKY = new RegExp(reflinkSearchRe.source, 'y');
const CODE_STICKY = sticky(inlineCodeRe);

function maskReflink(S, match0) {
  const refStart = match0.lastIndexOf('[');
  if (!Object.hasOwn(S.links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
  if (refStart > 1 && match0.charAt(0) !== '!') {
    const text = match0.slice(1, refStart - 1);
    if (linkInText(S, text)) {
      return '[' + text.replace(reflinkSearchRe, (m) => maskReflink(S, m)) + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
    }
  }
  return '[' + 'a'.repeat(match0.length - 2) + ']';
}

function maskReflinks(S, src) {
  const len = src.length;
  let out = null;
  let chunkStart = 0;
  NEXT_A.lastIndex = 0;
  let m;
  while ((m = NEXT_A.exec(src)) !== null) {
    const j = m.index;
    const cap = execAt(REFLINK_STICKY, src, j);
    if (!cap) continue;
    const masked = maskReflink(S, cap[0]);
    const end = j + cap[0].length;
    if (masked !== cap[0]) {
      if (out === null) out = [];
      if (j > chunkStart) out.push(src.slice(chunkStart, j));
      out.push(masked);
      chunkStart = end;
    }
    NEXT_A.lastIndex = end;
  }
  if (out === null) return src;
  if (len > chunkStart) out.push(src.slice(chunkStart, len));
  return out.join('');
}

function normalizeCodeEscapes(src) {
  const len = src.length;
  let out = null;
  let chunkStart = 0;
  NEXT_B.lastIndex = 0;
  let m;
  while ((m = NEXT_B.exec(src)) !== null) {
    const j = m.index;
    if (src[j] === '\\') {
      // An escape: backslash before a punctuation character (possibly astral).
      let n = 0;
      if (j + 1 < len) {
        const c1 = src.charCodeAt(j + 1);
        if (c1 >= 0xd800 && c1 <= 0xdbff && j + 2 < len) {
          const c2 = src.charCodeAt(j + 2);
          if (c2 >= 0xdc00 && c2 <= 0xdfff && PUNCT_1.test(src.slice(j + 1, j + 3))) n = 3;
        }
        if (n === 0 && PUNCT_1.test(src[j + 1])) n = 2;
      }
      if (n > 0) {
        if (out === null) out = [];
        if (j > chunkStart) out.push(src.slice(chunkStart, j));
        out.push('+'.repeat(n));
        chunkStart = j + n;
        NEXT_B.lastIndex = j + n;
      }
    } else { // '`'
      const cap = execAt(CODE_STICKY, src, j);
      if (cap) {
        const run = cap[1].length;
        if (out === null) out = [];
        if (j > chunkStart) out.push(src.slice(chunkStart, j));
        out.push(cap[1] + cap[0].slice(run, -run).replace(/`/g, '+') + cap[1]);
        chunkStart = j + cap[0].length;
        NEXT_B.lastIndex = j + cap[0].length;
      } else {
        // No code span starts here: the whole backtick run is literal.
        let k = j + 1;
        while (k < len && src[k] === '`') k++;
        NEXT_B.lastIndex = k;
      }
    }
  }
  if (out === null) return src;
  if (len > chunkStart) out.push(src.slice(chunkStart, len));
  return out.join('');
}

function maskBlockSkip(src) {
  const len = src.length;
  let out = null;
  let chunkStart = 0;
  NEXT_C.lastIndex = 0;
  let m;
  while ((m = NEXT_C.exec(src)) !== null) {
    const j = m.index;
    const ch = src[j];
    if (ch === '[') {
      const cap = execAt(BS_LINK_STICKY, src, j);
      if (cap) {
        if (out === null) out = [];
        if (j > chunkStart) out.push(src.slice(chunkStart, j));
        out.push('[' + 'a'.repeat(cap[0].length - 2) + ']');
        chunkStart = j + cap[0].length;
        NEXT_C.lastIndex = j + cap[0].length;
      }
    } else if (ch === '`') {
      // A code span must not be preceded by a backtick.
      if (j > 0 && src[j - 1] === '`') continue;
      const cap = execAt(CODE_STICKY, src, j);
      if (cap) {
        if (out === null) out = [];
        if (j > chunkStart) out.push(src.slice(chunkStart, j));
        out.push('[' + 'a'.repeat(cap[0].length - 2) + ']');
        chunkStart = j + cap[0].length;
        NEXT_C.lastIndex = j + cap[0].length;
      } else {
        // No code span starts here, and the lookbehind blocks the rest
        // of this backtick run. Skip the run.
        let k = j + 1;
        while (k < len && src[k] === '`') k++;
        NEXT_C.lastIndex = k;
      }
    } else { // '<'
      const cap = execAt(BS_HTML_STICKY, src, j);
      if (cap) {
        if (out === null) out = [];
        if (j > chunkStart) out.push(src.slice(chunkStart, j));
        out.push('[' + 'a'.repeat(cap[0].length - 2) + ']');
        chunkStart = j + cap[0].length;
        NEXT_C.lastIndex = j + cap[0].length;
      }
    }
  }
  if (out === null) return src;
  if (len > chunkStart) out.push(src.slice(chunkStart, len));
  return out.join('');
}

function maskSrc(S, src) {
  return maskBlockSkip(normalizeCodeEscapes(maskReflinks(S, src)));
}

function outputLink(cap, link, raw, S) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(OUTPUT_LINK_REPLACE, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = S.inLink;
  const outerLinkEmitted = S.linkEmitted;
  const outerInRawBlock = S.inRawBlock;
  S.inLink = true;
  S.linkEmitted = false;
  const tokens = inlineTokens(S, text, []);
  const textHasLink = S.linkEmitted;
  S.linkEmitted = outerLinkEmitted;
  S.inLink = outerInLink;
  if (!isImage) {
    // Links may not contain other links, at any level of nesting. Bail so
    // the caller falls through to text and the inner link is the one kept.
    if (textHasLink) {
      S.inRawBlock = outerInRawBlock;
      return undefined;
    }
    S.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href, title, text, tokens };
}

function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = inlineCodeRe.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = tagRe.exec(tokenSrc) || autolinkRe.exec(tokenSrc);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

function tokEscape(S, src) {
  const cap = escapeRe.exec(src);
  if (cap) return { type: 'escape', raw: cap[0], text: cap[1] };
  return undefined;
}

function tokTag(S, src) {
  const cap = tagRe.exec(src);
  if (!cap) return undefined;
  if (!S.inLink && START_A_TAG.test(cap[0])) S.inLink = true;
  else if (S.inLink && END_A_TAG.test(cap[0])) S.inLink = false;
  if (!S.inRawBlock && START_PRE_TAG.test(cap[0])) S.inRawBlock = true;
  else if (S.inRawBlock && END_PRE_TAG.test(cap[0])) S.inRawBlock = false;
  return { type: 'html', raw: cap[0], inLink: S.inLink, inRawBlock: S.inRawBlock, block: false, text: cap[0] };
}

function tokLink(S, src) {
  if (S.linkParenPossible === false) return undefined;
  const cap = linkRe.exec(src);
  if (!cap) return undefined;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, cap[1], labelStart)) return undefined;
  const trimmedUrl = cap[2].trim();
  if (START_ANGLE.test(trimmedUrl)) {
    if (!END_ANGLE.test(trimmedUrl)) return undefined;
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return undefined;
  } else {
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return undefined;
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  // The ')' that ends the match is the link closer only when it is not
  // escaped: `[foo](/url\)` has no closer.
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return undefined;
  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (START_ANGLE.test(href)) href = href.slice(1, -1);
  return outputLink(cap, {
    href: href ? href.replace(anyPunctRe, '$1') : href,
    title: title ? title.replace(anyPunctRe, '$1') : title,
  }, cap[0], S);
}

function tokReflink(S, src) {
  let cap;
  if ((cap = reflinkRe.exec(src)) || (cap = nolinkRe.exec(src))) {
    const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
    if (isLabelEndInsideToken(src, cap[1], labelStart)) return undefined;
    const link = S.links[normalizeLabel(cap[2] || cap[1])];
    if (!link) {
      const text = cap[0].charAt(0);
      return { type: 'text', raw: text, text };
    }
    return outputLink(cap, link, cap[0], S);
  }
  return undefined;
}

function tokEmStrong(S, src, maskedSrc, prevChar = '') {
  let match = emStrongLDelimRe.exec(src);
  if (!match) return undefined;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return undefined;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = maskedSrc.length - src.length;
  let runStart = srcStart;
  while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) runStart--;
  // The last code point before the run (a surrogate pair counts as one).
  let runPrevChar = '';
  if (runStart > 0) {
    const c1 = maskedSrc.charCodeAt(runStart - 1);
    if (c1 >= 0xdc00 && c1 <= 0xdfff && runStart >= 2) {
      const c0 = maskedSrc.charCodeAt(runStart - 2);
      runPrevChar = (c0 >= 0xd800 && c0 <= 0xdbff) ? maskedSrc.slice(runStart - 2, runStart) : maskedSrc[runStart - 1];
    } else runPrevChar = maskedSrc[runStart - 1];
  }
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!punctuationRe.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!punctuationRe.exec(prevChar);
  if (match[4] && prevChar.match(UNICODE_ALNUM)) return undefined;
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    // The delimiter run is the leading run of delimChar in the match (the
    // character after it is never a delimiter by the regex's construction).
    let lLength = 0;
    while (lLength < match[0].length && match[0][lLength] === delimChar) lLength++;
    let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return undefined;
    const endReg = delimChar === '*' ? emStrongRDelimAstRe : emStrongRDelimUndRe;
    const lastPossible = lastEmCloser(S, maskedSrc, delimChar);
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastPossible < windowStart) return undefined;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastPossibleInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastPossibleInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = rDelim.length; // a run of '*' or '_' only
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      } else if (match[5] || match[6] || openerCanClose) {
        if (midRun && (match[5] || match[6])) break;
        if (runLength % 3 && !((runLength + rLength) % 3)) {
          midDelimTotal += rLength;
          continue;
        }
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      // Length in UTF-16 units of the match's first code point (1 or 2).
      const lastCharLength = match[0].codePointAt(0) > 0xffff ? 2 : 1;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: inlineTokens(S, text, []) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: inlineTokens(S, text, []) };
    }
  }
  return undefined;
}

function tokCodespan(S, src) {
  const cap = inlineCodeRe.exec(src);
  if (!cap) return undefined;
  let text = cap[2].replace(/\n/g, ' ');
  const hasNonSpaceChars = /[^ ]/.test(text);
  const hasSpaceCharsOnBothEnds = /^ /.test(text) && / $/.test(text);
  if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) text = text.substring(1, text.length - 1);
  return { type: 'codespan', raw: cap[0], text };
}

function tokBr(S, src) {
  const cap = brRe.exec(src);
  if (cap) return { type: 'br', raw: cap[0] };
  return undefined;
}

function tokDel(S, src, maskedSrc, prevChar = '') {
  let match = delLDelimRe.exec(src);
  if (!match) return undefined;
  const nextChar = match[1] || '';
  if (!nextChar || !prevChar || punctuationRe.exec(prevChar)) {
    // The delimiter run is the leading run of '~' in the match.
    let lLength = 0;
    while (lLength < match[0].length && match[0][lLength] === '~') lLength++;
    let rDelim, rLength, delimTotal = lLength;
    const endReg = delRDelimRe;
    const lastPossible = lastDelCloser(S, maskedSrc);
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastPossible < windowStart) return undefined;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastPossibleInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastPossibleInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = rDelim.length; // a run of '~' only
      if (rLength !== lLength) continue;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = match[0].codePointAt(0) > 0xffff ? 2 : 1;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      return { type: 'del', raw, text, tokens: inlineTokens(S, text, []) };
    }
  }
  return undefined;
}

function tokAutolink(S, src) {
  const cap = autolinkRe.exec(src);
  if (!cap) return undefined;
  let text, href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  return { type: 'link', raw: cap[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
}

function tokUrl(S, src) {
  let cap;
  if (cap = urlRe.exec(src)) {
    let text, href;
    if (cap[2] === '@') {
      text = cap[0];
      href = 'mailto:' + text;
    } else {
      let prevCapZero;
      do {
        prevCapZero = cap[0];
        cap[0] = backpedalRe.exec(cap[0])?.[0] ?? '';
      } while (prevCapZero !== cap[0]);
      text = cap[0];
      href = cap[1] === 'www.' ? 'http://' + cap[0] : cap[0];
    }
    return { type: 'link', raw: cap[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
  }
  return undefined;
}

function tokInlineText(S, src) {
  const cap = inlineTextRe.exec(src);
  if (!cap) return undefined;
  const escaped = S.inRawBlock;
  return {
    type: 'text', raw: cap[0],
    text: escaped ? cap[0] : decodeNumericRefs(cap[0]),
    escaped,
  };
}

function inlineTokens(S, src, tokens = []) {
  const prevLinkParenPossible = S.linkParenPossible;
  S.linkParenPossible = prevLinkParenPossible && src.includes(')');
  try {
    return inlineTokensInner(S, src, tokens);
  } finally {
    S.linkParenPossible = prevLinkParenPossible;
  }
}

function inlineTokensInner(S, src, tokens) {
  // Fast path: a run with no inline markup at all renders as one escaped
  // text token. Nothing here can open a link, emphasis, code span, tag,
  // entity or hard break, and with inRawBlock off the text is escaped.
  if (!S.inRawBlock && src.length > 0 && isPlainInline(src)) {
    // No escapable characters ('>' '"' "'") means the text is already what
    // the renderer would output, so it is marked escaped to skip re-scanning.
    tokens.push({ type: 'text', raw: src, text: src, escaped: !/[>"']/.test(src) });
    return tokens;
  }
  const maskedSrc = src.includes('*') || src.includes('_') || src.includes('~')
    ? maskSrc(S, src)
    : src;
  S.closerStack.push(scanClosers(maskedSrc));
  try {
    return tokenizeInlines(S, src, maskedSrc, tokens);
  } finally {
    S.closerStack.pop();
  }
}

// True when an inline run holds nothing the inline tokenizers could act on:
// no escape, tag, link, emphasis, code span, strikethrough, entity or
// autolink trigger, and no hard break.
const PLAIN_TRIGGER = /[\\<\[!*_`~&@]/;
function isPlainInline(src) {
  return !PLAIN_TRIGGER.test(src) && !src.includes('www.') && !src.includes('://') && !src.includes('  \n');
}

// Could the GFM url regex match at the start of src? The url alternatives
// start with www., a protocol, mailto:/xmpp:, or an email local part
// (word characters) followed by '@'.
function urlMayMatch(src) {
  const a = src.charCodeAt(0) | 32;
  const b = src.charCodeAt(1) | 32;
  if (a === 119 && b === 119 && (src.charCodeAt(2) | 32) === 119 && src.charCodeAt(3) === 46) return true; // www.
  if (a === 109 && b === 97 && (src.charCodeAt(2) | 32) === 105 && (src.charCodeAt(3) | 32) === 108 && (src.charCodeAt(4) | 32) === 116 && (src.charCodeAt(5) | 32) === 111 && src.charCodeAt(6) === 58) return true; // mailto:
  if (a === 120 && b === 109 && (src.charCodeAt(2) | 32) === 112 && (src.charCodeAt(3) | 32) === 112 && src.charCodeAt(4) === 58) return true; // xmpp:
  if (a === 104 && b === 116 && (src.charCodeAt(2) | 32) === 116 && (src.charCodeAt(3) | 32) === 112) { // http(s)://
    let i = 4;
    if ((src.charCodeAt(4) | 32) === 115) i = 5;
    if (src.charCodeAt(i) === 58 && src.charCodeAt(i + 1) === 47 && src.charCodeAt(i + 2) === 47) return true;
  }
  if (a === 102 && b === 116 && (src.charCodeAt(2) | 32) === 112 && src.charCodeAt(3) === 58 && src.charCodeAt(4) === 47 && src.charCodeAt(5) === 47) return true; // ftp://
  // an email: word characters, then '@'
  for (let i = 0; i < src.length; i++) {
    const ch = src.charCodeAt(i);
    if (ch === 64) return true;
    if (!((ch >= 48 && ch <= 57) || (ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) || ch === 46 || ch === 95 || ch === 43 || ch === 45)) return false;
  }
  return false;
}

function tokenizeInlines(S, src, maskedSrc, tokens) {
  let keepPrevChar = false;
  let prevChar = '';
  let srcLength = Infinity;
  while (src) {
    if (src.length < srcLength) srcLength = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    if (!keepPrevChar) prevChar = '';
    keepPrevChar = false;
    // First-character dispatch: only the tokenizers that can match a string
    // starting with this character are tried, in marked's order; the rest
    // fall through to inline text.
    const c = src[0];
    let token;
    if (c === '\\') {
      if ((token = tokEscape(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
      if ((token = tokBr(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (c === '<') {
      if ((token = tokTag(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
      if ((token = tokAutolink(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (c === '[' || c === '!') {
      if ((token = tokLink(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
      if ((token = tokReflink(S, src))) {
        src = src.substring(token.raw.length);
        const lastToken = tokens.at(-1);
        if (token.type === 'text' && lastToken?.type === 'text') {
          lastToken.raw += token.raw;
          lastToken.text += token.text;
        } else tokens.push(token);
        continue;
      }
    } else if (c === '*' || c === '_') {
      if ((token = tokEmStrong(S, src, maskedSrc, prevChar))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (c === '`') {
      if ((token = tokCodespan(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (c === '~') {
      if ((token = tokDel(S, src, maskedSrc, prevChar))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (c === ' ') {
      if ((token = tokBr(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    } else if (!S.inLink && urlMayMatch(src)) {
      if ((token = tokUrl(S, src))) { src = src.substring(token.raw.length); tokens.push(token); continue; }
    }
    if ((token = tokInlineText(S, src))) {
      src = src.substring(token.raw.length);
      if (token.raw.slice(-1) !== '_') prevChar = token.raw.slice(-1);
      keepPrevChar = true;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += token.raw;
        lastToken.text += token.text;
      } else tokens.push(token);
      continue;
    }
    if (src) throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  return tokens;
}

// ----------------------------------------------------------------- rendering

function renderCheckbox(token) {
  return '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
}

function renderTextToken(S, token) {
  if ('tokens' in token && token.tokens) return renderInline(S, token.tokens);
  return ('escaped' in token && token.escaped) ? token.text : escapeHtml(token.text);
}

function renderCode(token) {
  const langString = (token.lang || '').match(/^\S*/)?.[0];
  const code = token.text ? token.text.replace(/\n$/, '') + '\n' : '';
  if (!langString) return '<pre><code>' + escapeHtml(code, true) + '</code></pre>\n';
  return '<pre><code class="language-' + escapeHtml(langString) + '">' + escapeHtml(code, true) + '</code></pre>\n';
}

function renderTableCell(S, cell) {
  const content = renderInline(S, cell.tokens);
  const type = cell.header ? 'th' : 'td';
  const tag = cell.align ? `<${type} align="${cell.align}">` : `<${type}>`;
  return tag + content + `</${type}>\n`;
}

function renderTable(S, token) {
  let cell = '';
  for (const h of token.header) cell += renderTableCell(S, h);
  let header = `<tr>\n${cell}</tr>\n`;
  let body = '';
  for (const row of token.rows) {
    cell = '';
    for (const c of row) cell += renderTableCell(S, c);
    body += `<tr>\n${cell}</tr>\n`;
  }
  if (body) body = `<tbody>${body}</tbody>`;
  return '<table>\n<thead>\n' + header + '</thead>\n' + body + '</table>\n';
}

function renderLink(S, token) {
  const parsedText = token.autolink ? escapeHtml(token.text, true) : renderInline(S, token.tokens);
  const cleanHref = cleanUrl(token.href);
  if (cleanHref === null) return parsedText;
  const href = escapeHtml(cleanHref, token.autolink);
  let out = '<a href="' + href + '"';
  if (token.title) out += ' title="' + escapeHtml(token.title) + '"';
  out += '>' + parsedText + '</a>';
  return out;
}

function renderImage(S, token) {
  let text = token.text;
  if (token.tokens) text = renderTextInline(S, token.tokens);
  const cleanHref = cleanUrl(token.href);
  if (cleanHref === null) return escapeHtml(text);
  let out = `<img src="${escapeHtml(cleanHref)}" alt="${escapeHtml(text)}"`;
  if (token.title) out += ` title="${escapeHtml(token.title)}"`;
  out += '>';
  return out;
}

// Text-only rendering (image alt text): no markup, just the words.
function renderTextInline(S, tokens) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'strong':
      case 'em':
      case 'del':
        out += token.tokens ? renderTextInline(S, token.tokens) : token.text;
        break;
      case 'codespan':
      case 'html':
      case 'text':
      case 'escape':
        out += token.text;
        break;
      case 'link':
      case 'image':
        out += token.tokens ? renderTextInline(S, token.tokens) : token.text;
        break;
      case 'br':
        break;
      case 'checkbox':
        out += token.raw;
        break;
      default:
        throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

function renderInline(S, tokens) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'escape': out += renderTextToken(S, token); break;
      case 'html': out += token.text; break;
      case 'link': out += renderLink(S, token); break;
      case 'image': out += renderImage(S, token); break;
      case 'checkbox': out += renderCheckbox(token); break;
      case 'strong': out += `<strong>${renderInline(S, token.tokens)}</strong>`; break;
      case 'em': out += `<em>${renderInline(S, token.tokens)}</em>`; break;
      case 'codespan': out += `<code>${escapeHtml(token.text, true)}</code>`; break;
      case 'br': out += '<br>'; break;
      case 'del': out += `<del>${renderInline(S, token.tokens)}</del>`; break;
      case 'text': out += renderTextToken(S, token); break;
      default: throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

function renderTokens(S, tokens) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'space': break;
      case 'hr': out += '<hr>\n'; break;
      case 'heading': out += `<h${token.depth}>${renderInline(S, token.tokens)}</h${token.depth}>\n`; break;
      case 'code': out += renderCode(token); break;
      case 'table': out += renderTable(S, token); break;
      case 'blockquote': out += `<blockquote>\n${renderTokens(S, token.tokens)}</blockquote>\n`; break;
      case 'list': {
        let body = '';
        for (const item of token.items) body += `<li>${renderTokens(S, item.tokens)}</li>\n`;
        const type = token.ordered ? 'ol' : 'ul';
        const startAttr = (token.ordered && token.start !== 1) ? (' start="' + token.start + '"') : '';
        out += '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
        break;
      }
      case 'checkbox': out += renderCheckbox(token); break;
      case 'html': out += token.text; break;
      case 'def': break;
      case 'paragraph': out += `<p>${renderInline(S, token.tokens)}</p>\n`; break;
      case 'text': out += renderTextToken(S, token); break;
      default: throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

