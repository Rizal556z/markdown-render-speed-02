// A fast drop-in for marked 18.1.3 (default options: GFM on, breaks off,
// pedantic off). parse(markdown) returns exactly the HTML marked renders,
// byte for byte, for every input; it just gets there quicker.
//
// How it works, in three layers:
//   1. A cursor-based block scanner walks the source once, deciding each
//      block with anchored patterns applied at the cursor (no repeated
//      substring copies of the remainder). It collects link reference
//      definitions and queues every stretch of inline content in order.
//   2. An inline renderer turns each queued stretch into tokens with a
//      first-character dispatch loop, so each position tries one or two
//      patterns instead of a dozen. Plain stretches take a fast path that
//      skips tokenising altogether.
//   3. A small renderer walks the block tree and joins the HTML.
//
// The grammar patterns below are the ones that define marked's behaviour
// (its block and inline rules); the scanner, the inline loop and the
// renderer around them are written from scratch for speed.

// ---------------------------------------------------------------------------
// Pattern assembly helpers
// ---------------------------------------------------------------------------

// Global string substitution inside a pattern source (all occurrences).
function subAll(src, name, val) {
  return src.split(name).join(val);
}

// Turn a ^-anchored pattern into a sticky one that matches at a cursor
// position instead of at the start of a string. Sticky matching is the
// anchor, so the leading ^ is dropped.
function sticky(re) {
  const flags = re.flags.replace('g', '').replace('m', '') + 'y';
  return new RegExp(re.source.replace(/^\^/, ''), flags);
}

// Run a sticky pattern at `pos` in `src`; null when it does not match there.
function at(re, src, pos) {
  re.lastIndex = pos;
  return re.exec(src);
}

// ---------------------------------------------------------------------------
// Grammar: block patterns
// ---------------------------------------------------------------------------

const BLOCK_TAG = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

const HR_BODY = '(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})';
const BULLET = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const BLOCK_CODE_START = '(?: {4}| {0,3}\\t)';
const FENCES_START = ' {0,3}(?:`{3,}|~{3,})';
const BLOCKQUOTE_START = ' {0,3}>';
const HEADING_START = ' {0,3}#{1,6}(?:\\s|$)';
const HTML_NARROW = ' {0,3}<[^\\n>]+>\\n';
// The html interrupt a paragraph (and a setext body) recognises: any of the
// block-html start conditions, types 1-6.
const HTML_INTERRUPT = ' {0,3}(?:</?(?:' + BLOCK_TAG + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';
// The table row that can interrupt a paragraph / setext body.
const TABLE_INTERRUPT = ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n';

const reNewline = /^ *(?:[ \t]*(?:\n|$))+/;
// Indented code: lines indented 4 spaces (or a tab), with blank lines kept.
const reBlockCode = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const reFences = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const reHr = new RegExp('^ {0,3}(' + HR_BODY + ')(?:\\n+|$)');
const reHeading = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;

// Setext heading. The body is a lazy run of lines, each continuation line
// passing the interrupt lookahead; the underline is = or -.
const LHEADING_CORE = '^(?!BULLET |BLOCKCODE|FENCES|BLOCKQUOTE|HEADING|HR|HTML|TABLE)'
  + '((?:.|\\n(?!\\s*?\\n|BULLET |FENCES|BLOCKQUOTE|HEADING|HR|HTML|TABLE))+?)'
  + '\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
function buildLheading() {
  let s = LHEADING_CORE;
  s = subAll(s, 'BULLET ', BULLET + ' ');
  s = subAll(s, 'BLOCKCODE', BLOCK_CODE_START);
  s = subAll(s, 'FENCES', FENCES_START);
  s = subAll(s, 'BLOCKQUOTE', BLOCKQUOTE_START);
  s = subAll(s, 'HEADING', HEADING_START);
  s = subAll(s, 'HR', ' {0,3}' + HR_BODY + '(?:\\n+|$)');
  s = subAll(s, 'HTML', HTML_NARROW);
  s = subAll(s, 'TABLE', TABLE_INTERRUPT);
  return new RegExp(s);
}
const reLheading = buildLheading();

// A link reference definition: [label]: destination "title"
const BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const DEF_TITLE = '(?:"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))';
const reDef = new RegExp('^ {0,3}\\[' + BLOCK_LABEL + '\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)'
  + '(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(' + DEF_TITLE + '))? *(?:\\n+|$)');

// HTML block: seven alternatives, (1) script/pre/style/textarea, (2) comment,
// (3) processing instruction, (4) declaration, (5) CDATA, (6) block tag,
// (7) any other open/close tag that ends the line.
const COMMENT = '<!--(?:-?>|[\\s\\S]*?(?:-->|$))';
const reHtml = new RegExp('^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|COMMENT[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(TAG)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:ATTR)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + ')', 'i');
const reHtmlBuilt = (() => {
  let s = reHtml.source;
  s = subAll(s, 'COMMENT', COMMENT);
  s = subAll(s, 'TAG', BLOCK_TAG);
  s = subAll(s, 'ATTR', ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?');
  return new RegExp(s, 'i');
})();

// GFM table: header line, delimiter row, then rows until an interrupting
// construct or a blank line.
const reTable = (() => {
  let s = '^ *([^\\n ].*)\\n'
    + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
    + '(?:\\n((?:(?! *\\n|HR|HEADING|BLOCKQUOTE|CODE|FENCES|LIST|HTML).*(?:\\n|$))*)\\n*|$)';
  s = subAll(s, 'HR', ' {0,3}' + HR_BODY + '(?:\\n+|$)');
  s = subAll(s, 'HEADING', HEADING_START);
  s = subAll(s, 'BLOCKQUOTE', BLOCKQUOTE_START);
  s = subAll(s, 'CODE', '(?: {4}| {0,3}\\t)[^\\n]');
  s = subAll(s, 'FENCES', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)');
  s = subAll(s, 'LIST', ' {0,3}(?:[*+-]|1[.)])[ \\t]');
  s = subAll(s, 'HTML', HTML_INTERRUPT);
  s = subAll(s, 'TAG', BLOCK_TAG);
  return new RegExp(s);
})();

// A list start: bullet + optional rest of the line.
const reListStart = new RegExp('^(' + BULLET.trim() + ')([ \\t][^\\n]*?)?(?:\\n|$)');
// Paragraph: lines that do not start an interrupting construct. Setext
// headings do not interrupt a paragraph (they are claimed first, at block
// level), but tables do in GFM.
const reParagraph = (() => {
  let s = '^([^\\n]+(?:\\n(?!HR|HEADING|BLOCKQUOTE|FENCES|LIST|HTML|TABLE|[ \\t]+\\n)[^\\n]+)*)';
  s = subAll(s, 'HR', ' {0,3}' + HR_BODY + '(?:\\n+|$)');
  s = subAll(s, 'HEADING', HEADING_START);
  s = subAll(s, 'BLOCKQUOTE', BLOCKQUOTE_START);
  s = subAll(s, 'FENCES', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)');
  s = subAll(s, 'LIST', ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]');
  s = subAll(s, 'HTML', HTML_INTERRUPT);
  s = subAll(s, 'TAG', BLOCK_TAG);
  s = subAll(s, 'TABLE', reTable.source.slice(1)); // table pattern without ^
  return new RegExp(s);
})();
// Inside a blockquote a bare list marker (any number) also interrupts.
const reBlockquoteParagraph = (() => {
  let s = '^([^\\n]+(?:\\n(?!HR|HEADING|BLOCKQUOTE|FENCES|LIST|HTML|TABLE|[ \\t]+\\n)[^\\n]+)*)';
  s = subAll(s, 'HR', ' {0,3}' + HR_BODY + '(?:\\n+|$)');
  s = subAll(s, 'HEADING', HEADING_START);
  s = subAll(s, 'BLOCKQUOTE', BLOCKQUOTE_START);
  s = subAll(s, 'FENCES', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)');
  s = subAll(s, 'LIST', ' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)');
  s = subAll(s, 'HTML', HTML_INTERRUPT);
  s = subAll(s, 'TAG', BLOCK_TAG);
  s = subAll(s, 'TABLE', '');
  return new RegExp(s);
})();
const reBlockquote = (() => {
  const s = '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(PARA)|[^\\n]*)(?:\\n|$))+';
  return new RegExp(subAll(s, 'PARA', reBlockquoteParagraph.source.slice(1)));
})();
const reBlockText = /^[^\n]+/;

// Sticky copies of the block patterns, for the cursor scanner.
const sNewline = sticky(reNewline);
const sBlockCode = sticky(reBlockCode);
const sFences = sticky(reFences);
const sHr = sticky(reHr);
const sHeading = sticky(reHeading);
const sLheading = sticky(reLheading);
const sDef = sticky(reDef);
const sHtml = sticky(reHtmlBuilt);
const sTable = sticky(reTable);
const sListStart = sticky(reListStart);
const sParagraph = sticky(reParagraph);
const sBlockquote = sticky(reBlockquote);
const sBlockText = sticky(reBlockText);

// Per-indent patterns used while collecting list items (cached by indent).
const indentCache = [];
function indentRegexes(indent) {
  const idx = Math.max(0, Math.min(3, indent - 1));
  let r = indentCache[idx];
  if (r) return r;
  const n = idx;
  r = {
    nextBullet: new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`),
    hr: new RegExp(`^ {0,${n}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`),
    fences: new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`),
    heading: new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`),
    html: new RegExp(`^ {0,${n}}(?:</?(?:${BLOCK_TAG})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'),
    blockquote: new RegExp(`^ {0,${n}}>`),
  };
  indentCache[idx] = r;
  return r;
}
function listItemRegex(bull) {
  return new RegExp(`^( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`);
}

// ---------------------------------------------------------------------------
// Grammar: inline patterns
// ---------------------------------------------------------------------------

const reInlineEscape = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const reInlineCode = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const reBr = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;

// Unicode punctuation classes (CommonMark's flanking rules).
const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_NOT_TILDE = '(?!~)[\\p{P}\\p{S}]';
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const PUNCT_SPACE_NOT_TILDE = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_NOT_TILDE = '(?:[^\\s\\p{P}\\p{S}]|~)';

// Emphasis / strong delimiters (GFM: ~ is not punctuation for em/strong).
const reEmLDelim = new RegExp(
  '^(?:\\*+(?:((?!\\*)' + PUNCT_NOT_TILDE + ')|([^\\s*]))?)'
  + '|^_+(?:((?!_)' + PUNCT_NOT_TILDE + ')|([^\\s_]))?', 'u');
const EM_R_CORE =
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)' // skip an orphan inside strong
  + '|[^*]+(?=[^*])' // consume to the delimiter
  + '|(?!\\*)PUNCT(\\*+)(?=[\\s]|$)' // (1) #*** : right only
  + '|NOTPUNCTSPACE(\\*+)(?!\\*)(?=PUNCTSPACE|$)' // (2) a***# : right only
  + '|(?!\\*)PUNCTSPACE(\\*+)(?=NOTPUNCTSPACE)' // (3) #***a : left only
  + '|[\\s](\\*+)(?!\\*)(?=PUNCT)' // (4) ***# : left only
  + '|(?!\\*)PUNCT(\\*+)(?!\\*)(?=PUNCT)' // (5) #***# : either
  + '|NOTPUNCTSPACE(\\*+)(?=NOTPUNCTSPACE)'; // (6) a***a : either
function buildEmRDelimAst() {
  let s = EM_R_CORE;
  s = subAll(s, 'NOTPUNCTSPACE', NOT_PUNCT_SPACE_NOT_TILDE);
  s = subAll(s, 'PUNCTSPACE', PUNCT_SPACE_NOT_TILDE);
  s = subAll(s, 'PUNCT', PUNCT_NOT_TILDE);
  return new RegExp(s, 'gu');
}
function buildEmRDelimUnd() {
  let s = '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)' // skip an orphan inside strong
    + '|[^_]+(?=[^_])' // consume to the delimiter
    + '|(?!_)PUNCT(_+)(?=[\\s]|$)' // (1)
    + '|NOTPUNCTSPACE(_+)(?!_)(?=PUNCTSPACE|$)' // (2)
    + '|(?!_)PUNCTSPACE(_+)(?=NOTPUNCTSPACE)' // (3)
    + '|[\\s](_+)(?!_)(?=PUNCT)' // (4)
    + '|(?!_)PUNCT(_+)(?!_)(?=PUNCT)'; // (5) (no rule 6 for _)
  s = subAll(s, 'NOTPUNCTSPACE', NOT_PUNCT_SPACE);
  s = subAll(s, 'PUNCTSPACE', PUNCT_SPACE);
  s = subAll(s, 'PUNCT', PUNCT);
  return new RegExp(s, 'gu');
}
const reEmRDelimAst = buildEmRDelimAst();
const reEmRDelimUnd = buildEmRDelimUnd();

// Strikethrough delimiters.
const reDelLDelim = new RegExp('^~~?(?:((?!~)' + PUNCT + ')|[^\\s~])', 'u');
function buildDelRDelim() {
  let s = '^[^~]+(?=[^~])' // consume to the delimiter
    + '|(?!~)PUNCT(~~?)(?=[\\s]|$)' // (1)
    + '|NOTPUNCTSPACE(~~?)(?!~)(?=PUNCTSPACE|$)' // (2)
    + '|(?!~)PUNCTSPACE(~~?)(?=NOTPUNCTSPACE)' // (3)
    + '|[\\s](~~?)(?!~)(?=PUNCT)' // (4)
    + '|(?!~)PUNCT(~~?)(?!~)(?=PUNCT)' // (5)
    + '|NOTPUNCTSPACE(~~?)(?=NOTPUNCTSPACE)'; // (6)
  s = subAll(s, 'NOTPUNCTSPACE', NOT_PUNCT_SPACE);
  s = subAll(s, 'PUNCTSPACE', PUNCT_SPACE);
  s = subAll(s, 'PUNCT', PUNCT);
  return new RegExp(s, 'gu');
}
const reDelRDelim = buildDelRDelim();

const reAnyPunct = new RegExp('\\\\(' + PUNCT + ')', 'gu');
// Escapes outside code spans, for the emphasis mask. A backslash is literal
// inside a code span, so code spans are matched whole and kept.
const reAnyPunctOutsideCode = new RegExp(
  '(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(' + PUNCT + ')', 'gu');
const rePunctTest = new RegExp('^((?![*_])' + PUNCT_SPACE + ')', 'u');

// Autolink <scheme:...> or <email>.
const reAutolink = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;

// Inline HTML tag (comment, close tag, open tag, PI, declaration, CDATA).
const INLINE_COMMENT = '<!--(?:-?>|[\\s\\S]*?-->)';
const reInlineTag = new RegExp('^' + INLINE_COMMENT
  + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>'
  + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:ATTR)*?\\s*/?>'
  + '|^<\\?[\\s\\S]*?\\?>'
  + '|^<![a-zA-Z]+\\s[\\s\\S]*?>'
  + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>');
const reInlineTagBuilt = (() => {
  const s = reInlineTag.source.replace('ATTR',
    '\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*"[^"]*"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s"\'=<>`]+)?');
  return new RegExp(s);
})();

// Link labels: one nested bracket pair at most, code spans allowed inside.
const INLINE_LABEL_BRACKETS = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const INLINE_LABEL = '(?:\\[(?:BRACKETS|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const LABEL = subAll(INLINE_LABEL, 'BRACKETS', INLINE_LABEL_BRACKETS);
const LINK_HREF = '<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))';
const LINK_TITLE = '"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)';
const reLink = new RegExp('^!?\\[(' + LABEL + ')\\]\\([ \\t\\n]*(' + LINK_HREF + ')(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(' + LINK_TITLE + '))?[ \\t\\n]*\\)');
const reReflink = new RegExp('^!?\\[(' + LABEL + ')\\]\\[(' + BLOCK_LABEL + ')\\]');
const reNolink = new RegExp('^!?\\[(' + BLOCK_LABEL + ')\\](?:\\[\\])?');

// The search form of the reference link patterns, bounded so a candidate
// that can never match still scans in linear time.
const BOUNDED_BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const BOUNDED_INLINE_LABEL = '(?:[^\\[\\]\\\\`]*(?:\\[(?:BRACKETS|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?';
const reReflinkSearch = new RegExp(
  subAll('^!?\\[(' + BOUNDED_INLINE_LABEL + ')\\]\\[(' + BOUNDED_BLOCK_LABEL + ')\\]', 'BRACKETS', INLINE_LABEL_BRACKETS)
  + '|^!?\\[(' + BOUNDED_BLOCK_LABEL + ')\\](?:\\[\\])?(?!\\()', 'g');

// Code spans / links / html, for the emphasis mask.
const reBlockSkip = new RegExp(
  '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)'
  + '|(?<!`)(?<b>`+)[^`]+\\k<b>(?!`)'
  + '|<(?! )[^<>]*?>', 'g');

// GFM extended autolink: mailto:/xmpp: email, scheme:// or www. host, email.
const EXT_EMAIL = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const EXT_EMAIL_PROTO = '(?:mailto:' + EXT_EMAIL + '|xmpp:' + EXT_EMAIL + '(?:\\/[A-Za-z0-9@.]+)?)';
const reUrl = new RegExp('^' + EXT_EMAIL_PROTO
  + '|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*'
  + '^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])');
const reBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Inline text (GFM). The pattern is not used directly: the scanner below
// reproduces its stops by hand (special characters, protocol://, www.,
// email starts, hard breaks), which is the same decision procedure without
// re-running a big pattern at every position. It is kept here as the
// reference for those stops.
const reInlineText = /^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/;

// ---------------------------------------------------------------------------
// Small shared patterns
// ---------------------------------------------------------------------------

const reCodeRemoveIndent = /^(?: {0,3}\t| {1,4})/gm;
const reIndentCodeComp = /^(\s+)(?:```)/;
const reBeginningSpace = /^\s+/;
const reEndingHash = /#$/;
const reStartingSpace = /^ /;
const reEndingSpace = / $/;
const reEndingSpaceTab = /[ \t]$/;
const reNonSpace = /[^ ]/;
const reNewlineGlobal = /\n/g;
const reTabGlobal = /\t/g;
const reLeadingSpaceTab = /^[ \t]+/;
const reMultiSpace = /\s+/g;
const reBlankLine = /^[ \t]*$/;
const reDoubleBlank = /\n[ \t]*\n[ \t]*$/;
const reBlockquoteStart = /^ {0,3}>/;
const reBlockquoteSetext = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const reBlockquoteMarker2 = /^ {0,3}>[ \t]?/gm;
const reBlockquoteMarkerWs = /^( {0,3}>)([ \t]+)/gm;
const reListNesting = /^ {1,4}(?=( {4})*[^ ])/g;
const reListIsTask = /^\[[ xX]\][ \t]+\S/;
const reListReplaceTask = /^\[[ xX]\][ \t]+/;
const reListTaskCheckbox = /\[[ xX]\]/;
const reAnyLine = /\n.*\n/;
const reHrefBrackets = /^<(.*)>$/;
const reTableDelim = /[:|]/;
const reTableAlignChars = /^\||\| *$/g;
const reTableRowBlank = /\n[ \t]*$/;
const reTableAlignRight = /^ *-+: *$/;
const reTableAlignCenter = /^ *:-+: *$/;
const reTableAlignLeft = /^ *:-+ *$/;
const reStartATag = /^<a /i;
const reEndATag = /^<\/a>/i;
const reStartPreTag = /^<(pre|code|kbd|script)(\s|>)/i;
const reEndPreTag = /^<\/(pre|code|kbd|script)(\s|>)/i;
const reStartAngle = /^</;
const reEndAngle = />$/;
const reUnicodeAlnum = /[\p{L}\p{N}]/u;
const reNumericRef = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const reNumericRefOrAmp = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const reEscapeTest = /[&<>"']/;
const reEscapeReplace = /[&<>"']/g;
const reEscapeTestNoEnc = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const reEscapeReplaceNoEnc = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const rePercentDecode = /%25/g;
const reFindPipe = /\|/g;
const reSplitPipe = / \|/;
const reSlashPipe = /\\\|/g;
const reCarriageReturn = /\r\n|\r/g;
const reSpaceLine = /^ +$/gm;
const reNotSpaceStart = /^\S*/;
const reEndingNewline = /\n$/;
const reOutputLinkReplace = /\\([\[\]])/g;
const reSetextLine = /^ {0,3}(?:=+|-+) *$/;
const reLeading3Spaces = /^ {0,3}/;

// ---------------------------------------------------------------------------
// Text helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

// Escape HTML entities. With encode, every & < > " ' is escaped; without it,
// an & that already starts a character reference is left alone.
function escapeHtml(text, encode) {
  if (encode) {
    if (reEscapeTest.test(text)) return text.replace(reEscapeReplace, (ch) => ESCAPE_MAP[ch]);
  } else if (reEscapeTestNoEnc.test(text)) {
    return text.replace(reEscapeReplaceNoEnc, (ch) => ESCAPE_MAP[ch]);
  }
  return text;
}

// Numeric character references name the character itself; zero, out of
// range and surrogate values become the replacement character. A decoded
// character must not join its neighbours into a new reference, so every &
// that is not already one is escaped here.
function decodeNumericRefs(text) {
  if (!reNumericRef.test(text)) return text;
  return text.replace(reNumericRefOrAmp, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(rePercentDecode, '%');
  } catch {
    return null;
  }
  return href;
}

// Split a table row on unescaped pipes; pad or trim to `count` cells.
function splitCells(tableRow, count) {
  const row = tableRow.replace(reFindPipe, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(reSplitPipe);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(reSlashPipe, '|');
  }
  return cells;
}

// Remove trailing `c` characters (equivalent to str.replace(/c*$/, '')).
function rtrim(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let suffLen = 0;
  while (suffLen < l) {
    const curr = str.charAt(l - suffLen - 1);
    if (curr === c && !invert) suffLen++;
    else if (curr !== c && invert) suffLen++;
    else break;
  }
  return str.slice(0, l - suffLen);
}

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && reBlankLine.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

// Normalise a link label so definitions and references match: trim, collapse
// inner whitespace to one space, Unicode case-fold via lower/upper/lower.
function normalizeLabel(label) {
  return label.trim().replace(reMultiSpace, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Find the closing bracket of a balanced pair in `str`, or -1 when there is
// none and -2 when more open than close. Backslash escapes skip a character.
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

// Expand tabs to the next multiple-of-4 column, starting at `indent`.
function expandTabs(line, indent = 0) {
  let col = indent;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const added = 4 - (col % 4);
      out += ' '.repeat(added);
      col += added;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

// Is `ch` (a one-character string) an ASCII punctuation character?
function isAsciiPunct(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64)
    || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
