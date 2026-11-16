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
const LHEADING_CORE = '^(?!BULLET |BLOCKCODE|FENCES|BLOCKQUOTE|HEADING|HTML|TABLE)'
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
const reDef = new RegExp('^ {0,3}\\[(' + BLOCK_LABEL + ')\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)'
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
const reListStart = new RegExp('^(' + BULLET + ')([ \\t][^\\n]*?)?(?:\\n|$)');
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
  s = subAll(s, '|TABLE', ''); // no table alternative inside a blockquote
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
  subAll('!?\\[(' + BOUNDED_INLINE_LABEL + ')\\]\\[(' + BOUNDED_BLOCK_LABEL + ')\\]', 'BRACKETS', INLINE_LABEL_BRACKETS)
  + '|!?\\[(' + BOUNDED_BLOCK_LABEL + ')\\](?:\\[\\])?(?!\\()', 'g');

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
  + '|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])');
const reBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Inline text (GFM): the run of plain text up to the next inline construct.
// Used directly by the inline loop's text step.
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

// ---------------------------------------------------------------------------
// Per-parse state (reset at the start of every parse() call)
// ---------------------------------------------------------------------------

let LINKS = null; // link reference definitions, keyed by normalised label
let QUEUE = null; // inline sources queued by block lexing: {src, html, pre}
let IN_LINK = false; // inside a link label or an <a> tag
let IN_RAW = false; // inside a <pre>/<code>/<kbd>/<script> raw block
let LINK_EMITTED = false; // a link was emitted while lexing the current label
let LINK_PAREN = true; // current inline source contains ')'
let TOP = true; // block lexer is at the top level

// Code-point length of a string (fast path when it has no astral chars).
const reAstral = /[\uD800-\uDBFF]/;
function cpLen(s) {
  return reAstral.test(s) ? [...s].length : s.length;
}

// UTF-16 length of the first code point of s (1, or 2 for astral).
function firstCpLen(s) {
  return s.codePointAt(0) > 0xFFFF ? 2 : 1;
}

// Last code point of s (1 or 2 UTF-16 units), or ''.
function lastCp(s) {
  if (!s) return '';
  const c = s.charCodeAt(s.length - 1);
  if (c >= 0xDC00 && c <= 0xDFFF && s.length >= 2) {
    const p = s.charCodeAt(s.length - 2);
    if (p >= 0xD800 && p <= 0xDBFF) return s.slice(-2);
  }
  return s.slice(-1);
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

// Fenced-code indent compensation: strip the fence's own indent from the
// body lines that carry at least that much leading space.
function fenceIndentComp(fenceRaw, body) {
  const m = fenceRaw.match(reIndentCodeComp);
  if (m === null) return body;
  const indent = m[1];
  return body.split('\n').map((line) => {
    const sp = line.match(reBeginningSpace);
    if (sp === null) return line;
    const [w] = sp;
    return line.slice(Math.min(w.length, indent.length));
  }).join('\n');
}

// ---------------------------------------------------------------------------
// Inline masking (marked's emStrongMask)
// ---------------------------------------------------------------------------

// Whether a bracketed span in `s` contains a link (used by the masking pass).
function linkInText(s) {
  if (!s.includes('[')) return false;
  for (const m of s.matchAll(reBlockSkip)) {
    if (reLink.test(m[0]) && s.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of s.matchAll(reReflinkSearch)) {
    const t = m[0], r = t.lastIndexOf('[');
    if (!(t.charAt(0) === '!' || !Object.hasOwn(LINKS, normalizeLabel(t.slice(r + 1, -1)))) &&
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
    const re = reReflinkSearch;
    const sub = (r) => {
      const o = r.lastIndexOf('[');
      if (!Object.hasOwn(LINKS, normalizeLabel(r.slice(o + 1, -1)))) return r;
      if (o > 1 && r.charAt(0) !== '!') {
        const inner = r.slice(1, o - 1);
        if (linkInText(inner)) return '[' + inner.replace(re, sub) + '][' + 'a'.repeat(r.length - o - 2) + ']';
      }
      return '[' + 'a'.repeat(r.length - 2) + ']';
    };
    t = t.replace(re, sub);
  }
  if (t.includes('`') || t.includes('\\')) {
    t = t.replace(reAnyPunctOutsideCode, (n, s, r) =>
      r ? '+'.repeat(n.length)
        : s ? s + n.slice(s.length, -s.length).replace(/`/g, '+') + s
        : n);
  }
  if (t.includes('[') || t.includes('`') || t.includes('<')) {
    t = t.replace(reBlockSkip, (n) => '[' + 'a'.repeat(n.length - 2) + ']');
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
      const m = reInlineCode.exec(label.slice(s));
      if (m) { s += m[0].length - 1; continue; }
    }
    if (label[s] !== '<') continue;
    const o = reInlineTagBuilt.exec(src.slice(off + s)) || reAutolink.exec(src.slice(off + s));
    if (o) {
      if (o[0].length > label.length - s) return true;
      s += o[0].length - 1;
    }
  }
  return false;
}

// Shared link/image creation (marked's link/image renderer): renders the
// label with inLink set, suppresses a non-image link whose label itself
// contains a link, and returns the HTML (or plain text in text mode).
function makeLink(m, href, title, raw, textMode) {
  const isImage = m[0].charAt(0) === '!';
  const label = m[1].replace(reOutputLinkReplace, '$1');
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
    const enc = cleanUrl(href);
    if (enc === null) return { html: escapeHtml(inner), len: raw.length };
    let o = `<img src="${escapeHtml(enc)}" alt="${escapeHtml(inner)}"`;
    if (title) o += ` title="${escapeHtml(title)}"`;
    return { html: o + '>', len: raw.length };
  }
  const enc = cleanUrl(href);
  if (enc === null) return { html: inner, len: raw.length };
  let o = `<a href="${escapeHtml(enc)}"`;
  if (title) o += ` title="${escapeHtml(title)}"`;
  return { html: o + '>' + inner + '</a>', len: raw.length };
}

// Inline link [label](href "title").
function tryLink(src, i, textMode) {
  if (!LINK_PAREN) return null;
  const m = reLink.exec(src.slice(i));
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(src.slice(i), m[1], off)) return null;
  const s = m[2].trim();
  if (reStartAngle.test(s)) {
    if (!reEndAngle.test(s)) return null;
    const stripped = rtrim(s.slice(0, -1), '\\');
    if ((s.length - stripped.length) % 2 === 0) return null;
  } else {
    const bal = findClosingBracket(m[2], '()');
    if (bal === -2) return null;
    if (bal > -1) {
      const h = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + bal;
      m[2] = m[2].substring(0, bal);
      m[0] = m[0].substring(0, h).trim();
      m[3] = '';
    }
  }
  const r = rtrim(m[0].slice(0, -1), '\\');
  if ((m[0].length - r.length) % 2 === 0) return null;
  let href = m[2].trim();
  if (reStartAngle.test(href)) href = href.slice(1, -1);
  const title = m[3] ? m[3].slice(1, -1) : '';
  return makeLink(m, href.replace(reAnyPunct, '$1'), title.replace(reAnyPunct, '$1'), m[0], textMode);
}

// Reference / shortcut link [label][ref] or [label].
function tryReflink(src, i, textMode) {
  let m = reReflink.exec(src.slice(i));
  if (!m) m = reNolink.exec(src.slice(i));
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(src.slice(i), m[1], off)) return null;
  const ref = LINKS[normalizeLabel(m[2] || m[1])];
  if (!ref) {
    const first = m[0].charAt(0);
    return { html: textMode ? first : escapeHtml(first), len: 1 };
  }
  return makeLink(m, ref.href, ref.title, m[0], textMode);
}

// <scheme:...> and <email> autolinks.
function autolinkOut(m, textMode) {
  let text, href;
  if (m[2] === '@') { text = m[1]; href = 'mailto:' + text; }
  else { text = m[1]; href = text; }
  if (textMode) return text;
  const enc = cleanUrl(href);
  if (enc === null) return escapeHtml(text, true);
  return '<a href="' + escapeHtml(enc, true) + '">' + escapeHtml(text, true) + '</a>';
}

// Extended autolinks: www., http(s)://, ftp://, bare emails, mailto:/xmpp:.
function tryUrl(src, i, textMode) {
  const m = reUrl.exec(src.slice(i));
  if (!m) return null;
  let text, href;
  if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + text;
  } else {
    let t0 = m[0], prev;
    do {
      prev = t0;
      const b = reBackpedal.exec(t0);
      t0 = b ? b[0] : '';
    } while (prev !== t0);
    text = t0;
    href = m[1] === 'www.' ? 'http://' + t0 : t0;
  }
  if (textMode) return { html: text, len: text.length };
  const enc = cleanUrl(href);
  if (enc === null) return { html: escapeHtml(text, true), len: text.length };
  return { html: '<a href="' + escapeHtml(enc, true) + '">' + escapeHtml(text, true) + '</a>', len: text.length };
}

// Emphasis / strong emphasis (marked's emStrong), searching the masked
// source for a closer run.
function tryEmStrong(src, i, masked, closers, textMode, prevChar) {
  const m = reEmLDelim.exec(src.slice(i));
  if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return null;
  const delim = m[0][0];
  const openLeft = prevChar === delim;
  const pos = i;
  let l = pos;
  while (l > 0 && masked[l - 1] === delim) l--;
  const p = lastCp(masked.slice(Math.max(0, l - 2), l));
  const h = p === '*' || p === '_' || !!rePunctTest.exec(p);
  let n = prevChar;
  if (l < pos) n = p;
  const u = l < pos ? h : !!rePunctTest.exec(n);
  if (m[4] && reUnicodeAlnum.test(n)) return null;
  const d = m[1] || m[3] || '';
  if (!d || !n || u) {
    const k = cpLen(m[0]) - 1;
    const y = pos - l + k;
    const R = !!p.trim() && (!!d || (delim === '*' && !h));
    if (delim !== '*' && delim !== '_') return null;
    const A = delim === '*' ? reEmRDelimAst : reEmRDelimUnd;
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
      const b = g.length;
      if (s2[3] || s2[4]) { mm += b; continue; }
      if (s2[5] || s2[6] || R) {
        if (openLeft && (s2[5] || s2[6])) break;
        if (y % 3 && !((y + b) % 3)) { f += b; continue; }
      }
      mm -= b;
      if (mm > 0) continue;
      const bb = Math.min(b, b + mm + f);
      const te = firstCpLen(s2[0]);
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
  const m = reDelLDelim.exec(src.slice(i));
  if (!m) return null;
  if (!((m[1] || '') === '' || !prevChar || rePunctTest.exec(prevChar))) return null;
  const o = cpLen(m[0]) - 1;
  const pos = i;
  const u = closers.del;
  const d = pos + o;
  if (u < d) return null;
  const sub = masked.slice(pos + o);
  const kk = u - d;
  if (sub.indexOf('~') === -1) return null;
  let p = o, s2;
  reDelRDelim.lastIndex = 0;
  while ((s2 = reDelRDelim.exec(sub)) !== null && !(s2.index > kk)) {
    const g = s2[1] || s2[2] || s2[3] || s2[4] || s2[5] || s2[6];
    if (!g) continue;
    const l = g.length;
    if (l !== o) continue;
    if (s2[3] || s2[4]) { p += l; continue; }
    p -= l;
    if (p > 0) continue;
    const ll = Math.min(l, l + p);
    const te = firstCpLen(s2[0]);
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
      const m = reInlineEscape.exec(rest);
      if (m) {
        out += textMode ? m[1] : escapeHtml(m[1]);
        i += m[0].length;
        continue;
      }
      const b = reBr.exec(rest);
      if (b) {
        if (!textMode) out += '<br>';
        i += b[0].length;
        continue;
      }
    } else if (ch === '<') {
      const m = reInlineTagBuilt.exec(rest);
      if (m) {
        const tag = m[0];
        if (!IN_LINK && reStartATag.test(tag)) IN_LINK = true;
        else if (IN_LINK && reEndATag.test(tag)) IN_LINK = false;
        if (!IN_RAW && reStartPreTag.test(tag)) IN_RAW = true;
        else if (IN_RAW && reEndPreTag.test(tag)) IN_RAW = false;
        out += tag;
        i += tag.length;
        continue;
      }
      const a = reAutolink.exec(rest);
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
      const c = reInlineCode.exec(rest);
      if (c) {
        let text = c[2].replace(reNewlineGlobal, ' ');
        if (reNonSpace.test(text) && reStartingSpace.test(text) && reEndingSpace.test(text)) {
          text = text.substring(1, text.length - 1);
        }
        out += textMode ? text : '<code>' + escapeHtml(text, true) + '</code>';
        i += c[0].length;
        continue;
      }
    } else if (ch === ' ') {
      const b = reBr.exec(rest);
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
    const m = reInlineText.exec(rest);
    if (!m) throw new Error('Infinite loop on byte: ' + src.charCodeAt(i));
    const raw = m[0];
    const text = IN_RAW ? raw : decodeNumericRefs(raw);
    out += textMode ? text : IN_RAW ? text : escapeHtml(text);
    prevTextEnd = raw.slice(-1) !== '_' ? raw.slice(-1) : '';
    wasText = true;
    i += raw.length;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Block lexer
// ---------------------------------------------------------------------------

// Queue an inline source for rendering after block lexing (link
// definitions may appear after their uses).
function queueInline(src) {
  const q = { src, html: '', pre: '' };
  QUEUE.push(q);
  return q;
}

// Blockquote token, or null. Port of marked's blockquote tokenizer.
function blockquoteTok(src) {
  const m = reBlockquote.exec(src);
  if (!m) return null;
  let lines = rtrim(m[0], '\n').split('\n');
  let raw = '', text = '';
  const toks = [];
  while (lines.length > 0) {
    let seenMarker = false;
    const chunk = [];
    let p;
    for (p = 0; p < lines.length; p++) {
      if (reBlockquoteStart.test(lines[p])) { chunk.push(lines[p]); seenMarker = true; }
      else if (!seenMarker) chunk.push(lines[p]);
      else break;
    }
    lines = lines.slice(p);
    const h = chunk.join('\n');
    const u = h
      .replace(reBlockquoteMarkerWs, (g, b, mm) => b + expandTabs(mm, b.length))
      .replace(reBlockquoteSetext, '\n    $1')
      .replace(reBlockquoteMarker2, '');
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
      const joined = k.raw + '\n' + rest.replace(reBlockquoteMarker2, '');
      const f = blockquoteTok(joined);
      toks[toks.length - 1] = f;
      const y = joined.substring(f.raw.length).replace(/^\n/, '');
      const r2 = y ? y.split('\n').length : 0;
      const extra = r2 ? lines.slice(0, -r2) : lines;
      if (extra.length > 0) raw = raw + '\n' + extra.join('\n');
      text = text.substring(0, text.length - k.text.length) + f.text;
      lines = lines.slice(extra.length);
      if (lines.length > 0 && reBlockquoteStart.test(lines[0])) continue;
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
  const first = reListStart.exec(src);
  if (!first) return null;
  let e = src;
  const n0 = e;
  const consumed = () => n0.length - e.length;
  let bullet = first[1].trim();
  const ordered = bullet.length > 1;
  const list = { t: 'list', raw: '', ordered, start: ordered ? +bullet.slice(0, -1) : '', loose: false, items: [] };
  bullet = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = listItemRegex(bullet);
  let prevDoubleBlank = false;
  while (e) {
    let emptyItem = false, d = '';
    const t = itemRe.exec(e);
    if (!t || reHr.test(e)) break;
    const k = consumed();
    e = e.substring(t[0].length);
    const g = t[2].split('\n', 1)[0];
    const b = t[1].length;
    const mm = g.replace(reLeadingSpaceTab, (v) => expandTabs(v, b));
    let f = e.split('\n', 1)[0];
    const y = !mm.trim();
    let R = 0;
    if (y) R = b + 1;
    else {
      R = mm.search(reNonSpace);
      if (R > 4) R = 1;
      d = mm.slice(R);
      R += b;
    }
    if (y && reBlankLine.test(f)) {
      e = e.substring(f.length + 1);
      emptyItem = true;
    }
    if (!emptyItem) {
      const ind = indentRegexes(R);
      const vRe = ind.nextBullet, qRe = ind.hr, eeRe = ind.fences,
        teRe = ind.heading, mRe = ind.html, neRe = ind.blockquote;
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
        const Z = U.replace(reLeadingSpaceTab, (v) => expandTabs(v));
        let zns = 0;
        while (zns < Z.length && Z.charCodeAt(zns) === 32) zns++;
        const fBlank = !U.trim();
        if (zns >= R || fBlank) {
          d += '\n' + Z.slice(R);
        } else {
          if (yFlag || firstNonSpaceCol(mLine) >= 4 || startsBlock(mLine, true)) break;
          const qe = reSetextLine.test(U) && reLheading.test(`${mLine}\n${U}`)
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
      else if (reDoubleBlank.test(itemRaw)) prevDoubleBlank = true;
    }
    list.items.push({ t: 'list_item', raw: itemRaw, task: reListIsTask.test(d), loose: false, text: d, toks: [] });
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
      if (spaces.length > 0 && spaces.some((g) => reAnyLine.test(g.raw))) list.loose = true;
    }
  }
  for (const item of list.items) {
    const firstTok = item.toks[0];
    if (item.task && firstTok && (firstTok.t === 'text' || firstTok.t === 'paragraph')) {
      item.text = item.text.replace(reListReplaceTask, '');
      firstTok.raw = firstTok.raw.replace(reListReplaceTask, '');
      firstTok.text = firstTok.text.replace(reListReplaceTask, '');
      for (let g = QUEUE.length - 1; g >= 0; g--) {
        if (reListIsTask.test(QUEUE[g].src)) {
          QUEUE[g].src = QUEUE[g].src.replace(reListReplaceTask, '');
          break;
        }
      }
      const ck = reListTaskCheckbox.exec(item.raw);
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
// A line that is a single `<...>` tag ending at EOL: the narrow HTML
// lookahead marked's setext-heading regex uses (unlike the paragraph
// regex's broad HTML lookahead above). Such a line kills a setext heading
// AND interrupts a paragraph; a broad-HTML line that is not narrow (e.g.
// `<!-- c --> <div>`) interrupts the paragraph but a setext heading may
// still span it, so the paragraph break is deferred until the heading
// question is settled.
const P_HTML_NARROW = /^ {0,3}<[^>]+>$/;

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
  if (l1 !== null && P_TABLE_DELIM.test(l1) && reTableDelim.test(l1)) {
    const m = reTable.exec(src);
    if (m) {
      const headerCells = splitCells(m[1]);
      const aligns = m[2].replace(reTableAlignChars, '').split('|');
      if (headerCells.length === aligns.length) {
        const rowsRaw = m[3] && m[3].trim() ? m[3].replace(reTableRowBlank, '').split('\n') : [];
        const raw = rtrim(m[0], '\n');
        const align = aligns.map((a) =>
          reTableAlignRight.test(a) ? 'right'
            : reTableAlignCenter.test(a) ? 'center'
            : reTableAlignLeft.test(a) ? 'left' : null);
        const header = headerCells.map((c, idx) => ({ text: c, align: align[idx], q: queueInline(c) }));
        const rows = rowsRaw.map((r) =>
          splitCells(r, header.length).map((c, idx) => ({ text: c, align: align[idx], q: queueInline(c) })));
        return { tok: { t: 'table', raw, header, align, rows }, len: raw.length };
      }
    }
    // Table regex failed or header/align lengths differ: the paragraph
    // still stops before line 1 (the table lookahead matched), so fall
    // into the paragraph scan below.
  }
  let end = 1;
  // If >= 0, the paragraph already broke before this line (broad-HTML
  // line that is not a narrow HTML line); the scan continues only to
  // settle whether a setext heading spans that line.
  let paraEnd = -1;
  for (let i = 1; ; i++) {
    const ln = line(i);
    // A whitespace-only line ends the paragraph only when a newline
    // follows it; at end of input it is a paragraph line (cm-241).
    if (ln === null || (P_BLANK.test(ln) && hasNl[i])) break;
    if (P_SETEXT.test(ln)) {
      const m = reLheading.exec(src);
      if (m) {
        const text = m[1].trim();
        const raw = rtrim(m[0], '\n');
        return { tok: { t: 'heading', raw, depth: m[2].charAt(0) === '=' ? 1 : 2, text, q: queueInline(text) }, len: raw.length };
      }
      // Not a setext heading: the underline is an ordinary line — except
      // that `---` is also a thematic break, which still interrupts the
      // paragraph (marked's lheading regex refuses lines that look like an
      // HTML block start, e.g. `<http://x>` followed by `---`).
      // Fall through to the interrupt tests below.
    }
    if (reHr.test(ln) || P_INT_HEADING.test(ln) || P_INT_BQ.test(ln) || P_INT_FENCE.test(ln) ||
        P_INT_LIST.test(ln)) break;
    if (indentRegexes(4).html.test(ln)) {
      if (P_HTML_NARROW.test(ln)) break;
      if (paraEnd < 0) paraEnd = i;
      end = i + 1;
      continue;
    }
    const nx = line(i + 1);
    if (nx !== null && P_TABLE_HEADER.test(ln) && P_TABLE_DELIM.test(nx)) {
      // A table interrupts the paragraph — unless the delimiter line is
      // itself a setext underline, in which case the whole block is a
      // setext heading (cm-095).
      if (P_SETEXT.test(nx)) {
        const m = reLheading.exec(src);
        if (m) {
          const text = m[1].trim();
          const raw = rtrim(m[0], '\n');
          return { tok: { t: 'heading', raw, depth: m[2].charAt(0) === '=' ? 1 : 2, text, q: queueInline(text) }, len: raw.length };
        }
      }
      break;
    }
    end = i + 1;
  }
  if (!top) return null;
  const pe = paraEnd >= 0 ? paraEnd : end;
  const text = lines.slice(0, pe).join('\n');
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
    m = reNewline.exec(src);
    if (m && m[0].length > 0) {
      src = src.substring(m[0].length);
      const prev = toks.at(-1);
      if (m[0].length === 1 && prev !== undefined) prev.raw += '\n';
      else toks.push({ t: 'space', raw: m[0] });
      continue;
    }
    // indented code
    m = reBlockCode.exec(src);
    if (m) {
      const raw = trimTrailingBlankLines(m[0]);
      const text = raw.replace(reCodeRemoveIndent, '');
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
    m = reFences.exec(src);
    if (m) {
      const lang = m[2] ? m[2].trim().replace(reAnyPunct, '$1') : m[2];
      const text = fenceIndentComp(m[0], m[3] || '');
      src = src.substring(m[0].length);
      toks.push({ t: 'code', raw: m[0], text, lang });
      continue;
    }
    // ATX heading
    m = reHeading.exec(src);
    if (m) {
      let text = m[2].trim();
      if (reEndingHash.test(text)) {
        const stripped = rtrim(text, '#');
        if (!stripped || reEndingSpaceTab.test(stripped)) text = stripped.trim();
      }
      const raw = rtrim(m[0], '\n');
      src = src.substring(raw.length);
      toks.push({ t: 'heading', raw, depth: m[1].length, text, q: queueInline(text) });
      continue;
    }
    // thematic break
    m = reHr.exec(src);
    if (m) {
      const raw = rtrim(m[0], '\n');
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
    m = reHtmlBuilt.exec(src);
    if (m) {
      const raw = trimTrailingBlankLines(m[0]);
      src = src.substring(raw.length);
      toks.push({ t: 'html', raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text: raw });
      continue;
    }
    // link reference definition
    m = reDef.exec(src);
    if (m) {
      if (reStartAngle.test(m[2]) || findClosingBracket(m[2], '()') === -1) {
        const tag = normalizeLabel(m[1]);
        const href = m[2] ? m[2].replace(reHrefBrackets, '$1').replace(reAnyPunct, '$1') : '';
        const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(reAnyPunct, '$1') : m[3];
        const raw = rtrim(m[0], '\n');
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
    m = reBlockText.exec(src);
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

// ---------------------------------------------------------------------------
// Block renderer (same HTML as marked's Renderer)
// ---------------------------------------------------------------------------

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
        const lang = (tk.lang || '').match(reNotSpaceStart)?.[0];
        const text = tk.text ? tk.text.replace(reEndingNewline, '') + '\n' : '';
        const body = escapeHtml(text, true);
        out += lang
          ? `<pre><code class="language-${escapeHtml(lang)}">${body}</code></pre>\n`
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

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

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
  const src = markdown.replace(reCarriageReturn, '\n');
  const toks = lexBlocks(src, [], false);
  for (const q of QUEUE) {
    IN_RAW = false;
    q.html = (q.pre || '') + renderInline(q.src, false);
  }
  return renderBlocks(toks);
}
