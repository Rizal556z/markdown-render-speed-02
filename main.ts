// Driver for the markdown-render-speed-02 entry. The harness runs
// `node /bot/main.ts` (Node 22, type stripping only). It reads every case
// from /input/cases.json (or $MAKEFUN_INPUT_DIR), renders each case alone
// with parse() from ./parse.js, and writes the HTML strings in order to
// /output/html.json (or $MAKEFUN_OUTPUT_DIR). No caching across cases:
// parse() is called once per case, in order, and nothing is shared.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const out = new Array(cases.length);
for (let i = 0; i < cases.length; i++) out[i] = parse(cases[i].markdown);
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(out));
