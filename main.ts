// Driver for markdown-render-speed-02: reads every case from
// /input/cases.json (or $MAKEFUN_INPUT_DIR), renders each one alone with
// parse() from parse.js, and writes /output/html.json (or
// $MAKEFUN_OUTPUT_DIR) as a JSON array of the HTML strings in case order.
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const html = new Array(cases.length);
for (let i = 0; i < cases.length; i++) html[i] = parse(cases[i].markdown);
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
