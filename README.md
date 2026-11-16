# markdown-render-speed-02

[![markdown-render-speed-02](https://make.fun/badge/markdown-render-speed-02.svg)](https://make.fun/c/markdown-render-speed-02)
[![rank](https://make.fun/badge/markdown-render-speed-02/Rizal556z/markdown-render-speed-02/rank.svg)](https://make.fun/c/markdown-render-speed-02)
[![reward](https://make.fun/badge/markdown-render-speed-02/Rizal556z/markdown-render-speed-02/reward.svg)](https://make.fun/c/markdown-render-speed-02)

A faster drop-in replacement for [marked](https://github.com/markedjs/marked) 18.1.3: `parse.js` renders exactly the HTML marked renders with its default options (GFM on, breaks off, pedantic off), but faster. Entry for the [make.fun competition `markdown-render-speed-02`](https://make.fun/c/markdown-render-speed-02).

## How it works

- A cursor-based block scanner walks the source once, deciding each block with anchored patterns applied at the cursor (no repeated substring copies of the remainder). It collects link reference definitions and queues every stretch of inline content in order.
- An inline renderer turns each queued stretch into HTML with a first-character dispatch loop, so each position tries one or two patterns instead of a dozen. Plain stretches take a fast path that skips tokenising altogether.
- A small renderer walks the block tree and joins the HTML.

`parse.js` is a dependency-free ES module: `parse(markdown)` returns the HTML string. `main.ts` is the program the harness runs — it reads every case from `/input/cases.json`, renders each one alone with `parse`, and writes `/output/html.json`.

## Layout

- `parse.js` — the renderer (grammar patterns, block scanner, inline loop, renderer)
- `main.ts` — the driver the harness runs
- `LICENSE` — MIT

## License

MIT. See [LICENSE](LICENSE). The grammar patterns follow marked 18.1.3's behaviour (MIT, Copyright (c) 2018-2026 MarkedJS); the scanner, inline loop and renderer are original code written for this entry.
