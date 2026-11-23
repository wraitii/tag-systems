"use strict";

// Static SVG figures for the walkthrough. Colours come from CSS classes so both themes work.
(() => {
  const NS = "http://www.w3.org/2000/svg";

  function svg(tag, attrs = {}, text) {
    const node = document.createElementNS(NS, tag);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, value);
    if (text !== undefined) node.textContent = text;
    return node;
  }

  // "s_0" → s with a subscript 0.
  function label(parent, x, y, value, attrs = {}) {
    const node = svg("text", { x, y, ...attrs });
    const [base, sub] = value.split("_");
    node.append(base);
    if (sub !== undefined) node.append(svg("tspan", { class: "d-sub", dy: 3 }, sub));
    parent.append(node);
    return node;
  }

  function root(width, height, title) {
    const node = svg("svg", { viewBox: `0 0 ${width} ${height}`, role: "img", class: "diagram", style: `--natural-width: ${width}px` });
    node.append(svg("title", {}, title));
    return node;
  }

  function laneChip(parent, x, y, lane) {
    parent.append(svg("rect", { x: x - 8, y: y - 8, width: 16, height: 16, rx: 2, class: `d-lane-fill-${lane}` }));
    parent.append(svg("text", { x, y: y + 4, class: "d-chip-text" }, String(lane)));
  }

  /* ---------- Figure 1: even vs odd queue, and where the next sweep starts ---------- */

  function parity() {
    const cell = 30, gap = 3, left = 92, rowHeight = 86;
    const rows = [
      { title: "Even length", queue: ["s_0", "s_1", "s_2", "s_3"], cut: 0 },
      { title: "Odd length", queue: ["s_0", "s_1", "s_2"], cut: 1 },
    ];
    const appended = 5;
    const width = left + (4 + appended) * (cell + gap) + 24;
    const figure = root(width, rows.length * rowHeight + 2,
      "An even-length queue is read at s0 and s2 and the next sweep starts at the first appended symbol, lane 0. " +
      "An odd-length queue's last pair takes the first appended symbol with it, so the next sweep starts one symbol in, lane 1.");

    rows.forEach(({ title, queue, cut }, r) => {
      const top = r * rowHeight + 26;
      const g = svg("g");
      figure.append(g);
      label(g, 0, top + 20, title, { class: "d-row-title" });
      const x = i => left + i * (cell + gap);
      const symbols = [...queue, ...Array.from({ length: appended }, (_, i) => `o_${i}`)];
      const appendStart = queue.length;

      // Separator between the queue and what this sweep appends.
      const sepX = x(appendStart) - gap / 2 - .5;
      g.append(svg("line", { x1: sepX, x2: sepX, y1: top - 14, y2: top + cell + 6, class: "d-sep" }));
      if (r === 0) {
        label(g, x(0), top - 18, "queue at sweep start", { class: "d-note" });
        label(g, x(appendStart), top - 18, "appended this sweep", { class: "d-note" });
      }

      symbols.forEach((name, i) => {
        const isQueue = i < appendStart;
        const read = isQueue && i % 2 === 0;
        const eaten = !isQueue && i < cut + appendStart;
        const next = i === appendStart + cut;
        const cls = read ? "d-cell d-cell-read" : isQueue ? "d-cell" : eaten ? "d-cell d-cell-eaten" : "d-cell d-cell-out";
        g.append(svg("rect", { x: x(i), y: top, width: cell, height: cell, rx: 2, class: cls }));
        label(g, x(i) + cell / 2, top + 20, name, { class: read ? "d-cell-text d-cell-text-read" : "d-cell-text" });
        if (eaten) g.append(svg("line", { x1: x(i) + 4, y1: top + cell - 4, x2: x(i) + cell - 4, y2: top + 4, class: "d-strike" }));
        if (next) {
          const cx = x(i) + cell / 2;
          g.append(svg("path", { d: `M${cx} ${top + cell + 26} L${cx} ${top + cell + 6}`, class: `d-arrow d-lane-stroke-${cut}`, "marker-end": `url(#d-head-${cut})` }));
          laneChip(g, cx + 20, top + cell + 22, cut);
          label(g, cx + 34, top + cell + 26, "next sweep starts here", { class: "d-note" });
        }
      });

      // Deleted pairs: bracket every two symbols from the start of the queue.
      for (let i = 0; i < queue.length; i += 2) {
        const x1 = x(i) + 2, x2 = x(i + 1) + cell - 2, y = top + cell + 5;
        g.append(svg("path", { d: `M${x1} ${y - 3} V${y} H${x2} V${y - 3}`, class: "d-bracket" }));
      }
    });

    figure.prepend(markers());
    return figure;
  }

  function markers() {
    const defs = svg("defs");
    for (const lane of [0, 1]) {
      const marker = svg("marker", { id: `d-head-${lane}`, viewBox: "0 0 8 8", refX: 6, refY: 4, markerWidth: 7, markerHeight: 7, orient: "auto" });
      marker.append(svg("path", { d: "M0 0 L8 4 L0 8 z", class: `d-lane-fill-${lane}` }));
      defs.append(marker);
    }
    return defs;
  }

  /* ---------- Lane traces: the control lane flowing through clocks and counters ---------- */

  // blocks: [{ name, kind: "clock" | "counter" }]
  // rows:   [{ title, lane, steps: [{ flip, sign?, note? }] }]  (one step per block)
  function laneTrace({ blocks, rows, title }) {
    const left = 110, clockWidth = 58, counterWidth = 128, rowHeight = 78, head = 30, exitWidth = 44;
    const widths = blocks.map(b => (b.kind === "clock" ? clockWidth : counterWidth));
    const starts = widths.reduce((acc, w, i) => [...acc, acc[i] + w], [left]);
    const width = starts.at(-1) + exitWidth;
    const height = head + rows.length * rowHeight;
    const figure = root(width, height, title);

    // Column bands and headers.
    blocks.forEach((block, i) => {
      figure.append(svg("rect", { x: starts[i] + 2, y: 0, width: widths[i] - 4, height, rx: 2, class: `d-band d-band-${block.kind}` }));
      label(figure, starts[i] + widths[i] / 2, 18, block.name, { class: `d-col d-col-${block.kind}` });
    });

    rows.forEach((row, r) => {
      const top = head + r * rowHeight;
      const laneY = lane => top + 18 + lane * 26;
      const g = svg("g");
      figure.append(g);
      if (r > 0) g.append(svg("line", { x1: 0, x2: width, y1: top, y2: top, class: "d-row-rule" }));
      const [main, sub] = row.title.split(" · ");
      label(g, 0, laneY(0) + 4, main, { class: "d-row-title" });
      if (sub) label(g, 0, laneY(0) + 20, sub, { class: "d-note" });
      for (const lane of [0, 1]) g.append(svg("line", { x1: left - 24, x2: width - 10, y1: laneY(lane), y2: laneY(lane), class: "d-guide" }));
      for (const lane of [0, 1]) label(g, left - 28, laneY(lane) + 3.5, String(lane), { class: "d-guide-label" });

      let lane = row.lane;
      const entry = lane;
      row.steps.forEach((step, i) => {
        const x0 = starts[i], x1 = starts[i + 1], mid = (x0 + x1) / 2;
        const out = step.flip ? 1 - lane : lane;
        if (step.flip) {
          const a = mid - 12, b = mid + 12;
          g.append(svg("path", { d: `M${x0} ${laneY(lane)} H${a}`, class: `d-wire d-lane-stroke-${lane}` }));
          g.append(svg("path", { d: `M${a} ${laneY(lane)} L${b} ${laneY(out)}`, class: "d-wire d-wire-flip" }));
          g.append(svg("path", { d: `M${b} ${laneY(out)} H${x1}`, class: `d-wire d-lane-stroke-${out}` }));
        } else {
          g.append(svg("path", { d: `M${x0} ${laneY(lane)} H${x1}`, class: `d-wire d-lane-stroke-${lane}` }));
        }
        if (step.sign) {
          const y = laneY(lane);
          const cls = step.inverted ? "d-sign d-sign-inverted" : `d-sign d-lane-stroke-${lane}`;
          const cx = step.flip ? mid - 30 : mid;
          g.append(svg("rect", { x: cx - 10, y: y - 10, width: 20, height: 20, rx: 2, class: cls }));
          g.append(svg("text", { x: cx, y: y + 5, class: step.inverted ? "d-sign-text d-sign-text-inverted" : "d-sign-text" }, step.sign));
        }
        if (step.underflow || step.note) {
          // Underflow tag (same look as the guard table) followed by the note, centred under the column.
          const y = laneY(1) + 22, tagWidth = 50, spacing = 5;
          const noteWidth = step.note ? step.note.length * 5.2 : 0;
          const total = (step.underflow ? tagWidth + (step.note ? spacing : 0) : 0) + noteWidth;
          let x = mid - total / 2;
          if (step.underflow) {
            g.append(svg("rect", { x, y: y - 9.5, width: tagWidth, height: 13, rx: 2, class: "d-flag" }));
            g.append(svg("text", { x: x + tagWidth / 2, y: y, class: "d-flag-text" }, "underflow"));
            x += tagWidth + spacing;
          }
          if (step.note) {
            const anchor = step.underflow ? { x, "text-anchor": "start" } : { x: mid, "text-anchor": "middle" };
            label(g, anchor.x, y, step.note, { class: "d-step-note", "text-anchor": anchor["text-anchor"] });
          }
        }
        lane = out;
      });
      g.append(svg("path", { d: `M${left - 10} ${laneY(entry)} H${left}`, class: `d-wire d-lane-stroke-${entry}` }));
      laneChip(g, left - 12, laneY(entry), entry);
      laneChip(g, width - exitWidth + 24, laneY(lane), lane);
    });

    return figure;
  }

  const COLUMNS = [
    { name: "C_0", kind: "clock" },
    { name: "X", kind: "counter" },
    { name: "C_1", kind: "clock" },
    { name: "Y", kind: "counter" },
    { name: "C_2", kind: "clock" },
  ];

  const FIGURES = {
    parity,

    commands: () => laneTrace({
      title: "Two commands. Command 1: C0 flips to lane 1 so X decrements, C1 flips back so Y increments, C2 keeps lane 0. " +
        "Command 2: C0 keeps lane 0 so X increments, C1 flips so Y decrements, C2 flips back to end on lane 0.",
      blocks: COLUMNS,
      rows: [
        { title: "Cmd 1 · sweep 1", lane: 0, steps: [{ flip: true }, { sign: "−" }, { flip: true }, { sign: "+" }, {}] },
        { title: "Cmd 2 · sweep 1", lane: 0, steps: [{}, { sign: "+" }, { flip: true }, { sign: "−" }, { flip: true }] },
      ],
    }),

    probe: () => laneTrace({
      title: "The probe with X at E = 0. Command 1 sweep 2: X's singleton b flips the lane, leaving a carry of 1. " +
        "Command 2 sweep 1 starts on lane 1, so every sign is inverted: X gets minus, Y gets plus. " +
        "Command 2 sweep 2: C0 puts X back on lane 0, X flips again, and the carry is cancelled.",
      blocks: COLUMNS,
      rows: [
        { title: "Cmd 1 · sweep 1", lane: 0, steps: [{ flip: true }, { sign: "−", underflow: true, note: "W¹ → b¹" }, { flip: true }, { sign: "+" }, {}] },
        { title: "Cmd 1 · sweep 2", lane: 0, steps: [{}, { flip: true, note: "lone b flips lane" }, {}, { note: "even run, no effect" }, {}] },
        { title: "Cmd 2 · sweep 1", lane: 1, steps: [{}, { sign: "−", inverted: true, underflow: true, note: "b¹" }, { flip: true }, { sign: "+", inverted: true }, { flip: true }] },
        { title: "Cmd 2 · sweep 2", lane: 1, steps: [{ flip: true }, { flip: true, note: "lone b flips lane" }, { flip: true }, { note: "even run" }, {}] },
      ],
    }),
  };

  for (const figure of document.querySelectorAll("[data-diagram]")) {
    const make = FIGURES[figure.dataset.diagram];
    if (make) figure.prepend(make());
  }
})();
