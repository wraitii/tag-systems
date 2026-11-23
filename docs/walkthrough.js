"use strict";

(() => {
  const tabs = [
    { id: "playground", tab: document.getElementById("tab-playground"), panel: document.getElementById("panel-playground") },
    { id: "walkthrough", tab: document.getElementById("tab-walkthrough"), panel: document.getElementById("panel-walkthrough") },
  ];

  function selectTab(id, updateHash = true) {
    for (const item of tabs) {
      const selected = item.id === id;
      item.tab.setAttribute("aria-selected", String(selected));
      item.tab.tabIndex = selected ? 0 : -1;
      item.panel.hidden = !selected;
    }
    if (updateHash) {
      const hash = id === "walkthrough" ? "#how-it-works" : "#playground";
      if (location.hash !== hash) history.replaceState(null, "", hash);
    }
  }

  tabs.forEach((item, index) => {
    item.tab.addEventListener("click", () => selectTab(item.id));
    item.tab.addEventListener("keydown", event => {
      if (event.key !== "ArrowLeft" && event.key !== "ArrowRight") return;
      event.preventDefault();
      const next = tabs[(index + (event.key === "ArrowRight" ? 1 : tabs.length - 1)) % tabs.length];
      selectTab(next.id);
      next.tab.focus();
    });
  });

  if (location.hash === "#how-it-works") selectTab("walkthrough", false);

  for (const button of document.querySelectorAll("[data-open-preset]")) {
    button.addEventListener("click", () => {
      const name = button.getAttribute("data-open-preset");
      selectTab("playground");
      if (window.openPresetInPlayground) window.openPresetInPlayground(name);
      window.scrollTo({ top: 0, behavior: "smooth" });
    });
  }

  // Interactive 12-command Guard walkthrough: if X == 0: Y += 1 (leaving Z unchanged).
  // Mirrors guarded(0, [0, 1, 0]) in machine.js and Table 1 in paper/six-symbol-tag.tex.
  const COMMANDS = [
    // Commands 1-4: remove bias
    { cmd: 1, stage: 0, signs: [-1, +1, +1], p2Test: 0 },
    { cmd: 2, stage: 0, signs: [-1, -1, -1], p2Test: 0 },
    { cmd: 3, stage: 0, signs: [-1, +1, +1], p2Test: 0 },
    { cmd: 4, stage: 0, signs: [-1, -1, -1], p2Test: 0 },
    // Commands 5-6: first probe
    { cmd: 5, stage: 1, signs: [-1, +1, +1], p2Test: 0 },
    { cmd: 6, stage: 1, signs: [+1, -1, -1], p2Test: 1 },
    // Commands 7-8: second probe
    { cmd: 7, stage: 2, signs: [-1, +1, -1], p2Test: 0 },
    { cmd: 8, stage: 2, signs: [+1, -1, +1], p2Test: 1 },
    // Commands 9-12: restore bias
    { cmd: 9, stage: 3, signs: [+1, +1, +1], p2Test: 0 },
    { cmd: 10, stage: 3, signs: [+1, -1, -1], p2Test: 0 },
    { cmd: 11, stage: 3, signs: [+1, +1, +1], p2Test: 0 },
    { cmd: 12, stage: 3, signs: [+1, -1, -1], p2Test: 0 },
  ];

  const STAGES = [
    {
      title: "1–4 · Remove bias",
      summary: xZero => xZero
        ? "Commands 1–4 strip the +4 safety bias from X (E: 4 → 0) so it sits right on the edge of underflow. Y and Z oscillate (+ − + −) and finish unchanged."
        : "Commands 1–4 strip the +4 safety bias from X (E: 8 → 4). Because X > 0, it still has 4 exponent units of room and will not underflow during the probes.",
    },
    {
      title: "5–6 · First probe",
      summary: xZero => xZero
        ? "Command 5 decrements X at E = 0 and underflows. Its singleton b flips cut → 1 for command 6, inverting every programmed sign. In command 6, X underflows again and cancels cut → 0. Both Y and Z move +2."
        : "Command 5 decrements X from E = 4 to 3 (no underflow, cut stays 0). Command 6 runs unflipped and cancels every change from command 5.",
    },
    {
      title: "7–8 · Second probe",
      summary: xZero => xZero
        ? "Same underflow trick, but Z swaps its sign pair so it moves −2, cancelling its +2 from the first probe (net 0). Meanwhile Y gains another +2 (total +4 = +1 logical)."
        : "Again X stays above 0 (E: 4 → 3 → 4), cut stays 0, and both Y and Z cancel back to E = 4.",
    },
    {
      title: "9–12 · Restore bias",
      summary: xZero => xZero
        ? "Commands 9–12 unconditionally add +4 back to X (E: 0 → 4, logical v = 0) while Y and Z oscillate cleanly. Final logical values: X = 0, Y = 1, Z = 0, cut = 0."
        : "Commands 9–12 restore X’s +4 bias (E: 4 → 8, logical v = 1). Final logical values are completely unchanged: X = 1, Y = 0, Z = 0, cut = 0.",
    },
  ];

  let xZero = true;
  let stageIndex = 0;

  function simulateGuard(isZero) {
    // Exponents: X (v=0 or 1), Y (v=0, Y += 1), Z (v=0, unchanged)
    const exp = [isZero ? 4 : 8, 4, 4];
    let cut = 0;
    return COMMANDS.map(entry => {
      const cutIn = cut;
      const effective = entry.signs.map(s => (cutIn ? -s : s));
      let underflow = false;
      const before = exp.slice();
      for (let i = 0; i < exp.length; i++) {
        if (i === 0 && effective[i] === -1 && exp[i] === 0) {
          underflow = true;
          // Pass 2 reads singleton b on lane (cutIn ^ p2Test) = 0, regenerating W and toggling cut.
          cut = cutIn ^ 1;
        } else {
          exp[i] += effective[i];
        }
      }
      return { ...entry, cutIn, cutOut: cut, effective, underflow, before, after: exp.slice() };
    });
  }

  function makeChip(lane) {
    const span = document.createElement("span");
    span.className = `lane-chip lane-${lane}`;
    span.textContent = String(lane);
    return span;
  }

  function formatSign(programmed, effective) {
    const sign = document.createElement("span");
    const flipped = programmed !== effective;
    const symbol = value => (value > 0 ? "+" : "−");
    sign.className = flipped ? "wt-sign wt-sign-flip" : "wt-sign";
    if (flipped) {
      sign.textContent = symbol(effective);
      sign.title = `Programmed ${symbol(programmed)}, inverted by cut 1`;
    } else {
      sign.textContent = symbol(effective);
    }
    return sign;
  }

  function renderGuard() {
    document.getElementById("wt-x0").setAttribute("aria-pressed", String(xZero));
    document.getElementById("wt-x1").setAttribute("aria-pressed", String(!xZero));
    document.getElementById("wt-prev").disabled = stageIndex === 0;
    document.getElementById("wt-next").disabled = stageIndex === STAGES.length - 1;

    const pills = document.getElementById("wt-stage-pills");
    pills.replaceChildren(...STAGES.map((stage, i) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "wt-pill";
      button.textContent = stage.title;
      if (i === stageIndex) button.setAttribute("aria-current", "step");
      button.addEventListener("click", () => { stageIndex = i; renderGuard(); });
      return button;
    }));

    // Stack every summary in one grid cell so the tallest sets the height and the table never shifts.
    document.getElementById("wt-stage-summary").replaceChildren(...STAGES.flatMap((stage, i) =>
      [true, false].map(x => {
        const span = document.createElement("span");
        span.textContent = stage.summary(x);
        if (i !== stageIndex || x !== xZero) span.className = "wt-summary-spacer";
        return span;
      })));

    const trace = simulateGuard(xZero);
    const rows = trace.map((step, index) => {
      const tr = document.createElement("tr");
      if (step.stage === stageIndex) tr.classList.add("wt-row-active");
      if (index > 0 && trace[index - 1].stage !== step.stage) tr.classList.add("wt-stage-start");
      if (step.underflow) tr.classList.add("wt-row-underflow");

      const cmdCell = document.createElement("th");
      cmdCell.scope = "row";
      cmdCell.textContent = String(step.cmd);
      tr.append(cmdCell);

      const cutInCell = document.createElement("td");
      cutInCell.append(makeChip(step.cutIn));
      tr.append(cutInCell);

      for (let i = 0; i < 3; i++) {
        const td = document.createElement("td");
        td.append(formatSign(step.signs[i], step.effective[i]));
        const expSpan = document.createElement("span");
        expSpan.className = "wt-exp";
        expSpan.textContent = `E=${step.after[i]}`;
        td.append(expSpan);
        if (i === 0 && step.underflow) {
          const flag = document.createElement("span");
          flag.className = "wt-flag";
          flag.textContent = "underflow";
          td.append(flag);
        }
        tr.append(td);
      }

      const cutOutCell = document.createElement("td");
      cutOutCell.append(makeChip(step.cutOut));
      tr.append(cutOutCell);

      return tr;
    });
    document.getElementById("wt-guard-rows").replaceChildren(...rows);
  }

  document.getElementById("wt-x0").addEventListener("click", () => { xZero = true; renderGuard(); });
  document.getElementById("wt-x1").addEventListener("click", () => { xZero = false; renderGuard(); });
  document.getElementById("wt-prev").addEventListener("click", () => { if (stageIndex > 0) { stageIndex--; renderGuard(); } });
  document.getElementById("wt-next").addEventListener("click", () => { if (stageIndex < STAGES.length - 1) { stageIndex++; renderGuard(); } });
  document.getElementById("wt-reset").addEventListener("click", () => { stageIndex = 0; renderGuard(); });

  renderGuard();
})();
