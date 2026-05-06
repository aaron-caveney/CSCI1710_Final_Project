//To use run follow these steps:  
// 
// 1: Run the racket file
// 2: run the defualt visulizer creating a trace
// 3: press the script button in the top right of the visulizer
// 4: Make sure <svg> is selected and then Copy + paste the visulizer script into the script section
// 5: Press run and you should see the visualization of the trace

const stateContainer = d3.select(svg);
if (stateContainer.datum() === undefined) {
    stateContainer.datum({ current_state: 0 });
}

function getCurrentState() {
    return stateContainer.datum().current_state;
}

function incrementState() {
    const data = stateContainer.datum();
    if (data.current_state < instances.length - 1) {
        data.current_state += 1;
    }
}

function decrementState() {
    const data = stateContainer.datum();
    if (data.current_state !== 0) {
        data.current_state -= 1;
    }
}

// ── Helpers ───────────────────────────────────────────────────────
function fam(expr) {
    if (!expr.empty()) return expr.tuples()[0].atoms()[0];
    return "none";
}

function atomStr(atom) {
    return atom.toString().replace(/^\[|\]$/g, "");
}

function getPop(habitatName, field, stateIndex) {
    let hAtom = instances[stateIndex].atom(habitatName);
    if (!hAtom || !hAtom[field]) return "Empty0";
    return atomStr(fam(hAtom[field]));
}

function getLastEvent(habitatName, stateIndex) {
    let hAtom = instances[stateIndex].atom(habitatName);
    if (!hAtom || !hAtom["lastEvent"]) return "DoNothing0";
    return atomStr(fam(hAtom["lastEvent"])).replace("0", "");
}

// Population-level color mapping
const POP_COLORS = {
    "Empty0":         "#d0d0d0",
    "Low0":           "#e05252",
    "Medium0":        "#f0c040",
    "High0":          "#6bbf6b",
    "Overpopulated0": "#8b0000",
};

// Event color mapping
const EVENT_COLORS = {
    "ElkGrow":              "#a8d8a8",
    "ElkReproduce":         "#68b668",
    "WolfPredation":        "#e07070",
    "VegetationRecover":    "#70c0a0",
    "ElkDegradeVegetation": "#c0a040",
    "WolfStarve":           "#c06060",
    "ReintroduceWolves":    "#7090e0",
    "WolfMigrate":          "#9070c0",
    "ElkDisperse":          "#d0a060",
    "DoNothing":            "#cccccc",
};

function popColor(levelStr) {
    return POP_COLORS[levelStr] || "#aaaaaa";
}

function eventColor(eventStr) {
    return EVENT_COLORS[eventStr] || "#aaaaaa";
}

// ── Main Render Function ──────────────────────────────────────────
function render() {
    d3.select(svg).selectAll("*").remove();
    
    const stage = new Stage();
    const cs = getCurrentState();

    // ── Navigation Controls ───────────────────────────────────────
    stage.add(new TextBox({
        text: `State: ${cs} / ${instances.length - 1}`,
        coords: { x: 300, y: 520 },
        fontSize: 20,
        fontWeight: "Bold",
        color: "black",
    }));

    stage.add(new TextBox({
        text: "▬", color: cs === 0 ? "lightgray" : "gray", 
        coords: { x: 200, y: 550 }, fontSize: 100,
        events: [{ event: "click", callback: () => { decrementState(); render(); } }]
    }));
    stage.add(new TextBox({
        text: "Previous State", 
        coords: { x: 200, y: 540 }, fontSize: 14, fontWeight: "Bold", color: "white",
        events: [{ event: "click", callback: () => { decrementState(); render(); } }]
    }));

    stage.add(new TextBox({
        text: "▬", color: cs === instances.length - 1 ? "lightgray" : "gray", 
        coords: { x: 400, y: 550 }, fontSize: 100,
        events: [{ event: "click", callback: () => { incrementState(); render(); } }]
    }));
    stage.add(new TextBox({
        text: "Next State", 
        coords: { x: 400, y: 540 }, fontSize: 14, fontWeight: "Bold", color: "white",
        events: [{ event: "click", callback: () => { incrementState(); render(); } }]
    }));

    // ── Fetch Habitats ────────────────────────────────────────────
    const habitats = Habitat.atoms().map(t => atomStr(fam(t)));

    const HABITAT_X = 30;
    const HABITAT_W = 250;
    const HABITAT_H = 160;
    const ICON_W = 140;
    const ICON_H = 26;
    const SUMMARY_X = 340;

    // ── Draw Habitats (Left Column) ───────────────────────────────
    stage.add(new TextBox({
        text: 'Habitats', coords: { x: HABITAT_X + (HABITAT_W / 2), y: 30 },
        color: 'black', fontSize: 16, fontWeight: "Bold"
    }));

    habitats.forEach((hName, i) => {
        let hy = 50 + i * (HABITAT_H + 20);

        let wPop = getPop(hName, "wolfPop", cs);
        let ePop = getPop(hName, "elkPop", cs);
        let vPop = getPop(hName, "vegLevel", cs);
        let lastEv = getLastEvent(hName, cs);

        // Main Habitat Box
        stage.add(new Rectangle({
            coords: { x: HABITAT_X, y: hy },
            width: HABITAT_W, height: HABITAT_H,
            color: "#fcfaf7", borderColor: "black", borderWidth: 2,
            label: hName
        }));

        // Wolves
        stage.add(new Rectangle({
            coords: { x: HABITAT_X + 15, y: hy + 20 },
            width: ICON_W, height: ICON_H,
            color: popColor(wPop), borderColor: "black", borderWidth: 2,
            label: `🐺 ${wPop.replace("0", "")}`
        }));

        // Elk
        stage.add(new Rectangle({
            coords: { x: HABITAT_X + 15, y: hy + 55 },
            width: ICON_W, height: ICON_H,
            color: popColor(ePop), borderColor: "black", borderWidth: 2,
            label: `🦌 ${ePop.replace("0", "")}`
        }));

        // Vegetation
        stage.add(new Rectangle({
            coords: { x: HABITAT_X + 10, y: hy + 90 },
            width: HABITAT_W - 20, height: 20,
            color: popColor(vPop), borderColor: "black", borderWidth: 1,
            label: `🌿 Veg: ${vPop.replace("0", "")}`
        }));

        // Last Event banner at bottom of habitat box
        stage.add(new Rectangle({
            coords: { x: HABITAT_X + 10, y: hy + HABITAT_H - 28 },
            width: HABITAT_W - 20, height: 22,
            color: eventColor(lastEv), borderColor: "black", borderWidth: 1,
            label: `⚡ ${lastEv}`
        }));
    });

    // ── Summary & Legend (Right Column) ──────────────────────────

    // Divider
    stage.add(new Line({
        points: [ { x: SUMMARY_X - 30, y: 30 }, { x: SUMMARY_X - 30, y: 500 } ],
        color: 'black', width: 2, style: "dotted"
    }));

    // Summary Title
    stage.add(new TextBox({ 
        text: "Habitat Summary", coords: { x: SUMMARY_X + 60, y: 30 }, 
        fontSize: 16, fontWeight: "Bold", color: "black" 
    }));

    habitats.forEach((hName, i) => {
        let wPop = getPop(hName, "wolfPop", cs);
        let ePop = getPop(hName, "elkPop", cs);
        let sy = 60 + i * 80;

        stage.add(new TextBox({ 
            text: hName, coords: { x: SUMMARY_X + 20, y: sy }, 
            fontSize: 14, fontWeight: "Bold" 
        }));
        stage.add(new Rectangle({ 
            coords: { x: SUMMARY_X + 10, y: sy + 15 }, width: ICON_W - 30, height: ICON_H, 
            color: popColor(wPop), borderColor: "black", borderWidth: 2, 
            label: `🐺 ${wPop.replace("0", "")}` 
        }));
        stage.add(new Rectangle({ 
            coords: { x: SUMMARY_X + 130, y: sy + 15 }, width: ICON_W - 30, height: ICON_H, 
            color: popColor(ePop), borderColor: "black", borderWidth: 2, 
            label: `🦌 ${ePop.replace("0", "")}` 
        }));
    });

    // ── Population Legend ─────────────────────────────────────────
    stage.add(new TextBox({
        text: 'Population Level:',
        coords: { x: SUMMARY_X + 40, y: 240 },
        color: 'black', fontSize: 15, fontWeight: "Bold"
    }));

    const legendEntries = [
        { label: "Empty",         color: "#d0d0d0" },
        { label: "Low",           color: "#e05252" },
        { label: "Medium",        color: "#f0c040" },
        { label: "High",          color: "#6bbf6b" },
        { label: "Overpopulated", color: "#8b0000" }
    ];

    legendEntries.forEach((e, i) => {
        stage.add(new Rectangle({
            coords: { x: SUMMARY_X + 10, y: 265 + i * 30 },
            width: 18, height: 18,
            color: e.color, borderColor: "black", borderWidth: 1
        }));
        stage.add(new TextBox({
            text: e.label,
            coords: { x: SUMMARY_X + 40, y: 265 + i * 30 + 10 },
            fontSize: 13, color: "black"
        }));
    });

    // ── Event Legend ──────────────────────────────────────────────
    stage.add(new TextBox({
        text: 'Last Event:',
        coords: { x: SUMMARY_X + 40, y: 420 },
        color: 'black', fontSize: 15, fontWeight: "Bold"
    }));

    const eventLegend = Object.entries(EVENT_COLORS);
    eventLegend.forEach(([name, color], i) => {
        const col = i < 5 ? 0 : 1;
        const row = i % 5;
        stage.add(new Rectangle({
            coords: { x: SUMMARY_X + 10 + col * 160, y: 445 + row * 22 },
            width: 12, height: 12,
            color: color, borderColor: "black", borderWidth: 1
        }));
        stage.add(new TextBox({
            text: name,
            coords: { x: SUMMARY_X + 30 + col * 160, y: 445 + row * 22 + 8 },
            fontSize: 11, color: "black"
        }));
    });

    stage.render(svg);
}

render();