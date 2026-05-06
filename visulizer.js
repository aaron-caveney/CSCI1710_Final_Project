
//To use run follow these steps:  
// 
// 1: Run the racket file
// 2: press the script button in the top left of the visulizer
// 3: Make sure <svg> is selected and then Copy + paste the visulizer script into the script section
// 4: 

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
    return atom.toString().replace(/^\[/, "");
}

// Population-level color mapping
const POP_COLORS = {
    "Empty0":         "#d0d0d0",
    "Low0":           "#e05252",
    "Medium0":        "#f0c040",
    "High0":          "#6bbf6b",
    "Overpopulated0": "#8b0000",
};

function popColor(levelStr) {
    return POP_COLORS[levelStr] || "#aaaaaa";
}

// ── Main Render Function ──────────────────────────────────────────
function render() {
    // CRITICAL FIX: Completely wipe the SVG before drawing the new state
    // This prevents the "0" and "1" text from overlapping.
    d3.select(svg).selectAll("*").remove();
    
    // Create a fresh stage for this specific state
    const stage = new Stage();
    const cs = getCurrentState();

    // ──────────────────────────────────────────────────────────────
    // 1. Navigation Controls (At the bottom)
    // ──────────────────────────────────────────────────────────────
    stage.add(new TextBox({
        text: `State: ${cs} / ${instances.length - 1}`,
        coords: { x: 300, y: 520 },
        fontSize: 20,
        fontWeight: "Bold",
        color: "black",
    }));

    // Previous Button
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

    // Next Button
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

    // ──────────────────────────────────────────────────────────────
    // 2. Fetch Atoms for Current State
    // ──────────────────────────────────────────────────────────────
    const habitats = Habitat.atoms().map(t => fam(t));
    const wolves = Wolf.atoms().map(t => fam(t));
    const elks = Elk.atoms().map(t => fam(t));
    const vegs = Vegetation.atoms().map(t => fam(t));

    // Layout constants
    const HABITAT_X = 30;
    const HABITAT_W = 250;
    const HABITAT_H = 140;
    const ICON_W = 36;
    const ICON_H = 26;
    const SUMMARY_X = 340;

    // ──────────────────────────────────────────────────────────────
    // 3. Draw Habitats (Left Column)
    // ──────────────────────────────────────────────────────────────
    stage.add(new TextBox({
        text: 'Habitats', coords: { x: HABITAT_X + (HABITAT_W / 2), y: 30 },
        color: 'black', fontSize: 16, fontWeight: "Bold"
    }));

    habitats.forEach((habitat, i) => {
        let hName = atomStr(habitat);
        let hy = 50 + i * (HABITAT_H + 20);

        // Main Habitat Box
        stage.add(new Rectangle({
            coords: { x: HABITAT_X, y: hy },
            width: HABITAT_W, height: HABITAT_H,
            color: "#fcfaf7", borderColor: "black", borderWidth: 2,
            label: hName
        }));

        // Vegetation Strip (Bottom of Habitat)
        let hVegs = vegs.filter(v => atomStr(fam(instances[cs].atom(atomStr(v)).vegLocation)) === hName);
        hVegs.forEach((v, j) => {
            let vName = atomStr(v);
            let vPop = instances[cs].atom(vName).vegLevel.toString();
            stage.add(new Rectangle({
                coords: { x: HABITAT_X + 10, y: hy + HABITAT_H - 30 },
                width: HABITAT_W - 20, height: 20,
                color: popColor(vPop), borderColor: "black", borderWidth: 1,
                label: `🌿 Veg: ${vPop.replace("0", "")}`
            }));
        });

        // Wolves inside Habitat
        let hWolves = wolves.filter(w => atomStr(fam(instances[cs].atom(atomStr(w)).wolfLocation)) === hName);
        hWolves.forEach((w, j) => {
            let wName = atomStr(w);
            let wPop = instances[cs].atom(wName).wolfPop.toString();
            stage.add(new Rectangle({
                coords: { x: HABITAT_X + 15 + (j * (ICON_W + 10)), y: hy + 20 },
                width: ICON_W, height: ICON_H,
                color: popColor(wPop), borderColor: "black", borderWidth: 2,
                label: `🐺${wName.slice(-1)}`
            }));
        });

        // Elk inside Habitat
        let hElks = elks.filter(e => atomStr(fam(instances[cs].atom(atomStr(e)).elkLocation)) === hName);
        hElks.forEach((e, j) => {
            let eName = atomStr(e);
            let ePop = instances[cs].atom(eName).elkPop.toString();
            stage.add(new Rectangle({
                coords: { x: HABITAT_X + 15 + (j * (ICON_W + 10)), y: hy + 60 },
                width: ICON_W, height: ICON_H,
                color: popColor(ePop), borderColor: "black", borderWidth: 2,
                label: `🦌${eName.slice(-1)}`
            }));
        });
    });

    // ──────────────────────────────────────────────────────────────
    // 4. Draw Summary & Legend (Right Column)
    // ──────────────────────────────────────────────────────────────
    
    // Dotted Divider Line
    stage.add(new Line({
        points: [ { x: SUMMARY_X - 30, y: 30 }, { x: SUMMARY_X - 30, y: 450 } ],
        color: 'black', width: 2, style: "dotted"
    }));

    // All Wolves Summary
    stage.add(new TextBox({ text: "All Wolves", coords: { x: SUMMARY_X + 40, y: 40 }, fontSize: 14, fontWeight: "Bold" }));
    wolves.forEach((w, i) => {
        let name = atomStr(w);
        let pop = instances[cs].atom(name).wolfPop.toString();
        stage.add(new Rectangle({ 
            coords: { x: SUMMARY_X + i * 45, y: 60 }, width: ICON_W, height: ICON_H, 
            color: popColor(pop), borderColor: "black", borderWidth: 2, label: `🐺${name.slice(-1)}` 
        }));
    });

    // All Elk Summary
    stage.add(new TextBox({ text: "All Elk", coords: { x: SUMMARY_X + 40, y: 110 }, fontSize: 14, fontWeight: "Bold" }));
    elks.forEach((e, i) => {
        let name = atomStr(e);
        let pop = instances[cs].atom(name).elkPop.toString();
        stage.add(new Rectangle({ 
            coords: { x: SUMMARY_X + i * 45, y: 130 }, width: ICON_W, height: ICON_H, 
            color: popColor(pop), borderColor: "black", borderWidth: 2, label: `🦌${name.slice(-1)}` 
        }));
    });

    // Legend
    stage.add(new TextBox({
        text: 'Population Level:',
        coords: { x: SUMMARY_X + 40, y: 220 },
        color: 'black', fontSize: 15, fontWeight: "Bold"
    }));

    const legendEntries = [
        { label: "Empty", color: "#d0d0d0" },
        { label: "Low", color: "#e05252" },
        { label: "Medium", color: "#f0c040" },
        { label: "High", color: "#6bbf6b" },
        { label: "Overpopulated", color: "#8b0000" }
    ];

    legendEntries.forEach((e, i) => {
        stage.add(new Rectangle({
            coords: { x: SUMMARY_X + 10, y: 245 + i * 30 },
            width: 18, height: 18,
            color: e.color, borderColor: "black", borderWidth: 1
        }));
        stage.add(new TextBox({
            text: e.label,
            coords: { x: SUMMARY_X + 40, y: 245 + i * 30 + 10 },
            fontSize: 13, color: "black"
        }));
    });

    // Finally, render everything to the SVG
    stage.render(svg);
}

// Initial render
render();