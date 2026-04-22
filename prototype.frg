#lang forge/temporal

abstract sig PopLevel {}
one sig Empty, Low, Medium, High, Overpopulated extends PopLevel {}

sig Habitat {
    adjacent: set Habitat
    // var elkPop:  one PopLevel,
    // var wolfPop: one PopLevel,
    // var vegLevel: one PopLevel
}

sig Wolf {
    var wolfPop: one PopLevel,
    var wolfLocation: one Habitat
}

sig Elk {
    var elkPop: one PopLevel,
    var elkLocation: one Habitat
}

sig Vegetation {
    var vegLevel: one PopLevel,
    vegLocation: one Habitat
}

// ── level helpers ──────────────────────────────────────────────
pred nextLevel[p: PopLevel, q: PopLevel] {
    (p = Empty       and q = Low)         or
    (p = Low         and q = Medium)      or
    (p = Medium      and q = High)        or
    (p = High        and q = Overpopulated) or
    (p = Overpopulated and q = Overpopulated)
}

pred prevLevel[p: PopLevel, q: PopLevel] {
    (p = Overpopulated and q = High)   or
    (p = High          and q = Medium) or
    (p = Medium        and q = Low)    or
    (p = Low           and q = Empty)  or
    (p = Empty         and q = Empty)
}

// frames
// we call these inside each pred to hold everything else constant (where its breaking right now)

pred frameOthers[h: Habitat] {
    all other: Habitat | other != h implies {
        other.elkPop'   = other.elkPop
        other.wolfPop'  = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred frameWolves[w: Wolf] {
    all other_w: Wolf | other_w != w implies {
        other_w.wolfPop'      = other_w.wolfPop
        other_w.wolfLocation' = other_w.wolfLocation
    }
}

pred frameElk[e: Elk] {
    all other_e: Elk | other_e != e implies {
        other_e.elkPop'      = other_e.elkPop
        other_e.elkLocation' = other_e.elkLocation
    }
}

pred frameAllElk {
    all e: Elk | {
        e.elkPop'      = e.elkPop
        e.elkLocation' = e.elkLocation
    }
}

pred frameAllWolves {
    all w: Wolf | {
        w.wolfPop'      = w.wolfPop
        w.wolfLocation' = w.wolfLocation
    }
}

pred frameVegetation[v: Vegetation] {
    all other_v: Vegetation | other_v != v implies {
        other_v.vegLevel' = other_v.vegLevel
    }
}

pred frameAllVegetation {
    all v: Vegetation | v.vegLevel' = v.vegLevel
}

//transitions
pred elkGrow[e: Elk] {
    // LOGIC
    no w: Wolf | w.wolfLocation = e.elkLocation and w.wolfPop != Empty
    e.elkPop != Overpopulated
    // elk can only grow if vegetation exists in same habitat
    some v: Vegetation | v.vegLocation = e.elkLocation and v.vegLevel != Empty
    nextLevel[e.elkPop, e.elkPop']
    // growing elk consume vegetation
    some v: Vegetation | {
        v.vegLocation = e.elkLocation
        v.vegLevel != Empty
        prevLevel[v.vegLevel, v.vegLevel']
        frameVegetation[v]
    }
    // FRAME
    e.elkLocation' = e.elkLocation
    frameElk[e]
    frameAllWolves
}

pred wolfPredation[w: Wolf, e: Elk] {
    // LOGIC
    w.wolfLocation = e.elkLocation
    w.wolfPop != Empty
    e.elkPop != Empty
    prevLevel[e.elkPop, e.elkPop']
    nextLevel[w.wolfPop, w.wolfPop']
    // FRAME
    e.elkLocation' = e.elkLocation        // active elk's location unchanged
    w.wolfLocation' = w.wolfLocation      // active wolf's location unchanged
    frameElk[e]                           // all other elk unchanged
    frameWolves[w]                        // all other wolves unchanged
    frameAllVegetation                    // all vegetation unchanged
}

pred vegetationRecover[v: Vegetation] {
    // recovers when no overpopulated elk in same habitat
    no e: Elk | e.elkLocation = v.vegLocation and e.elkPop = Overpopulated
    v.vegLevel != Overpopulated
    nextLevel[v.vegLevel, v.vegLevel']
    frameVegetation[v]
    frameAllWolves
    frameAllElk
}

// pred elkDegradeVegetation[e: Elk, v: Vegetation] {
//     // LOGIC
//     e.elkLocation = v.vegLocation
//     e.elkPop = Overpopulated
//     v.vegLevel != Empty
//     prevLevel[v.vegLevel, v.vegLevel']
//     // FRAME
//     e.elkPop' = e.elkPop                  // active elk's pop unchanged
//     e.elkLocation' = e.elkLocation        // active elk's location unchanged
//     frameVegetation[v]                    // all other vegetation unchanged
//     frameElk[e]                           // all other elk unchanged
//     frameAllWolves                        // all wolves unchanged
// }

pred wolfStarve[w: Wolf, e: Elk] {
    // LOGIC
    w.wolfLocation = e.elkLocation
    e.elkPop = Empty
    w.wolfPop != Empty
    prevLevel[w.wolfPop, w.wolfPop']
    // FRAME
    w.wolfLocation' = w.wolfLocation      // active wolf's location unchanged
    e.elkPop' = e.elkPop                  // active elk's pop unchanged
    e.elkLocation' = e.elkLocation        // active elk's location unchanged
    frameWolves[w]                        // all other wolves unchanged
    frameAllElk                           // all other elk unchanged
    frameAllVegetation                    // all vegetation unchanged
}

pred wolfMigrate[w: Wolf] {
    // LOGIC
    some h: Habitat | {
        h in w.wolfLocation.adjacent
        w.wolfLocation' = h
    }
    // FRAME
    w.wolfPop' = w.wolfPop                // active wolf's pop unchanged
    frameWolves[w]                        // all other wolves unchanged
    frameAllElk                           // all elk unchanged
    frameAllVegetation                    // all vegetation unchanged
}

pred reintroduceWolves[w: Wolf, h: Habitat] {
    // LOGIC
    w.wolfPop = Empty
    w.wolfPop' = Low
    w.wolfLocation' = h
    // FRAME
    frameWolves[w]                        // all other wolves unchanged
    frameAllElk                           // all elk unchanged
    //all v: Vegetation | v.vegLocation != h implies v.vegLevel' = v.vegLevel               // all vegetation unchanged
    frameAllVegetation
}
pred doNothing {
    all w: Wolf | w.wolfPop' = w.wolfPop and w.wolfLocation' = w.wolfLocation
    all e: Elk  | e.elkPop'  = e.elkPop  and e.elkLocation'  = e.elkLocation
    all v: Vegetation | v.vegLevel' = v.vegLevel
}

pred step {
    some e: Elk, w: Wolf, v: Vegetation, h: Habitat | {
        wolfPredation[w, e]        or
        elkGrow[e]                 or
        wolfStarve[w, e]           or
        //elkDegradeVegetation[e, v] or
        wolfMigrate[w]             or
        reintroduceWolves[w, h]    or
        vegetationRecover[v]
    } or doNothing
}


// initial state (for now....)
pred init {
    all w: Wolf | w.wolfPop = Empty
    all e: Elk  | e.elkPop  = Overpopulated
    all v: Vegetation | v.vegLevel = Low
}

pred validTrace {
    init
    always step
}

// 

// can coexistence ever be reached?
option max_tracelength 20

run  {
    validTrace
    eventually {
        all w: Wolf | w.wolfPop != Empty
        all e: Elk  | e.elkPop  = Medium
        all v: Vegetation | v.vegLevel = Medium
    }
} for 2 Habitat, 1 Wolf, 1 Elk, 1 Vegetation

//more runs coming soon...

