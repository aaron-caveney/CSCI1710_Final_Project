#lang forge/temporal

abstract sig PopLevel {}
one sig Empty, Low, Medium, High, Overpopulated extends PopLevel {}

sig Habitat {
    adjacent: set Habitat,
    var elkPop:  one PopLevel,
    var wolfPop: one PopLevel,
    var vegLevel: one PopLevel
}

// sig Wolf {
//     var wolfPop: one PopLevel,
//     var wolfLocation: one Habitat
// }

// sig Elk {
//     var elkPop: one PopLevel,
//     var elkLocation: one Habitat
// }

// sig Vegetation {
//     var vegLevel: one PopLevel,
//     vegLocation: one Habitat
// }

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

// pred frameWolves[w: Wolf] {
//     all other_w: Wolf | other_w != w implies {
//         other_w.wolfPop'      = other_w.wolfPop
//         other_w.wolfLocation' = other_w.wolfLocation
//     }
// }

// pred frameElk[e: Elk] {
//     all other_e: Elk | other_e != e implies {
//         other_e.elkPop'      = other_e.elkPop
//         other_e.elkLocation' = other_e.elkLocation
//     }
// }

// pred frameAllElk {
//     all e: Elk | {
//         e.elkPop'      = e.elkPop
//         e.elkLocation' = e.elkLocation
//     }
// }

// pred frameAllWolves {
//     all w: Wolf | {
//         w.wolfPop'      = w.wolfPop
//         w.wolfLocation' = w.wolfLocation
//     }
// }

// pred frameVegetation[v: Vegetation] {
//     all other_v: Vegetation | other_v != v implies {
//         other_v.vegLevel' = other_v.vegLevel
//     }
// }

// pred frameAllVegetation {
//     all v: Vegetation | v.vegLevel' = v.vegLevel
// }

//transitions
pred elkGrow[h: Habitat] {
    h.wolfPop = Empty
    h.elkPop != Overpopulated
    h.vegLevel != Empty
    nextLevel[h.elkPop, h.elkPop']
    prevLevel[h.vegLevel, h.vegLevel']
    h.wolfPop' = h.wolfPop
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred wolfPredation[h: Habitat] {
    h.wolfPop != Empty
    h.elkPop  != Empty
    prevLevel[h.elkPop,  h.elkPop']
    nextLevel[h.wolfPop, h.wolfPop']
    h.vegLevel' = h.vegLevel
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred vegetationRecover[h: Habitat] {
    h.elkPop != Overpopulated
    h.vegLevel != Overpopulated
    nextLevel[h.vegLevel, h.vegLevel']
    h.elkPop'  = h.elkPop
    h.wolfPop' = h.wolfPop
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred elkDegradeVegetation[h: Habitat] {
    h.elkPop = Overpopulated
    h.vegLevel != Empty
    prevLevel[h.vegLevel, h.vegLevel']
    h.elkPop'  = h.elkPop
    h.wolfPop' = h.wolfPop
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred wolfStarve[h: Habitat] {
    h.elkPop  = Empty
    h.wolfPop != Empty
    prevLevel[h.wolfPop, h.wolfPop']
    h.elkPop'  = h.elkPop
    h.vegLevel' = h.vegLevel
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

// wolf moves from one habitat to adjacent, taking population with it
pred wolfMigrate[h1: Habitat, h2: Habitat] {
    h2 in h1.adjacent
    h1.wolfPop != Empty
    h2.wolfPop = Empty          // only migrate into empty habitat
    nextLevel[h2.wolfPop, h2.wolfPop']
    prevLevel[h1.wolfPop, h1.wolfPop']
    h1.elkPop'  = h1.elkPop
    h1.vegLevel' = h1.vegLevel
    h2.elkPop'  = h2.elkPop
    h2.vegLevel' = h2.vegLevel
    all other: Habitat | (other != h1 and other != h2) implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred reintroduceWolves[h: Habitat] {
    h.wolfPop = Empty
    h.wolfPop' = Low
    h.elkPop'  = h.elkPop
    h.vegLevel' = h.vegLevel
    all other: Habitat | other != h implies {
        other.elkPop'  = other.elkPop
        other.wolfPop' = other.wolfPop
        other.vegLevel' = other.vegLevel
    }
}

pred doNothing {
    all h: Habitat | {
        h.elkPop'   = h.elkPop
        h.wolfPop'  = h.wolfPop
        h.vegLevel' = h.vegLevel
    }
}


pred step {
    some h: Habitat, h2: Habitat | {
        elkGrow[h]              or
        wolfPredation[h]        or
        vegetationRecover[h]    or
        elkDegradeVegetation[h] or
        wolfStarve[h]           or
        reintroduceWolves[h]    or
        wolfMigrate[h, h2]
    } or doNothing
}

// initial state (for now....)
pred init {
    all h: Habitat | h.wolfPop = Empty
    all h: Habitat  | h.elkPop  = Overpopulated
    all h: Habitat | h.vegLevel = Low
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
        all h: Habitat | h.wolfPop != Empty
        all h: Habitat  | h.elkPop  = Medium
        all h: Habitat | h.vegLevel = Medium
    }
} for 2 Habitat

//more runs coming soon...

