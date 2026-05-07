#lang forge/temporal

abstract sig PopLevel {}
abstract sig Event {}
one sig Empty, Low, Medium, High, Overpopulated extends PopLevel {}
one sig ElkGrow, ElkReproduce, WolfPredation, VegetationRecover, 
        ElkDegradeVegetation, WolfStarve, ReintroduceWolves,
        WolfMigrate, ElkDisperse, DoNothing extends Event {}

sig Habitat {
    adjacent: set Habitat,
    var elkPop:   one PopLevel,
    var wolfPop:  one PopLevel,
    var vegLevel: one PopLevel,
    var lastEvent: one Event  
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
        other.lastEvent' = other.lastEvent
    }
}
//transitions
pred elkGrow[h: Habitat] {
    h.wolfPop = Empty
    h.elkPop != Overpopulated
    h.vegLevel != Empty
    nextLevel[h.elkPop, h.elkPop']
    prevLevel[h.vegLevel, h.vegLevel']
    h.wolfPop' = h.wolfPop
    frameOthers[h]
    h.lastEvent' = ElkGrow
}
//Harder to occur, but helps lead to a more stable scenario 
pred elkReproduce[h: Habitat] {
    h.elkPop != Overpopulated
    h.vegLevel = High or h.vegLevel = Overpopulated  // abundant food
    nextLevel[h.elkPop, h.elkPop']
    prevLevel[h.vegLevel, h.vegLevel']
    h.wolfPop' = h.wolfPop
    frameOthers[h]
    h.lastEvent' = ElkReproduce
}

pred wolfPredation[h: Habitat] {
    h.wolfPop != Empty
    h.elkPop  != Empty
    prevLevel[h.elkPop,  h.elkPop']
    nextLevel[h.wolfPop, h.wolfPop']
    h.vegLevel' = h.vegLevel
    frameOthers[h]
    h.lastEvent' = WolfPredation
}

pred vegetationRecover[h: Habitat] {
    h.elkPop != Overpopulated
    h.elkPop != High
    h.vegLevel != Overpopulated
    nextLevel[h.vegLevel, h.vegLevel']
    h.elkPop'  = h.elkPop
    h.wolfPop' = h.wolfPop
    frameOthers[h]
    h.lastEvent' = VegetationRecover
}

pred elkDegradeVegetation[h: Habitat] {
    h.elkPop = Overpopulated
    h.vegLevel != Empty
    prevLevel[h.vegLevel, h.vegLevel']
    h.elkPop'  = h.elkPop
    h.wolfPop' = h.wolfPop
    frameOthers[h]
    h.lastEvent' = ElkDegradeVegetation
}

pred elkDisperse[h1: Habitat, h2: Habitat] {
    // LOGIC
    h2 in h1.adjacent                                         // habitats must be connected
    h1.elkPop != Empty and h1.elkPop != Low                   // source must have meaningful population
    h1.vegLevel != High and h1.vegLevel != Overpopulated      // food is scarce (medium, low, or empty)
    h2.elkPop != Overpopulated                                // destination not already overwhelmed
    // source loses population
    prevLevel[h1.elkPop, h1.elkPop']
    // destination gains population
    nextLevel[h2.elkPop, h2.elkPop']
    // vegetation in destination decreases as new elk arrive
    prevLevel[h2.vegLevel, h2.vegLevel']
    // FRAME
    h1.wolfPop'  = h1.wolfPop
    h1.vegLevel' = h1.vegLevel                                // source veg unchanged (elk left)
    h2.wolfPop'  = h2.wolfPop
    all other: Habitat | (other != h1 and other != h2) implies {
        other.elkPop'   = other.elkPop
        other.wolfPop'  = other.wolfPop
        other.vegLevel' = other.vegLevel
        other.lastEvent' = other.lastEvent
    }
    h1.lastEvent' = ElkDisperse
    h2.lastEvent' = ElkDisperse
}

pred wolfStarve[h: Habitat] {
    h.elkPop  = Empty
    h.wolfPop != Empty
    prevLevel[h.wolfPop, h.wolfPop']
    h.elkPop'  = h.elkPop
    h.vegLevel' = h.vegLevel
    frameOthers[h]
    h.lastEvent' = WolfStarve
}

// wolf moves from one habitat to adjacent, taking population with it
pred wolfMigrate[h1: Habitat, h2: Habitat] {
    h2 in h1.adjacent
    h1.wolfPop != Empty
    h1.elkPop = Low or h1.elkPop = Empty  // wolves leave when food is scarce
    h2.wolfPop = Empty       // only migrate into empty habitat
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
        other.lastEvent' = other.lastEvent
    }
    h1.lastEvent' = WolfMigrate
    h2.lastEvent' = WolfMigrate
    
}

pred reintroduceWolves[h: Habitat] {
    h.wolfPop = Empty
    // wolves were never present anywhere before
    all h2: Habitat | h2.wolfPop = Empty
    h.wolfPop' = Low
    h.elkPop'  = h.elkPop
    h.vegLevel' = h.vegLevel
    frameOthers[h]
    h.lastEvent' = ReintroduceWolves
}

pred doNothing {
    all h: Habitat | {
        h.elkPop'   = h.elkPop
        h.wolfPop'  = h.wolfPop
        h.vegLevel' = h.vegLevel
        h.lastEvent' = DoNothing
    }
}


pred step {
    some h: Habitat, h2: Habitat | { //should switch to all h eventually for realism. just some for now bc easier to read
        elkGrow[h]              or
        wolfPredation[h]        or
        vegetationRecover[h]    or
        elkDegradeVegetation[h] or
        wolfStarve[h]           or
        reintroduceWolves[h]    or
        wolfMigrate[h, h2]      or 
        elkDisperse[h, h2]      or 
        elkReproduce[h]
    } or doNothing
}

// initial state (can be adjusted)
pred init {
    all h: Habitat | {
        h.wolfPop  = Empty
        h.elkPop   = Overpopulated
        h.vegLevel = Medium
    }
    // ensure habitats are connected
    all h: Habitat | some h.adjacent
    all h: Habitat | h not in h.adjacent  // no self-loops
}

pred validTrace {
    init
    always step
}

// 

// can coexistence ever be reached?
option max_tracelength 20
//"stability"
run  {
    validTrace
    eventually {
        all h: Habitat | h.wolfPop = Medium
        all h: Habitat  | h.elkPop  = Medium
        all h: Habitat | h.vegLevel = Medium
    }
} for exactly 2 Habitat
//wolves and veg are overpopulated 
run  {
    validTrace
    eventually {
        all h: Habitat | h.wolfPop = Overpopulated
        all h: Habitat  | h.elkPop  = Empty
        all h: Habitat | h.vegLevel = Overpopulated
    }
} for exactly 2 Habitat

//all overpopulated - unsats, showing that they all feed on each other and can't grow without the other
run  {
    validTrace
    eventually {
        all h: Habitat | h.wolfPop = Overpopulated
        all h: Habitat  | h.elkPop  = Overpopulated
        all h: Habitat | h.vegLevel = Overpopulated
    }
} for exactly 2 Habitat

//Everything extinct, should be UNSAT! - if we had lifespans it would be theoritcally possible
run  {
    validTrace
    eventually {
        all h: Habitat | h.wolfPop = Empty
        all h: Habitat  | h.elkPop  = Empty
        all h: Habitat | h.vegLevel = Empty
    }
} for exactly 2 Habitat
//more runs possible...





//CHEAT SHEET (for use without custom visualizer):
// elkGrow:              elkPop↑, vegLevel↓, wolfPop unchanged          (requires: wolfPop=Empty, vegLevel!=Empty, elkPop!=Overpopulated)
// elkReproduce:         elkPop↑, vegLevel↓, wolfPop unchanged          (requires: vegLevel=High or Overpopulated, elkPop!=Overpopulated)
// wolfPredation:        elkPop↓, wolfPop↑, vegLevel unchanged          (requires: wolfPop!=Empty, elkPop!=Empty)
// vegetationRecover:    vegLevel↑, elkPop unchanged, wolfPop unchanged  (requires: elkPop!=Overpopulated, vegLevel!=Overpopulated)
// elkDegradeVegetation: vegLevel↓, elkPop unchanged, wolfPop unchanged  (requires: elkPop=Overpopulated, vegLevel!=Empty)
// wolfStarve:           wolfPop↓, elkPop unchanged, vegLevel unchanged  (requires: elkPop=Empty, wolfPop!=Empty)
// reintroduceWolves:    wolfPop Empty→Low, elkPop unchanged, vegLevel unchanged (requires: ALL habitats have wolfPop=Empty, fires only once)
// wolfMigrate:          wolfPop↓ in h1, wolfPop↑ in h2, elk+veg unchanged in both  (requires: h1.elkPop=Low or Empty, h2.wolfPop=Empty, habitats adjacent)
// elkDisperse:          elkPop↓ in h1, elkPop↑ in h2, vegLevel↓ in h2, veg unchanged in h1  (requires: h1.elkPop!=Empty or Low, h1.vegLevel=Medium/Low/Empty, h2.elkPop!=Overpopulated, habitats adjacent)
// doNothing:            everything unchanged in all habitats