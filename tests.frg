#lang forge/temporal

open "prototype.frg"

///////////////////////////
// Helpers for Testing
///////////////////////////

pred allWolvesEmpty { 
    all w: Wolf | w.wolfPop = Empty
}

pred allElkOverpopulated {
    all e: Elk | e.elkPop = Overpopulated
}

pred allVegLow {
    all v: Vegetation | v.vegLevel = Low
}

pred coexistenceReached {
    all w: Wolf | w.wolfPop != Empty
    all e: Elk  | e.elkPop = Medium
    all v: Vegetation | v.vegLevel = Medium
}

pred noWolfPopsChange[w: Wolf] {
    w.wolfPop' = w.wolfPop
    w.wolfLocation' = w.wolfLocation
}

pred noElkPopsChange[e: Elk] {
    e.elkPop' = e.elkPop
    e.elkLocation' = e.elkLocation
}

pred noVegChange[v: Vegetation] {
    v.vegLevel' = v.vegLevel
}

pred validPopLevel[p: PopLevel] {
    p = Empty or p = Low or p = Medium or p = High or p = Overpopulated
}


///////////////////////////
// Test Suite: nextLevel
///////////////////////////

test suite for nextLevel {

    // Positive tests — each valid consecutive pair
    test expect { emptyToLow: {
        nextLevel[Empty, Low]
    } is sat }

    test expect { lowToMedium: {
        nextLevel[Low, Medium]
    } is sat }

    test expect { mediumToHigh: {
        nextLevel[Medium, High]
    } is sat }

    test expect { highToOverpopulated: {
        nextLevel[High, Overpopulated]
    } is sat }

    test expect { overpopulatedStays: {
        nextLevel[Overpopulated, Overpopulated]
    } is sat }

    // Negative tests — skipping levels or going backwards
    test expect { emptyToMediumInvalid: {
        nextLevel[Empty, Medium]
    } is unsat }

    test expect { highToLowInvalid: {
        nextLevel[High, Low]
    } is unsat }

    test expect { emptyToOverpopulatedInvalid: {
        nextLevel[Empty, Overpopulated]
    } is unsat }

    test expect { mediumToEmptyInvalid: {
        nextLevel[Medium, Empty]
    } is unsat }
}


///////////////////////////
// Test Suite: prevLevel
///////////////////////////

test suite for prevLevel {

    // Positive tests — each valid decreasing pair
    test expect { overpopulatedToHigh: {
        prevLevel[Overpopulated, High]
    } is sat }

    test expect { highToMedium: {
        prevLevel[High, Medium]
    } is sat }

    test expect { mediumToLow: {
        prevLevel[Medium, Low]
    } is sat }

    test expect { lowToEmpty: {
        prevLevel[Low, Empty]
    } is sat }

    test expect { emptyStaysEmpty: {
        prevLevel[Empty, Empty]
    } is sat }

    // Negative tests — skipping levels or going up
    test expect { emptyToHighInvalid: {
        prevLevel[Empty, High]
    } is unsat }

    test expect { lowToMediumInvalid: {
        prevLevel[Low, Medium]
    } is unsat }

    test expect { overpopulatedToEmptyInvalid: {
        prevLevel[Overpopulated, Empty]
    } is unsat }
}


///////////////////////////
// Test Suite: init
///////////////////////////

test suite for init {

    // Positive tests
    test expect { initIsSat: {
        init
    } is sat }

    test expect { initWolvesEmpty: {
        init
        all w: Wolf | w.wolfPop = Empty
    } is sat }

    test expect { initElkOverpopulated: {
        init
        all e: Elk | e.elkPop = Overpopulated
    } is sat }

    test expect { initVegLow: {
        init
        all v: Vegetation | v.vegLevel = Low
    } is sat }

    // Negative tests
    test expect { initWolfNotEmpty: {
        init
        some w: Wolf | w.wolfPop != Empty
    } is unsat }

    test expect { initElkNotOverpopulated: {
        init
        some e: Elk | e.elkPop != Overpopulated
    } is unsat }

    test expect { initVegNotLow: {
        init
        some v: Vegetation | v.vegLevel != Low
    } is unsat }
}


///////////////////////////
// Test Suite: elkGrow
///////////////////////////

test suite for elkGrow {

    // Positive tests — elk can grow when no wolves present
    test expect { elkGrowSat: {
        some e: Elk | {
            e.elkPop = Low
            no w: Wolf | w.wolfLocation = e.elkLocation and w.wolfPop != Empty
            elkGrow[e]
        }
    } is sat }

    test expect { elkGrowFromEmpty: {
        some e: Elk | {
            e.elkPop = Empty
            no w: Wolf | w.wolfLocation = e.elkLocation and w.wolfPop != Empty
            elkGrow[e]
            e.elkPop' = Low
        }
    } is sat }

    test expect { elkGrowFromMedium: {
        some e: Elk | {
            e.elkPop = Medium
            no w: Wolf | w.wolfLocation = e.elkLocation and w.wolfPop != Empty
            elkGrow[e]
            e.elkPop' = High
        }
    } is sat }

    // Negative tests — elk cannot grow when wolves are present
    test expect { elkDoNotGrowWithWolves: {
        some e: Elk, w: Wolf | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Medium
            elkGrow[e]
        }
    } is unsat }

    // Negative test — overpopulated elk cannot grow further
    test expect { overpopulatedElkCannotGrow: {
        some e: Elk | {
            e.elkPop = Overpopulated
            elkGrow[e]
        }
    } is unsat }
}


///////////////////////////
// Test Suite: wolfPredation
///////////////////////////

test suite for wolfPredation {

    // Positive tests
    test expect { wolfPredationSat: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Low
            e.elkPop = Medium
            wolfPredation[w, e]
        }
    } is sat }

    test expect { wolfPredationElkDrops: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Low
            e.elkPop = High
            wolfPredation[w, e]
            e.elkPop' = Medium
        }
    } is sat }

    test expect { wolfPredationWolfGrows: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Low
            e.elkPop = High
            wolfPredation[w, e]
            w.wolfPop' = Medium
        }
    } is sat }

    // Negative tests — wolf cannot predate with no elk
    test expect { wolfPredationOnEmptyElk: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Medium
            e.elkPop = Empty
            wolfPredation[w, e]
        }
    } is unsat }

    // Negative test — empty wolf cannot predate
    test expect { emptyWolfPredation: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Empty
            e.elkPop = Medium
            wolfPredation[w, e]
        }
    } is unsat }

    // Negative test — wolf in different habitat cannot predate
    test expect { wolfPredationDifferentHabitat: {
        some w: Wolf, e: Elk, h1, h2: Habitat | {
            h1 != h2
            w.wolfLocation = h1
            e.elkLocation = h2
            wolfPredation[w, e]
        }
    } is unsat }
}


///////////////////////////
// Test Suite: elkDegradeVegetation
///////////////////////////

test suite for elkDegradeVegetation {

    // Positive tests
    test expect { elkDegradeVegSat: {
        some e: Elk, v: Vegetation | {
            e.elkLocation = v.vegLocation
            e.elkPop = Overpopulated
            v.vegLevel = High
            elkDegradeVegetation[e, v]
        }
    } is sat }

    test expect { elkDegradeVegDropsLevel: {
        some e: Elk, v: Vegetation | {
            e.elkLocation = v.vegLocation
            e.elkPop = Overpopulated
            v.vegLevel = Medium
            elkDegradeVegetation[e, v]
            v.vegLevel' = Low
        }
    } is sat }

    // Negative tests — only overpopulated elk degrade vegetation
    test expect { nonOverpopulatedElkNoDegrade: {
        some e: Elk, v: Vegetation | {
            e.elkLocation = v.vegLocation
            e.elkPop = High
            v.vegLevel = Medium
            elkDegradeVegetation[e, v]
        }
    } is unsat }

    // Negative test — cannot degrade empty vegetation
    test expect { cannotDegradeEmptyVeg: {
        some e: Elk, v: Vegetation | {
            e.elkLocation = v.vegLocation
            e.elkPop = Overpopulated
            v.vegLevel = Empty
            elkDegradeVegetation[e, v]
        }
    } is unsat }

    // Negative test — elk not in same location as vegetation
    test expect { elkDegradeWrongLocation: {
        some e: Elk, v: Vegetation, h1, h2: Habitat | {
            h1 != h2
            e.elkLocation = h1
            v.vegLocation = h2
            e.elkPop = Overpopulated
            elkDegradeVegetation[e, v]
        }
    } is unsat }
}


///////////////////////////
// Test Suite: wolfStarve
///////////////////////////

test suite for wolfStarve {

    // Positive tests
    test expect { wolfStarveSat: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            e.elkPop = Empty
            w.wolfPop = Medium
            wolfStarve[w, e]
        }
    } is sat }

    test expect { wolfStarveDropsLevel: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            e.elkPop = Empty
            w.wolfPop = High
            wolfStarve[w, e]
            w.wolfPop' = Medium
        }
    } is sat }

    test expect { wolfStarveFromLow: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            e.elkPop = Empty
            w.wolfPop = Low
            wolfStarve[w, e]
            w.wolfPop' = Empty
        }
    } is sat }

    // Negative tests — wolf doesn't starve when elk present
    test expect { wolfDoesNotStarveWithElk: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            e.elkPop = Low
            w.wolfPop = Medium
            wolfStarve[w, e]
        }
    } is unsat }

    // Negative test — empty wolf cannot starve further (already gone)
    test expect { emptyWolfCannotStarve: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            e.elkPop = Empty
            w.wolfPop = Empty
            wolfStarve[w, e]
        }
    } is unsat }
}


///////////////////////////
// Test Suite: wolfMigrate
///////////////////////////

test suite for wolfMigrate {

    // Positive tests
    test expect { wolfMigrateSat: {
        some w: Wolf, h1, h2: Habitat | {
            h1 != h2
            h2 in h1.adjacent
            w.wolfLocation = h1
            wolfMigrate[w]
            w.wolfLocation' = h2
        }
    } is sat }

    test expect { wolfMigratePreservesPopLevel: {
        some w: Wolf, h1, h2: Habitat | {
            h1 != h2
            h2 in h1.adjacent
            w.wolfLocation = h1
            w.wolfPop = Medium
            wolfMigrate[w]
            w.wolfPop' = Medium
        }
    } is sat }

    // Negative tests — wolf cannot migrate to non-adjacent habitat
    test expect { wolfMigrateToNonAdjacent: {
        some w: Wolf, h1, h2: Habitat | {
            h1 != h2
            h2 not in h1.adjacent
            w.wolfLocation = h1
            wolfMigrate[w]
            w.wolfLocation' = h2
        }
    } is unsat }
}


///////////////////////////
// Test Suite: reintroduceWolves
///////////////////////////

test suite for reintroduceWolves {

    // Positive tests
    test expect { reintroduceSat: {
        some w: Wolf, h: Habitat | {
            w.wolfPop = Empty
            reintroduceWolves[w, h]
        }
    } is sat }

    test expect { reintroduceStartsAtLow: {
        some w: Wolf, h: Habitat | {
            w.wolfPop = Empty
            reintroduceWolves[w, h]
            w.wolfPop' = Low
        }
    } is sat }

    test expect { reintroduceSetsLocation: {
        some w: Wolf, h: Habitat | {
            w.wolfPop = Empty
            reintroduceWolves[w, h]
            w.wolfLocation' = h
        }
    } is sat }

    // Negative tests — cannot reintroduce a wolf that isn't empty
    test expect { reintroduceNonEmptyWolf: {
        some w: Wolf, h: Habitat | {
            w.wolfPop = Low
            reintroduceWolves[w, h]
        }
    } is unsat }

    test expect { reintroduceHighWolf: {
        some w: Wolf, h: Habitat | {
            w.wolfPop = High
            reintroduceWolves[w, h]
        }
    } is unsat }
}


///////////////////////////
// Test Suite: doNothing
///////////////////////////

test suite for doNothing {

    // Positive tests
    test expect { doNothingSat: {
        doNothing
    } is sat }

    test expect { doNothingPreservesWolves: {
        doNothing
        all w: Wolf | w.wolfPop' = w.wolfPop and w.wolfLocation' = w.wolfLocation
    } is sat }

    test expect { doNothingPreservesElk: {
        doNothing
        all e: Elk | e.elkPop' = e.elkPop and e.elkLocation' = e.elkLocation
    } is sat }

    test expect { doNothingPreservesVeg: {
        doNothing
        all v: Vegetation | v.vegLevel' = v.vegLevel
    } is sat }

    // Negative tests — doNothing cannot change any population
    test expect { doNothingCannotChangeWolfPop: {
        doNothing
        some w: Wolf | w.wolfPop' != w.wolfPop
    } is unsat }

    test expect { doNothingCannotChangeElkPop: {
        doNothing
        some e: Elk | e.elkPop' != e.elkPop
    } is unsat }

    test expect { doNothingCannotChangeVegLevel: {
        doNothing
        some v: Vegetation | v.vegLevel' != v.vegLevel
    } is unsat }
}


///////////////////////////
// Test Suite: step
///////////////////////////

test suite for step {

    // Positive tests — step is satisfiable
    test expect { stepSat: {
        step
    } is sat }

    // step permits doing nothing
    test expect { stepAllowsDoNothing: {
        step
        doNothing
    } is sat }

    // step permits wolf predation
    test expect { stepAllowsPredation: {
        some w: Wolf, e: Elk | {
            w.wolfLocation = e.elkLocation
            w.wolfPop = Low
            e.elkPop = Medium
            step
            wolfPredation[w, e]
        }
    } is sat }

    // step permits elk growth
    test expect { stepAllowsElkGrow: {
        some e: Elk | {
            e.elkPop = Low
            no w: Wolf | w.wolfLocation = e.elkLocation and w.wolfPop != Empty
            step
            elkGrow[e]
        }
    } is sat }

    // step permits wolf migration
    test expect { stepAllowsMigration: {
        some w: Wolf, h1, h2: Habitat | {
            h1 != h2
            h2 in h1.adjacent
            w.wolfLocation = h1
            step
            wolfMigrate[w]
        }
    } is sat }
}


///////////////////////////
// Test Suite: validTrace
///////////////////////////

test suite for validTrace {

    // Positive tests
    test expect { validTraceSat: {
        validTrace
    } is sat }

    // trace starts with init
    test expect { validTraceStartsWithInit: {
        validTrace
        init
    } is sat }

    // Negative tests — trace must start with correct init conditions
    test expect { validTraceCannotStartWithWolves: {
        validTrace
        some w: Wolf | w.wolfPop != Empty
    } is unsat }

    test expect { validTraceCannotStartWithLowElk: {
        validTrace
        some e: Elk | e.elkPop = Empty
    } is unsat }

    test expect { validTraceCannotStartWithHighVeg: {
        validTrace
        some v: Vegetation | v.vegLevel = High
    } is unsat }
}
