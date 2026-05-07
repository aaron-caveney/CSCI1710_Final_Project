#lang forge/temporal

// Alternative Stable States
    // Inspired by Colorado State Research Paper (2024) on returning tophic cascade versus actually restoring the ecosystem. 

// Core Finding: 
    // Wolf reintroduction suppresses elk (trophic cascade works)
    // Stream incision + beaver-willow feedback create an alternative stable state
    // Ecosystem doesn't fully recover (hystersis since ecosystem is trapped)
    // Environmental conditions (stream depth, water table) prevent reversal

// Key Ideas:
    // Degradation (stream incision, deep water tables) breaks
        // the beaver-willow mutualism, creating a self-reinforcing trap:
    //   No tall willows means beavers can't be present
    //   No beavers → no dams → water table stays deep
    //   Deep water table → willows can't establish
    //   Result: System stuck in degraded state even tho elk suppression works


// Sigs

abstract sig PopLevel {}
one sig Empty, Low, Medium, High, Overpopulated extends PopLevel {}

sig Habitat {
    adjacent: set Habitat,
    
    // Populations
    var wolfPop: one PopLevel,
    var elkPop: one PopLevel,
    var vegLevel: one PopLevel,
    
    // Changing environmental state (the hystersis)
    var degraded: one Int,           // 0 = restored, 1 = stream-incised
    var waterTableDepth: one Int,    // 0 = shallow, 1 = deep (bad)
    
    // Ecosystem engineering (beaver-willow relationship)
    var beaverPresent: one Int,      // 0 = no beavers, 1 = beavers active
    var damPresent: one Int          // 0 = no dam, 1 = dam present
}
// Pop Lvl Helper Preds

pred nextLevel[p: PopLevel, q: PopLevel] {
    (p = Empty       and q = Low)              or
    (p = Low         and q = Medium)           or
    (p = Medium      and q = High)             or
    (p = High        and q = Overpopulated)    or
    (p = Overpopulated and q = Overpopulated)
}

pred prevLevel[p: PopLevel, q: PopLevel] {
    (p = Overpopulated and q = High)   or
    (p = High          and q = Medium) or
    (p = Medium        and q = Low)    or
    (p = Low           and q = Empty)  or
    (p = Empty         and q = Empty)
}

// Frame Preds

pred frameOthersExcept[h1: Habitat] {
    all h: Habitat | h != h1 implies {
        h.wolfPop'      = h.wolfPop
        h.elkPop'       = h.elkPop
        h.vegLevel'     = h.vegLevel
        h.degraded'     = h.degraded
        h.waterTableDepth' = h.waterTableDepth
        h.beaverPresent' = h.beaverPresent
        h.damPresent'   = h.damPresent
    }
}

pred frameOthersExcept2[h1: Habitat, h2: Habitat] {
    all h: Habitat | (h != h1 and h != h2) implies {
        h.wolfPop'      = h.wolfPop
        h.elkPop'       = h.elkPop
        h.vegLevel'     = h.vegLevel
        h.degraded'     = h.degraded
        h.waterTableDepth' = h.waterTableDepth
        h.beaverPresent' = h.beaverPresent
        h.damPresent'   = h.damPresent
    }
}


// Beaver + Willow Preds


// Beavers colonize when conditions allow: tall willows and water accessible
pred beaverColonization[h: Habitat] {
    h.beaverPresent = 0                    // no beavers yet
    h.vegLevel = High or h.vegLevel = Overpopulated  // tall willows available
    h.elkPop != Overpopulated              // not being completely destroyed
    h.waterTableDepth = 0                  // water table is shallow enough
    h.beaverPresent' = 1                   // beavers back
    h.damPresent' = 1                      // they build a dam
    h.waterTableDepth' = 0                 // dam maintains shallow water
    h.vegLevel' = h.vegLevel               // willows don't change
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.degraded' = h.degraded
    frameOthersExcept[h]
}

// Beavers leave when willows become too short to support them
pred beaverAbandon[h: Habitat] {
    h.beaverPresent = 1                    // beavers present
    h.vegLevel = Low or h.vegLevel = Empty // willows too short/depleted
    h.beaverPresent' = 0                   // beavers leave
    h.damPresent' = 0                      // dams fall without beavers
    h.waterTableDepth' = 1                 // water table drops, deep streams
    h.vegLevel' = h.vegLevel
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.degraded' = 1                        // stream incision = physical degradation
    frameOthersExcept[h]
}

// Stream Degradtion Preds

// Stream incision occurs when beavers absent and elk are destroying everything
pred streamIncision[h: Habitat] {
    h.beaverPresent = 0                    // no beaver dams to keep water
    h.elkPop = Overpopulated               // extreme browsing = damage
    h.degraded = 0                         // not yet incised
    h.waterTableDepth = 0                  // water table not yet deep
    h.waterTableDepth' = 1                 // streams begin to incise
    h.degraded' = 1                        // physical degradation starts
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.vegLevel' = h.vegLevel
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Water table recovers naturally over time (slowly) or with beaver dams (quickly)
pred waterTableRestore[h: Habitat] {
    h.waterTableDepth = 1                  // water table currently deep (incised)
    h.beaverPresent = 1                    // beavers present with functioning dam
    h.damPresent = 1
    h.waterTableDepth' = 0                 // dam raises water table rapidly
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.vegLevel' = h.vegLevel
    h.degraded' = h.degraded
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Very slow natural water table recovery (without beavers/dams)
// This requires no beavers and represents natural groundwater processes
pred waterTableRestoreSlow[h: Habitat] {
    h.waterTableDepth = 1                  // water table currently deep
    h.beaverPresent = 0                    // no beavers (very slow recovery)
    // Allow recovery even in degraded habitats via natural processes
    h.waterTableDepth' = 0                 // slowly recovers (rare transition)
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.vegLevel' = h.vegLevel
    h.degraded' = h.degraded
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Vegetation Dyanmics (from existing model and adding extension))

// Elk growth when wolves absent
pred elkGrow[h: Habitat] {
    h.wolfPop = Empty                      // no predation
    h.elkPop != Overpopulated              // not already at max
    h.vegLevel != Empty                    // food available
    nextLevel[h.elkPop, h.elkPop']         // elk increase
    h.vegLevel' = h.vegLevel               // vegetation unchanged by this transition
    h.wolfPop' = h.wolfPop
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Vegetation degradation from overpopulated elk
pred vegDegradation[h: Habitat] {
    h.elkPop = Overpopulated               // massive browsing pressure
    h.vegLevel != Empty                    // vegetation still present
    prevLevel[h.vegLevel, h.vegLevel']     // vegetation decreases
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Vegetation recovery when water table shallow and browsing low
pred vegRecoveryShallow[h: Habitat] {
    h.waterTableDepth = 0                  // water table shallow (good for willows)
    h.elkPop != Overpopulated              // not being heavily browsed
    h.vegLevel != Overpopulated
    nextLevel[h.vegLevel, h.vegLevel']     // vegetation increases
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Vegetation recovery when water table deep (very difficult, requires low elk)
// This models the alternative pathway where recovery is extremely slow
pred vegRecoveryDeep[h: Habitat] {
    h.waterTableDepth = 1                  // water table deep (hard for willows)
    h.elkPop = Empty                       // must have absolutely zero elk pressure
    h.vegLevel != Overpopulated
    nextLevel[h.vegLevel, h.vegLevel']     // recovery, but only at Empty elk
    h.wolfPop' = h.wolfPop
    h.elkPop' = h.elkPop
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}


// Predator Dynamics


// Wolf predation
pred wolfPredation[h: Habitat] {
    h.wolfPop != Empty                     // wolves present
    h.elkPop != Empty                      // elk present
    prevLevel[h.elkPop, h.elkPop']         // elk suppressed
    nextLevel[h.wolfPop, h.wolfPop']       // wolves thrive
    h.vegLevel' = h.vegLevel
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Wolf starvation when no elk
pred wolfStarve[h: Habitat] {
    h.elkPop = Empty                       // no food
    h.wolfPop != Empty                     // wolves present
    prevLevel[h.wolfPop, h.wolfPop']       // wolves decline
    h.elkPop' = h.elkPop
    h.vegLevel' = h.vegLevel
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}

// Wolf migration to adjacent habitat
pred wolfMigrate[h1: Habitat, h2: Habitat] {
    h2 in h1.adjacent
    h1.wolfPop != Empty
    h2.wolfPop = Empty
    h2.wolfPop' = h1.wolfPop
    h1.wolfPop' = Empty
    h1.elkPop'  = h1.elkPop
    h1.vegLevel' = h1.vegLevel
    h1.degraded' = h1.degraded
    h1.waterTableDepth' = h1.waterTableDepth
    h1.beaverPresent' = h1.beaverPresent
    h1.damPresent' = h1.damPresent
    h2.elkPop'  = h2.elkPop
    h2.vegLevel' = h2.vegLevel
    h2.degraded' = h2.degraded
    h2.waterTableDepth' = h2.waterTableDepth
    h2.beaverPresent' = h2.beaverPresent
    h2.damPresent' = h2.damPresent
    frameOthersExcept2[h1, h2]
}

// Wolf reintroduction (external intervention)
pred reintroduceWolves[h: Habitat] {
    h.wolfPop = Empty
    h.wolfPop' = Low
    h.elkPop' = h.elkPop
    h.vegLevel' = h.vegLevel
    h.degraded' = h.degraded
    h.waterTableDepth' = h.waterTableDepth
    h.beaverPresent' = h.beaverPresent
    h.damPresent' = h.damPresent
    frameOthersExcept[h]
}


pred doNothing {
    all h: Habitat | {
        h.wolfPop'      = h.wolfPop
        h.elkPop'       = h.elkPop
        h.vegLevel'     = h.vegLevel
        h.degraded'     = h.degraded
        h.waterTableDepth' = h.waterTableDepth
        h.beaverPresent' = h.beaverPresent
        h.damPresent'   = h.damPresent
    }
}

// Step and Trace

pred step {
    some h: Habitat, h2: Habitat | {
        // Beaver-willow feedback
        beaverColonization[h]         or
        beaverAbandon[h]              or
        // Hydrologic dynamics (slowly-changing)
        streamIncision[h]             or
        waterTableRestore[h]          or
        waterTableRestoreSlow[h]      or
        // Vegetation
        elkGrow[h]                    or
        vegDegradation[h]             or
        vegRecoveryShallow[h]         or
        vegRecoveryDeep[h]            or
        // Predators
        wolfPredation[h]              or
        wolfStarve[h]                 or
        reintroduceWolves[h]          or
        wolfMigrate[h, h2]
    } or doNothing
}

pred init {
    all h: Habitat | {
        h.wolfPop = Empty              // no wolves (pre-reintroduction)
        h.elkPop = Overpopulated       // elk at high levels
        h.vegLevel = Low               // vegetation suppressed by overbrowsing
        h.beaverPresent = 0            // no beavers (they already left)
        h.damPresent = 0               // no functioning dams
        h.waterTableDepth = 1          // water table deep (streams incised)
        h.degraded = 1                 // habitat physically degraded
    }
}

pred validTrace {
    init
    always step
}

// Helper Preds

pred wolvesReintroduced {
    some h: Habitat | h.wolfPop != Empty
}

pred elkSuppressed {
    all h: Habitat | h.elkPop = Low or h.elkPop = Empty or h.elkPop = Medium
}

pred beaversRestored {
    some h: Habitat | h.beaverPresent = 1
}

pred waterRestored {
    some h: Habitat | h.waterTableDepth = 0
}

pred vegetationRecovered {
    all h: Habitat | h.vegLevel = Medium or h.vegLevel = High
}

pred vegetationSupressed {
    all h: Habitat | h.vegLevel = Low or h.vegLevel = Empty
}

pred habitatDegraded {
    some h: Habitat | h.degraded = 1 and h.waterTableDepth = 1
}

pred allHabitatsRestored {
    all h: Habitat | h.degraded = 0
}

pred beaverWillowMutualismActive {
    some h: Habitat | h.beaverPresent = 1 and h.vegLevel = High
}

pred hysteresisLocked {
    some h: Habitat | 
        h.degraded = 1 and 
        h.waterTableDepth = 1 and 
        h.beaverPresent = 0 and 
        h.vegLevel = Low
}

// Scenarios to demonstrate alternative stable states

option max_tracelength 30

// SCENARIO 1: Simple Trophic Cascade
run {
    validTrace
    eventually {
        wolvesReintroduced
        eventually {
            all h: Habitat | h.elkPop = Low or h.elkPop = Medium
            all h: Habitat | h.vegLevel = High
        }
    }
} for 2 Habitat

// SCENARIO 2: Hysteresis Trap - Restoration Fails
run {
    validTrace
    eventually {
        wolvesReintroduced
        eventually {
            some h: Habitat | h.elkPop = Low or h.elkPop = Empty
            some h: Habitat | h.degraded = 1 and h.waterTableDepth = 1
            eventually {
                always {
                    some h: Habitat | h.vegLevel = Low  // vegetation stays suppressed
                    some h: Habitat | h.beaverPresent = 0  // no beaver return
                }
            }
        }
    }
} for 2 Habitat

// SCENARIO 3: Different Fates
run {
    validTrace
    eventually {
        wolvesReintroduced
        eventually {
            // At least one habitat escapes: water restores, beavers colonize, veg recovers (with wolves)
            (some h1: Habitat | 
                h1.wolfPop != Empty and
                h1.waterTableDepth = 0 and 
                h1.beaverPresent = 1 and 
                h1.vegLevel = High) 
            and
            // At least one habitat stays trapped: incised, no beavers, veg suppressed (also has wolves)
            (some h2: Habitat | 
                h2.wolfPop != Empty and
                h2.degraded = 1 and 
                h2.waterTableDepth = 1 and 
                h2.beaverPresent = 0 and 
                h2.vegLevel = Low)
        }
    }
} for 3 Habitat
