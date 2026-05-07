#lang forge/temporal

open "PROJECT_WORKING.frg"



// Test file for prototype Working Version.frg



test suite for nextLevel {
    // Positive tests

    // these verrifies the next level increases 
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

    // this is max so doesn't increase but stays
    test expect { overpopulatedStays: {
        nextLevel[Overpopulated, Overpopulated] 
        } is sat }

    // Negative tests

    // can't skip a step
    test expect { skipLevelInvalid: {
        nextLevel[Empty, Medium] 
        } is unsat }
    // cnat go backwards
    test expect { goBackwardInvalid: { 
        nextLevel[High, Low] 
        } is unsat }
}

test suite for prevLevel {
    // Positive tests

    // these verify they go backwards correctly and by one step at a time
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

    // lowest level so stays
    test expect { emptyStaysEmpty: { 
        prevLevel[Empty, Empty] 
        } is sat }

    // Negative tests

    // can't skip
    test expect { skipLevelDownInvalid: { 
        prevLevel[High, Low] 
        } is unsat }

    // can't increase
    test expect { goUpwardInvalid: { 
        prevLevel[Low, Medium] 
        } is unsat }
}

test suite for frameOthers {
    // positive
    // the framing predicate successfully keeps all unselected habitats at their exact same population levels
    test expect { frameOthersSat: {
        some h1, h2: Habitat | {
            h1 != h2
            frameOthers[h1]
            h2.elkPop' = h2.elkPop
            h2.wolfPop' = h2.wolfPop
            h2.vegLevel' = h2.vegLevel
        }
    } is sat }

    //negative
    // doing frameOthers makes it impossible for uninvolved habitats to accidentally change their populations.
    test expect { frameOthersPreventsChange: {
        some h1, h2: Habitat | {
            h1 != h2
            frameOthers[h1]
            h2.elkPop' != h2.elkPop 
        }
    } is unsat }

}


// Helper for assertion test
pred isNextElk[h: Habitat] {
    nextLevel[h.elkPop, h.elkPop'] 
}

pred isPrevVeg[h: Habitat] { 
    prevLevel[h.vegLevel, h.vegLevel'] 
}

test suite for elkGrow {

    //positive

    // no wolves and high vegatiation equals growing elk pop
    test expect { elkGrowSat: {
        some h: Habitat | {
            h.wolfPop = Empty
            h.elkPop = Low
            h.vegLevel = High
            elkGrow[h]
            h.elkPop' = Medium
            h.vegLevel' = Medium
        }
    } is sat }

    // negative

    // if there are wolves then elk cant grow 
    test expect { elkCannotGrowWithWolves: {
        some h: Habitat | {
            h.wolfPop = Low
            h.elkPop = Low
            elkGrow[h]
        }
    } is unsat }

    // if elk are overpopulated that is the max and cant keep growing
    test expect { overpopulatedElkCannotGrow: {
        some h: Habitat | {
            h.elkPop = Overpopulated
            elkGrow[h]
        }
    } is unsat }
    

    // no vegitation elk cant grow 
    test expect { elkCannotGrowWithoutVeg: {
        some h: Habitat | {
            h.vegLevel = Empty
            elkGrow[h]
        }
    } is unsat }

    // Assert test
    // if elkGrow that means  a higher elk population
    ElkGrowIncreasesElk: assert all h: Habitat | 
        elkGrow[h] is sufficient for isNextElk[h]
        for exactly 2 Habitat
    // if elkGrow that means a lower veg level
    ElkGrowDecreasesVeg: assert all h: Habitat | 
        elkGrow[h] is sufficient for isPrevVeg[h]
        for exactly 2 Habitat
}

// Assert Helpers
pred isPrevElk[h: Habitat] { 
    prevLevel[h.elkPop, h.elkPop']
}

pred isNextWolf[h: Habitat] {
    nextLevel[h.wolfPop, h.wolfPop'] 
}

pred hasNotEmptyWolf[h: Habitat] { 
    h.wolfPop != Empty 
}

test suite for wolfPredation {
    // positive
    // wolves will increase and elk will decrease when there are elk for the wolves to eat
    test expect { wolfPredationSat: {
        some h: Habitat | {
            h.wolfPop = Low
            h.elkPop = Medium
            wolfPredation[h]
            h.wolfPop' = Medium
            h.elkPop' = Low
            h.vegLevel' = h.vegLevel
        }
    } is sat }

    // no wolves means no wolfPredation can't occur
    test expect { emptyWolfCannotPredate: {
        some h: Habitat | {
            h.wolfPop = Empty
            wolfPredation[h]
        }
    } is unsat }

    // if there are no elk then wolfPredation can't take place
    test expect { wolfCannotPredateEmptyElk: {
        some h: Habitat | {
            h.elkPop = Empty
            wolfPredation[h]
        }
    } is unsat }

    // Assert tests
    PredationDecreasesElk: assert all h: Habitat |
    wolfPredation[h] is sufficient for isPrevElk[h]
    for exactly 2 Habitat

    PredationIncreasesWolf: assert all h: Habitat |
        wolfPredation[h] is sufficient for isNextWolf[h]
        for exactly 2 Habitat

    // Predation requires wolves to exist
    PredationRequiresWolves: assert all h: Habitat |
        wolfPredation[h] is sufficient for hasNotEmptyWolf[h]
        for exactly 2 Habitat
}

test suite for vegetationRecover {

    //positive
    // vegetation grows by one level when elk are not overpopulated
    test expect { vegRecoverSat: {
        some h: Habitat | {
            h.elkPop = Medium
            h.vegLevel = Low
            vegetationRecover[h]
            h.vegLevel' = Medium
        }
    } is sat }

    // vegetation can't increase if elk are overpopulated
    test expect { vegCannotRecoverIfElkOverpopulated: {
        some h: Habitat | {
            h.elkPop = Overpopulated
            vegetationRecover[h]
        }
    } is unsat }


    // vegetation can't increase if already overpopulated 
    test expect { overpopulatedVegCannotRecoverFurther: {
        some h: Habitat | {
            h.vegLevel = Overpopulated
            vegetationRecover[h]
        }
    } is unsat }
}

test suite for elkDegradeVegetation {
    //positive
    // vegitation decreases if elk are overpopulated
    test expect { degradeVegSat: {
        some h: Habitat | {
            h.elkPop = Overpopulated
            h.vegLevel = High
            elkDegradeVegetation[h]
            h.vegLevel' = Medium
        }
    } is sat }

    // negative
    // if elk are not overpopulated then elkDegradeVegetation can't be called 
    test expect { nonOverpopulatedElkCannotDegrade: {
        some h: Habitat | {
            h.elkPop = High
            elkDegradeVegetation[h]
        }
    } is unsat }

    // cant decrease past empty
    test expect { cannotDegradeEmptyVeg: {
        some h: Habitat | {
            h.elkPop = Overpopulated
            h.vegLevel = Empty
            elkDegradeVegetation[h]
        }
    } is unsat }
}

test suite for elkDisperse {

    // positive
    // elk will go from a habitat with high population and low veg to the pther habitat
    // with low population and high veg -> 
   // medium population in both and medium veg in the destination
    test expect { disperseSat: {
        some h1, h2: Habitat | {
            h2 in h1.adjacent
            h1.elkPop = High
            h1.vegLevel = Low
            h2.elkPop = Low
            h2.vegLevel = High
            elkDisperse[h1, h2]
            h1.elkPop' = Medium
            h2.elkPop' = Medium
            h2.vegLevel' = Medium
        }
    } is sat }

    // elk can only travel to directly connected habitats
    test expect { cannotDisperseToNonAdjacent: {
        some h1, h2: Habitat | {
            h2 not in h1.adjacent
            elkDisperse[h1, h2] 
        }
    } is unsat }

    // if a habitat has a low elk pop then the elk can't disperse
    test expect { cannotDisperseIfSourcePopTooLow: {
        some h1, h2: Habitat | {
            h2 in h1.adjacent
            h1.elkPop = Low
            elkDisperse[h1, h2]
        }
    } is unsat }

    // if the a habitat has a high vegitation then elk won't migrate
    test expect { cannotDisperseIfSourceVegAbundant: {
        some h1, h2: Habitat | {
            h2 in h1.adjacent
            h1.elkPop = High
            h1.vegLevel = High // Elk won't leave if food is high
            elkDisperse[h1, h2]
        }
    } is unsat }

}

test suite for wolfStarve {
    // positive
    // if there are no elk but there are wolves then the wolves will decrease in population
    test expect { starveSat: {
        some h: Habitat | {
            h.elkPop = Empty
            h.wolfPop = Medium
            wolfStarve[h]
            h.wolfPop' = Low
        }
    } is sat }

    // negative
    // if there are elk then wolves won't starve
    test expect { wolfDoesNotStarveWithElk: {
        some h: Habitat | {
            h.elkPop = Low
            wolfStarve[h]
        }
    } is unsat }
}

test suite for wolfMigrate {

    // positive
    // wolves go to a habitat that is empty
    test expect { migrateSat: {
        some h1, h2: Habitat | {
            h2 in h1.adjacent
            h1.wolfPop = Medium
            h2.wolfPop = Empty
            wolfMigrate[h1, h2]
            h1.wolfPop' = Low
            h2.wolfPop' = Low
        }
    } is sat }

    // negtive
    // habitat must be adjacant
    test expect { cannotMigrateToNonAdjacent: {
        some h1, h2: Habitat | {
            h2 not in h1.adjacent
            wolfMigrate[h1, h2]
        }
    } is unsat }

    // must be empty to migrate
    test expect { cannotMigrateToOccupiedHabitat: {
        some h1, h2: Habitat | {
            h2 in h1.adjacent
            h2.wolfPop = Low 
            wolfMigrate[h1, h2]
        }
    } is unsat }
}


test suite for reintroduceWolves {

    // positive
    // must have no wolves
    test expect { reintroduceSat: {
        some h: Habitat | {
            h.wolfPop = Empty
            reintroduceWolves[h]
            h.wolfPop' = Low
        }
    } is sat }

    // must have no wolves 
    test expect { cannotReintroduceIfWolvesPresent: {
        some h: Habitat | {
            h.wolfPop = Low
            reintroduceWolves[h]
        }
    } is unsat }
}

// Helper for assert test, this is when no change occurs in the habitat after a step
pred habitatIsUnchanged[h: Habitat] {
    h.elkPop' = h.elkPop
    h.wolfPop' = h.wolfPop
    h.vegLevel' = h.vegLevel
}

test suite for doNothing {
    
    // positive
    // doNothing keeps all habitats the same
    test expect { doNothingSat: {
        doNothing
        all h: Habitat | h.elkPop' = h.elkPop and h.wolfPop' = h.wolfPop and h.vegLevel' = h.vegLevel
    } is sat }

    test expect { doNothingPreventsChange: {
        doNothing
        some h: Habitat | h.elkPop' != h.elkPop
    } is unsat }
    
    // this pred requires nothing to change 
    DoNothingPreservesAll: assert all h: Habitat |
        doNothing is sufficient for habitatIsUnchanged[h]
        for exactly 2 Habitat
}

test suite for step {
    
    // positive
    // anything can be a step so something must happen 
    test expect { stepSat: {
        step
    } is sat }

    test expect { stepAllowsDoNothing: {
        step
        doNothing
    } is sat }
}

test suite for validTrace {

    // positive
    // starting state must have one habitat with this
    test expect { validTraceEnsuresInit: {
        validTrace
        some h: Habitat | h.wolfPop = Empty and h.elkPop = Overpopulated and h.vegLevel = Medium
    } is sat }


    // cant start not with overpopulated elk for everything at state 0
    test expect { validTraceFailsIfInitViolated: {
        validTrace
        all h: Habitat | h.elkPop != Overpopulated
    } is unsat }
}


