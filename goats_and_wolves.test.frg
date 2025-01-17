#lang forge/temporal
open "goats_and_wolves.frg"

//// Do not edit anything above this line ////
pred checkValidAnimalPosition1 {
    all m: GWPosition.gw | {
        GWBoat.gwlocation = GWNear or GWBoat.gwlocation = GWFar
        m in GWFar.gw <=> m not in GWNear.gw}
}
pred checkValidAnimalPosition2 {
    all m: GWPosition.gw | {
        GWBoat.gwlocation = GWNear or GWBoat.gwlocation = GWFar
        m in GWFar.gw <=> m not in GWNear.gw
    }
}
pred checkValidGWBoatPosition1{
    all m: GWPosition.gw | {
        GWBoat.gwlocation = GWNear <=> GWBoat.gwlocation != GWFar
        m in GWNear.gw <=> m not in GWFar.gw 
        m in GWFar.gw <=> m not in GWNear.gw
    }
}
pred checkValidGWBoatPosition2 {
    all m: GWPosition.gw | {
        GWBoat.gwlocation != GWNear <=> GWBoat.gwlocation = GWFar
        m in GWNear.gw <=> m not in GWFar.gw 
        m in GWFar.gw <=> m not in GWNear.gw
    }
}
test suite for GWvalidState {
    // If you have tests for this predicate, put them here!
    assert checkValidAnimalPosition1 is necessary for GWvalidState
    assert checkValidAnimalPosition2 is necessary for GWvalidState
    assert checkValidGWBoatPosition1 is necessary for GWvalidState
    assert checkValidGWBoatPosition2 is necessary for GWvalidState
    test expect {
        checkInvalidAnimalPosition: {
            GWvalidState
            (some disj m, n: GWPosition.gw | {
                GWBoat.gwlocation = GWNear or GWBoat.gwlocation = GWFar
                m in GWNear.gw
                m not in GWFar.gw 
                n in GWFar.gw
                n in GWNear.gw
            })
        } is unsat
        checkInvalidGWBoatPosition: {
            GWvalidState
            (some disj m, n: GWPosition.gw | {
                GWBoat.gwlocation = GWNear and GWBoat.gwlocation = GWFar
                m in GWNear.gw
                m not in GWFar.gw 
                n in GWFar.gw
                n not in GWNear.gw
            })
        } is unsat
        simpleValidsameSide: {
            GWvalidState
            some disj a1, a2, a3: GWAnimal | {
                GWBoat.gwlocation = GWNear
                (a1+a2+a3) in GWNear.gw
            }   
        } is sat
        simpleValidDiffSides: {
            GWvalidState
            some disj a1, a2, a3: GWAnimal | {
                GWBoat.gwlocation = GWFar
                (a1) in GWNear.gw
                (a2+a3) in GWFar.gw
            }   
        } is sat
        testVacuoty: {
            GWvalidState
        } is sat
    }
    
}
pred inNear{
    all m: GWAnimal | {
        GWBoat.gwlocation = GWNear
        m in GWNear.gw <=> m not in GWFar.gw
    }
}
pred notInFar{
    all m: GWAnimal | {
        GWBoat.gwlocation != GWFar
        m not in GWFar.gw
    }
}
pred notInitYet{
    (#{a: GWAnimal | a in GWFar.gw} > 0) => not GWinitState
}
test suite for GWinitState {
    // If you have tests for this predicate, put them here!
    assert inNear is necessary for GWinitState
    assert notInFar is necessary for GWinitState
    assert notInitYet is necessary for GWinitState
    test expect{
        notInit: {
            not GWinitState 
            some m, n: GWAnimal | {
                m in GWFar.gw
                n in GWNear.gw
            }
        }is sat
        isInit: {
            GWinitState 
            all disj m, n, b: GWAnimal | {
                (m+n+b) in GWNear.gw 
                (m+n+b) not in GWFar.gw
            }
        }is sat
        isInit2: {
            not GWinitState 
            all disj m, n, b: GWAnimal | {
                (m+n+b) not in GWNear.gw 
                (m+n+b) in GWFar.gw
            }
        }is sat
        testVacuoty2: {
            GWinitState
        } is sat
        isNotInit: {
            GWinitState 
            some disj m, n, b: GWAnimal | {
                GWBoat.gwlocation = GWNear
                (m+n+b) not in GWNear.gw 
                (m+n+b) in GWFar.gw
            }
        }is unsat
        isNotInit2: {
            GWinitState 
            some disj m, n, b: GWAnimal | {
                (m+n+b) in GWNear.gw 
                (m+n+b) not in GWFar.gw
                GWBoat.gwlocation = GWFar
            }
        }is unsat
    }
}
pred  checkInFar {
    all m: GWAnimal | {
        m in GWFar.gw <=> m not in GWNear.gw
    }
}
pred checkNotInNear {
    #{a: GWAnimal | a in GWNear.gw} = 0
    //#{a: GWAnimal | a in GWFar.gw} >= 0
}
pred notInFinalYet {
     #{a: GWAnimal | a in GWNear.gw} > 0 implies not GWfinalState
}
test suite for GWfinalState {
    // If you have tests for this predicate, put them here!
    assert checkInFar is necessary for GWfinalState
    assert checkNotInNear is necessary for GWfinalState
    assert notInFinalYet is necessary for GWfinalState
    test expect{
        validFinalSat: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                no GWNear.gw
                (g1 + g2 + g3 + w1 + w2 + w3) in GWFar.gw
            }
            GWfinalState
        } is sat
        validTransitionSat: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                GWNear.gw = (w2 + w3)
                GWFar.gw = (g1 + g2 + g3 + w1)
                GWNear.gw' =  GWNear.gw - (w2 + w3)
                GWFar.gw' = GWFar.gw + (w2 + w3)
                next_state{GWfinalState}
            }
        } is sat
        testVacuoty3: {
            GWfinalState
        } is sat
         validFinalUNSAT: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                no GWFar.gw
                (g1 + g2 + g3 + w1 + w2 + w3) in GWNear.gw
            }
            GWfinalState
        } is unsat
        validTransitionUNSAT: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                GWNear.gw = (w2 + w3)
                GWFar.gw = (g1 + g2 + g3 + w1)
                GWNear.gw' =  GWNear.gw + (w1)
                GWFar.gw' = GWFar.gw - (w1)
                next_state{GWfinalState}
            }
        } is unsat
        invalidFinal: {
            some m: GWAnimal | m in GWNear.gw and GWfinalState
        } is unsat
        invalidFinal2: {
            some m: GWAnimal | #{a: GWAnimal | a in GWFar.gw} = 0 and GWfinalState
        } is unsat
    }
}
test suite for GWmove {
    // If you have tests for this predicate, put them here!
    test expect{
        testGWBoatPositionProperty: {
            all to, from: GWPosition | {
                GWmove[to, from] => ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = to)) 
            }
        } is theorem
        testAnimalPositionProperty: {
            all to, from: GWPosition | {
                GWmove[to, from] => {
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw 
                        (m+n) not in from.gw'
                        (m+n) in to.gw'}
                } 
            }
        } is theorem
        testAnimalGWBoatPositionProperty: {
            all to, from: GWPosition | {
                GWmove[to, from] => {
                    ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = to))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) in to.gw'}
                } 
            }
        } is theorem
        testStrictOneAnimalPositionProperty: {
            all to, from: GWPosition | {
                GWmove[to, from] => {
                    ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = to))
                    some m: GWAnimal | {
                        (m) in from.gw 
                        (m) not in to.gw
                        (m) not in from.gw'
                        (m) in to.gw'}
                } 
            }
        } is theorem
        testVacuoty5: {
            some t, f: GWPosition | GWmove[t,f]
        } is sat
        testGWBoatDoesntMove: {
            all disj to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
            }
        } is unsat
        testGWBoatDoesntMoveButgwDo: {
            all disj to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) in to.gw'}
            }    
        } is unsat
        testgwDontMove: {
            all to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) not in to.gw'}
            }    
        } is unsat
        testgwDontLeave: {
            all to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
                    some m,n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n)  in from.gw'
                        (m+n)  in to.gw'}
            }    
        } is unsat
    } 
}

pred checkNearEating {
    (some g: Goat | g in GWNear.gw) implies 
    not (#{s: Goat | s in GWNear.gw} < #{w: Wolf | w in GWNear.gw})
}
pred checkFarEating {
    (some g: Goat | g in GWFar.gw) implies 
    not (#{s: Goat | s in GWFar.gw} < #{w: Wolf | w in GWFar.gw})
}
pred checkAlwaysNeverEating {
    always {GWneverEating} => (checkNearEating and checkFarEating)
}

test suite for GWneverEating {  
    assert checkNearEating is necessary for GWneverEating
    assert checkFarEating is necessary for GWneverEating
    assert checkAlwaysNeverEating is necessary for GWneverEating
    test expect {
        testVacuoty6: {
            GWneverEating
        } is sat
        neverEatingTest : {
            some g: Goat | some w: Wolf | {
                GWNear.gw = g + w
                no GWFar.gw
                GWneverEating
            }
        } is sat
        neverEatingTestSanity : {
            some g: Goat | some w: Wolf | {
                GWNear.gw = g 
                GWFar.gw =  w
                GWneverEating
            }
        } is sat
        testNeverEating: {
            some g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g1 + g2 + g3
                GWFar.gw = w1 + w2 + w3
                GWneverEating
            }
        } is sat 
        testNeverEating2: {
            some g1, g2, g3: Goat | some w1,w2,w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g3 + w2
                GWFar.gw = w1 + w3 + g1 + g2
                GWneverEating
            }
        } is sat

        //ask why disjoing doesnt work

        testNeverEating3: {
            some  g1, g2, g3: Goat | some  w1, w2, w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g3 + w2 + w3 + g1 + g2
                GWFar.gw = w1 
                GWneverEating
            }
        } is sat
        testNeverEating4: {
            some g1, g2, g3: Goat | some  w1,w2,w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g3 + w2 + w3 
                GWFar.gw = w1 + g1 + g2
                not GWneverEating
            }
        } is sat
        someEatingTest : {
            some g1, g2: Goat | some w1, w2: Wolf | {
                -- ensuring we have disjoint goats/wolves
                g1 != g2
                w1 != w2
                
                -- state 1
                GWNear.gw = g1 + g2 + w1 + w2
                no GWFar.gw
                GWBoat.gwlocation = GWNear

                --state 2
                GWNear.gw' = g2 + w1 + w2
                GWFar.gw' = g1
                GWBoat.gwlocation' = GWFar

                -- predicate that we're testing
                always GWneverEating
            }
        } is unsat
        neverEatingTestUNSAT: {
            some g: Goat | some w1, w2: Wolf | {
                w1 != w2
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                GWNear.gw = g + w1
                GWFar.gw = w2
                no GWNear.gw' 
                GWFar.gw' = w2 + g + w1
                always {GWneverEating}
            }
        } is unsat
        testNeverEatingUNSAT: {
            some g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g1
                w1 != w2
                w2 != w3
                w3 ! = w1
                GWNear.gw = g1 + g2 + g3
                GWFar.gw = w1 + w2 + w3
                GWNear.gw' = g1
                GWFar.gw' = w1 + w2 + w3 + g2 + g3
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                always {GWneverEating}
            }
        } for exactly 6 GWAnimal, exactly 3 Goat, exactly 3 Wolf is unsat 
        testNeverEating2UNSAT: {
            some g1, g2, g3: Goat | some w1,w2,w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g1
                w1 != w2
                w2 != w3
                w3 ! = w1
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                GWNear.gw = g3 
                GWFar.gw = w1 + w3 + g1 + g2+ w2
                GWneverEating
            }
        } for exactly 6 GWAnimal, exactly 3 Goat, exactly 3 Wolf is unsat
        testNeverEating3UNSAT: {
            some  g1, g2, g3: Goat | some  w1, w2, w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g1
                w1 != w2
                w2 != w3
                w3 ! = w1
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                GWNear.gw = g3 + w2 + w3 + g1 + g2
                GWFar.gw = w1 
                GWNear.gw' = g3 + w2 + w3
                GWFar.gw' = w1 + g1 + g2
                always {GWneverEating}
            }
        } for exactly 6 GWAnimal, exactly 3 Goat, exactly 3 Wolf is unsat
        testNeverEating4UNSAT: {
            some g1, g2: Goat | some  w1,w2,w3: Wolf | {
                g1 != g2
                w1 != w2
                w2 != w3
                w3 ! = w1
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                GWNear.gw = g1 + g2 + w1 + w2 + w3 
                no GWFar.gw
                GWneverEating
            }
        } for exactly 6 GWAnimal, exactly 2 Goat, exactly 3 Wolf is unsat 
    }
    // If you have any more tests for this predicate, put them here!
}
pred moveGood {
    always{GWvalidState}
    GWinitState
    GWmove[GWFar, GWNear]
    always{GWneverEating}
}
pred initValid {
    GWinitState 
    GWvalidState
   
}
pred finalValid {
    GWfinalState implies GWvalidState
}
pred moveToFinal {
    always{GWvalidState}
    GWmove[GWFar, GWNear]
    eventually {GWfinalState}
    always{GWneverEating}
}

pred initNeverSteal {
    GWinitState
    neverStealing
}

pred finalNeverEat {
    GWfinalState implies GWneverEating
}
test suite for GWtraces {
    // If you have tests for this predicate, put them here!
    test expect {
        testVacuoty7: {
            GWtraces
        } is sat
        checkInvalidAnimalPositionTraces: {
            GWvalidState
            (some disj m, n: GWPosition.gw | {
                GWBoat.gwlocation = GWNear or GWBoat.gwlocation = GWFar
                m in GWNear.gw
                m not in GWFar.gw 
                n in GWFar.gw
                n in GWNear.gw
            })
        } is unsat
        checkInvalidGWBoatPositionTraces: {
            GWvalidState
            (some disj m, n: GWPosition.gw | {
                GWBoat.gwlocation = GWNear and GWBoat.gwlocation = GWFar
                m in GWNear.gw
                m not in GWFar.gw 
                n in GWFar.gw
                n not in GWNear.gw
            })
        } is unsat
        simpleValidsameSideTraces: {
            GWvalidState
            some disj a1, a2, a3: GWAnimal | {
                GWBoat.gwlocation = GWNear
                (a1+a2+a3) in  GWNear.gw
            }   
        } is sat
        simpleValidDiffSidesTraces: {
            GWvalidState
            some disj a1, a2, a3: GWAnimal | {
                GWBoat.gwlocation = GWFar
                (a1) in GWNear.gw
                (a2+a3) in GWFar.gw
            }   
        } is sat
        isNotInitTraces: {
            GWinitState 
            some disj m, n, b: GWAnimal | {
                GWBoat.gwlocation = GWNear
                (m+n+b) not in GWNear.gw 
                (m+n+b) in GWFar.gw
            }
        }is unsat
        isNotInit2Traces: {
            GWinitState 
            some disj m, n, b: GWAnimal | {
                (m+n+b) in GWNear.gw 
                (m+n+b) not in GWFar.gw
                GWBoat.gwlocation = GWFar
            }
        }is unsat
        isInitTraces: {
            GWinitState 
            all disj m, n, b: GWAnimal | {
                (m+n+b) in GWNear.gw 
                (m+n+b) not in GWFar.gw
            }
        }is sat
        isInit2Traces: {
            not GWinitState 
            all disj m, n, b: GWAnimal | {
                (m+n+b) not in GWNear.gw 
                (m+n+b) in GWFar.gw
            }
        }is sat
        validFinalSatTRaces: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                no GWNear.gw
                (g1 + g2 + g3 + w1 + w2 + w3) in GWFar.gw
            }
            GWfinalState
        } is sat
        validTransitionSatTRaces: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                GWNear.gw = (w2 + w3)
                GWFar.gw = (g1 + g2 + g3 + w1)
                GWNear.gw' =  GWNear.gw - (w2 + w3)
                GWFar.gw' = GWFar.gw + (w2 + w3)
                next_state{GWfinalState}
            }
        } is sat
        validFinalUNSATTraces: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                no GWFar.gw
                (g1 + g2 + g3 + w1 + w2 + w3) in GWNear.gw
            }
            GWfinalState
        } is unsat
        validTransitionUNSATTraces: {
            some disj g1, g2, g3: Goat | some w1, w2, w3: Wolf | {
                GWNear.gw = (w2 + w3)
                GWFar.gw = (g1 + g2 + g3 + w1)
                GWNear.gw' =  GWNear.gw + (w1)
                GWFar.gw' = GWFar.gw - (w1)
                next_state{GWfinalState}
            }
        } is unsat
        testGWBoatDoesntMoveButgwDoTraces: {
            all disj to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) in to.gw'}
            }    
        } is unsat
        testgwDontMoveTraces: {
            all to, from: GWPosition | {
                GWmove[to, from]  
                ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = from))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) not in to.gw'}
            }    
        } is unsat
        testAnimalGWBoatPositionPropertyTraces: {
            all to, from: GWPosition | {
                GWmove[to, from] => {
                    ((GWBoat.gwlocation = from) <=> (GWBoat.gwlocation' = to))
                    some m, n: GWAnimal | {
                        (m+n) in from.gw 
                        (m+n) not in to.gw
                        (m+n) not in from.gw'
                        (m+n) in to.gw'}
                } 
            }
        } is theorem
        testNeverEating3Traces: {
            some  g1, g2, g3: Goat | some  w1, w2, w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g3 + w2 + w3 + g1 + g2
                GWFar.gw = w1 
                GWneverEating
            }
        } is sat
        testNeverEating4TRaces: {
            some g1, g2, g3: Goat | some  w1,w2,w3: Wolf | {
                g1 != g2
                g2 != g3
                g3 ! = g2
                w1 != w2
                w2 != w3
                w3 ! = w2
                GWNear.gw = g3 + w2 + w3 
                GWFar.gw = w1 + g1 + g2
                not GWneverEating
            }
        } is sat
        someEatingTestTRaces: {
            some g1, g2: Goat | some w1, w2: Wolf | {
                -- ensuring we have disjoint goats/wolves
                g1 != g2
                w1 != w2
                
                -- state 1
                GWNear.gw = g1 + g2 + w1 + w2
                no GWFar.gw
                GWBoat.gwlocation = GWNear

                --state 2
                GWNear.gw' = g2 + w1 + w2
                GWFar.gw' = g1
                GWBoat.gwlocation' = GWFar

                -- predicate that we're testing
                always GWneverEating
            }
        } is unsat
        neverEatingTestUNSATTraces: {
            some g: Goat | some w1, w2: Wolf | {
                w1 != w2
                GWBoat.gwlocation = GWNear
                GWBoat.gwlocation' = GWFar
                GWNear.gw = g + w1
                GWFar.gw = w2
                no GWNear.gw' 
                GWFar.gw' = w2 + g + w1
                always {GWneverEating}
            }
        } is unsat
    }

}
