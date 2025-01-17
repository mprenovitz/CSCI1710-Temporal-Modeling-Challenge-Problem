#lang forge/temporal

// option max_tracelength 12
// option min_tracelength 12
open "pets_and_owners.frg"

//// Do not edit anything above this line ////

pred checkValidAnimalPosition1 {
    all m: POPosition.po | {
        POBoat.polocation = PONear or POBoat.polocation = POFar
        m in POFar.po <=> m not in PONear.po}
}
pred checkValidAnimalPosition2 {
    all m: POPosition.po | {
        POBoat.polocation = PONear or POBoat.polocation = POFar
        m in POFar.po <=> m not in PONear.po
    }
}
pred checkValidBoatPosition1{
    all m: POPosition.po | {
        POBoat.polocation = PONear <=> POBoat.polocation != POFar
        m in PONear.po <=> m not in POFar.po 
        m in POFar.po <=> m not in PONear.po
    }
}
pred checkValidBoatPosition2 {
    all m: POPosition.po | {
        POBoat.polocation != PONear <=> POBoat.polocation = POFar
        m in PONear.po <=> m not in POFar.po 
        m in POFar.po <=> m not in PONear.po
    }
}
pred checkSame {
    all p1, p2: Pet | {
        p1.owner = p2.owner => p1=p2
    }
}
pred checkNotSame {
    all p1, p2: Pet | {
        p1.owner != p2.owner => p1 != p2
    }
}
test suite for POvalidState {
    // If you have tests for this predicate, put them here!
    assert checkValidAnimalPosition1 is necessary for POvalidState
    assert checkValidAnimalPosition2 is necessary for POvalidState
    assert checkValidBoatPosition1 is necessary for POvalidState
    assert checkValidBoatPosition2 is necessary for POvalidState
    assert checkNotSame is necessary for POvalidState
    assert checkSame is necessary for POvalidState
    test expect {
        checkInvalidAnimalPosition: {
            POvalidState
            (some disj m, n: POPosition.po | {
                POBoat.polocation = PONear or POBoat.polocation = POFar
                m in PONear.po
                m not in POFar.po 
                n in POFar.po
                n in PONear.po
            })
        } is unsat
        checkInvalidBoatPosition: {
            POvalidState
            (some disj m, n: POPosition.po | {
                POBoat.polocation = PONear and POBoat.polocation = POFar
                m in PONear.po
                m not in POFar.po 
                n in POFar.po
                n not in PONear.po
            })
        } is unsat
        simpleValidsameSide: {
            POvalidState
            some disj a1, a2, a3: POAnimal | {
                POBoat.polocation = PONear
                (a1+a2+a3) in  PONear.po
                no POFar.po
            }   
        } is sat
        simpleValidDiffSides: {
            POvalidState
            some disj a1, a2, a3: POAnimal | {
                POBoat.polocation = POFar
                (a1) in  PONear.po
                (a1) not in  POFar.po
                (a2+a3) in POFar.po
                (a2+a3) not in PONear.po
            }   
        } is sat
        Owners:  {
            POvalidState
            some disj p1, p2: Pet | some o: Owner | (p1.owner = o) implies (p2.owner != o)
        } is sat
        Pets: {
            POvalidState
            some disj p: Pet | some disj o1, o2: Owner | (p.owner = o1) implies (p.owner != o2)
        } is sat
        tooManyOwners:  {
            POvalidState
            some p: Pet | some disj o1, o2: Owner {
                p.owner = o1
                p.owner = o2
            }
        } is unsat
        tooMAnyPets: {
            POvalidState
            some disj p1, p2: Pet | some o: Owner {
                p1.owner = o
                p2.owner = o
            }
        } is unsat
        alltogetherSAT: {
            POvalidState
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                PONear.po = o1 + o2
                POFar.po = p1 + p2
                p1.owner = o1
                p2.owner = o2
                POBoat.polocation = PONear
            }
        }is sat
        alltogetherUNSAT: {
            POvalidState
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                PONear.po = o1 + o2
                POFar.po = p1 + p2 + o1
                p1.owner = o2
                p2.owner = o2
                POBoat.polocation = PONear
            }
        }is unsat
        testVacuoty: {
            POvalidState
        } is sat
    }
    
}
pred inNear{
    all m: POAnimal | {
        POBoat.polocation = PONear
        m in PONear.po 
        no POFar.po
    }
}

pred notInFar{
    all m: POAnimal | {
        POBoat.polocation != POFar
        m not in POFar.po
    }
}
pred notInitYet{
    (#{a: POAnimal | a in POFar.po} > 0) => not POinitState
}
pred initCount {
    #{a: POAnimal | a in PONear.po} >= 0
    #{a: POAnimal | a in POFar.po} = 0
}
test suite for POinitState {
    // If you have tests for this predicate, put them here!
    assert inNear is necessary for POinitState
    assert notInFar is necessary for POinitState
    assert notInitYet is necessary for POinitState
    assert initCount is necessary for POinitState
    test expect{
        notInit: {
            not POinitState 
            some m, n: POAnimal | {
                m in POFar.po
                n in PONear.po
            }
        }is sat
        
        isInit: {
            POinitState 
            all disj m, n, b: POAnimal | {
                (m+n+b) in PONear.po 
                (m+n+b) not in POFar.po
            }
        }is sat
        isInit2: {
            not POinitState 
            all disj m, n, b: POAnimal | {
                (m+n+b) not in PONear.po 
                (m+n+b) in POFar.po
            }
        }is sat
        testVacuoty2: {
            POinitState
        } is sat
        isNotInit: {
            POinitState 
            some disj m, n, b: POAnimal | {
                POBoat.polocation = PONear
                (m+n+b) not in PONear.po 
                (m+n+b) in POFar.po
            }
        }is unsat
        isNotInit2: {
            POinitState 
            some disj m, n, b: POAnimal | {
                (m+n+b) in PONear.po 
                (m+n+b) not in POFar.po
                POBoat.polocation = POFar
            }
        }is unsat
    }
}

pred  checkInFar {
    all m: POAnimal | {
        m in POFar.po <=> m not in PONear.po
    }
}
pred checkNotInNear {
    #{a: POAnimal | a in PONear.po} = 0
   
}
pred notInFinalYet {
     #{a: POAnimal | a in PONear.po} > 0 implies not POfinalState
}
test suite for POfinalState {
    // If you have tests for this predicate, put them here!
    assert checkInFar is necessary for POfinalState
    assert checkNotInNear is necessary for POfinalState
    assert notInFinalYet is necessary for POfinalState
    test expect{
        validFinalSat: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                no PONear.po
                (g1 + g2 + g3 + w1 + w2 + w3) in POFar.po
            }
            POfinalState
        } is sat
        validTransitionSat: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                PONear.po = (w2 + w3)
                POFar.po = (g1 + g2 + g3 + w1)
                PONear.po' =  PONear.po - (w2 + w3)
                POFar.po' = POFar.po + (w2 + w3)
                next_state{POfinalState}
            }
        } is sat
        testVacuoty3: {
            POfinalState
        } is sat
         validFinalUNSAT: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                no POFar.po
                (g1 + g2 + g3 + w1 + w2 + w3) in PONear.po
            }
            POfinalState
        } is unsat
        validTransitionUNSAT: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                PONear.po = (w2 + w3)
                POFar.po = (g1 + g2 + g3 + w1)
                PONear.po' =  PONear.po + (w1)
                POFar.po' = POFar.po - (w1)
                next_state{POfinalState}
            }
        } is unsat
        invalidFinal: {
            some m: POAnimal | m in PONear.po and POfinalState
        } is unsat
        invalidFinal2: {
            some m: POAnimal | #{a: POAnimal | a in POFar.po} = 0 and POfinalState
        } is unsat
    }
}
test suite for POmove {
    // If you have tests for this predicate, put them here!
    test expect{
        testBoatPositionProperty: {
            all to, from: POPosition | {
                POmove[to, from] => ((POBoat.polocation = from) <=> (POBoat.polocation' = to)) 
            }
        } is theorem
        testAnimalPositionProperty: {
            all to, from: POPosition | {
                POmove[to, from] => {
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po 
                        (m+n) not in from.po'
                        (m+n) in to.po'}
                } 
            }
        } is theorem
        testAnimalBoatPositionProperty: {
            all to, from: POPosition | {
                POmove[to, from] => {
                    ((POBoat.polocation = from) <=> (POBoat.polocation' = to))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) in to.po'}
                } 
            }
        } is theorem
        testStrictOneAnimalPositionProperty: {
            all to, from: POPosition | {
                POmove[to, from] => {
                    ((POBoat.polocation = from) <=> (POBoat.polocation' = to))
                    some m: POAnimal | {
                        (m) in from.po 
                        (m) not in to.po
                        (m) not in from.po'
                        (m) in to.po'}
                } 
            }
        } is theorem
        testVacuoty5: {
            some t, f: POPosition | POmove[t,f]
        } is sat
        testBoatDoesntMove: {
            all disj to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
            }
        } is unsat
        testBoatDoesntMoveButpoDo: {
            all disj to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) in to.po'}
            }    
        } is unsat
        testpoDontMove: {
            all to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) not in to.po'}
            }    
        } is unsat
        testpoDontLeave: {
            all to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
                    some m,n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n)  in from.po'
                        (m+n)  in to.po'}
            }    
        } is unsat
    } 
}

    
pred noStealingNear {

    all p: Pet | {
        (p in PONear.po  and (some o: Owner | o in PONear.po)) implies (p.owner in PONear.po) }
}

pred noStealingFar {
    all p: Pet | {
        (p in POFar.po and (some o: Owner | o in POFar.po)) implies (p.owner in POFar.po) }
}
test suite for neverStealing {
    // If you have tests for this predicate, put them here!
    assert noStealingNear is necessary for neverStealing
    assert noStealingFar is necessary for neverStealing
    test expect {
        vacuoty: {
            neverStealing
        }is sat
        noStealing: {
            neverStealing
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po
            }
        } is sat
        noStealingStateTransition: {
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2 + o2
                PONear.po' = p1 + o1 

                always neverStealing
            }
        } is sat
        noStealingStateTransition2: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2 + p1
                PONear.po' = o2 + o1 

                always neverStealing
            }
        } is sat
        noStealing2: {
            neverStealing
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                p1.owner = o1
                p2.owner = o2
                POFar.po =  o1 + o2
                PONear.po = p1 + p2
            }
        } is sat
        noStealing3: {
            neverStealing
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                p1.owner = o1
                p2.owner = o2
                POFar.po =  o1 + o2 + p2
                PONear.po = p1 
            }
        } is sat
        noStealingStateTransition3: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2 
                PONear.po' = p1 + o1 + o2
                always neverStealing
            }
        } is sat
        noStealingStateTransition4: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = PONear
                p1.owner = o1
                p2.owner = o2
                POFar.po =  o1 + o2
                PONear.po = p1 + p2

                POBoat.polocation' = POFar
                POFar.po' = p2 + p1 + o2 + o1 
                no PONear.po' 

                always neverStealing
            }
        } is sat
        noStealingStateTransition3UNSAT: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2  + o1
                PONear.po' = p1 + o2
                always neverStealing
            }
        } is unsat
        noStealingStateTransition4UNSAT: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = PONear
                p1.owner = o1
                p2.owner = o2
                POFar.po =  o1 + o2
                PONear.po = p1 + p2

                POBoat.polocation' = o1 
                POFar.po' = p2 + p1 + o2 
                no PONear.po' 

                always neverStealing
            }
        } is unsat
    }
}
pred moveGood {
    always{POvalidState}
    POinitState
    POmove[POFar, PONear]
    always{neverStealing}
}
pred initValid {
    POinitState 
    POvalidState
   
}
pred finalValid {
    POfinalState implies POvalidState
}
pred moveToFinal {
    always{POvalidState}
    POmove[POFar, PONear]
    eventually {POfinalState}
    always{neverStealing}
}

pred initNeverSteal {
    POinitState
    neverStealing
}

pred finalNeverSteal {
    POfinalState implies neverStealing
}


test suite for POtraces {
    assert moveGood is necessary for POtraces
    assert initValid is necessary for POtraces
    assert finalValid is necessary for POtraces
    assert finalNeverSteal is necessary for POtraces
    assert initNeverSteal is necessary for POtraces
    assert moveToFinal is necessary for POtraces
    // If you have tests for this predicate, put them here!
    // make sure sats from other test suites also hold
    test expect {
        tracesVacuoty: {
            POtraces
        } is sat
       checkInvalidAnimalPositionTraces: {
            POvalidState
            (some disj m, n: POPosition.po | {
                POBoat.polocation = PONear or POBoat.polocation = POFar
                m in PONear.po
                m not in POFar.po 
                n in POFar.po
                n in PONear.po
            })
        } is unsat
        checkInvalidBoatPositionTraces: {
            POvalidState
            (some disj m, n: POPosition.po | {
                POBoat.polocation = PONear and POBoat.polocation = POFar
                m in PONear.po
                m not in POFar.po 
                n in POFar.po
                n not in PONear.po
            })
        } is unsat
        alltogetherSATTraces: {
            POvalidState
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                PONear.po = o1 + o2
                POFar.po = p1 + p2
                p1.owner = o1
                p2.owner = o2
                POBoat.polocation = PONear
            }
        }is sat
        alltogetherUNSATtrraces: {
            POvalidState
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                PONear.po = o1 + o2
                POFar.po = p1 + p2 + o1
                p1.owner = o2
                p2.owner = o2
                POBoat.polocation = PONear
            }
        }is unsat
        isInitTraces: {
            POinitState 
            all disj m, n, b: POAnimal | {
                (m+n+b) in PONear.po 
                (m+n+b) not in POFar.po
            }
        }is sat
        isNotInitTraces: {
            POinitState 
            some disj m, n, b: POAnimal | {
                POBoat.polocation = PONear
                (m+n+b) not in PONear.po 
                (m+n+b) in POFar.po
            }
        }is unsat
        validFinalSatTraces: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                no PONear.po
                (g1 + g2 + g3 + w1 + w2 + w3) in POFar.po
            }
            POfinalState
        } is sat
        validFinalUNSATTraces: {
            some disj g1, g2, g3: Pet | some w1, w2, w3: Owner | {
                no POFar.po
                (g1 + g2 + g3 + w1 + w2 + w3) in PONear.po
            }
            POfinalState
        } is unsat
        testAnimalBoatPositionPropertyTraces: {
            all to, from: POPosition | {
                POmove[to, from] => {
                    ((POBoat.polocation = from) <=> (POBoat.polocation' = to))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) in to.po'}
                } 
            }
        } is theorem
        testBoatDoesntMoveButpoDoTraces: {
            all disj to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) in to.po'}
            }    
        } is unsat
        testpoDontMoveTraces: {
            all to, from: POPosition | {
                POmove[to, from]  
                ((POBoat.polocation = from) <=> (POBoat.polocation' = from))
                    some m, n: POAnimal | {
                        (m+n) in from.po 
                        (m+n) not in to.po
                        (m+n) not in from.po'
                        (m+n) not in to.po'}
            }    
        } is unsat
        noStealingStateTransitionTraces: {
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2 + o2
                PONear.po' = p1 + o1 

                always neverStealing
            }
        } is sat
        noStealingStateTransitionTESTUNSAT: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = POFar
                p1.owner = o1
                p2.owner = o2
                POFar.po = p1 + o1 + p2 + o2
                no PONear.po

                POBoat.polocation' = PONear
                POFar.po' = p2  + o1
                PONear.po' = p1 + o2
                always neverStealing
            }
        } is unsat
        noStealingStateTransition4UNSATTraces: {
            
            some disj p1, p2: Pet | some disj o1, o2: Owner {
                POBoat.polocation = PONear
                p1.owner = o1
                p2.owner = o2
                POFar.po =  o1 + o2
                PONear.po = p1 + p2

                POBoat.polocation' = o1 
                POFar.po' = p2 + p1 + o2 
                no PONear.po' 

                always neverStealing
            }
        } is unsat
    }
}