#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

---------- Definitions ----------

abstract sig GWPosition {
    var gw: set GWAnimal
}
one sig GWNear extends GWPosition {}
one sig GWFar extends GWPosition {}

abstract sig GWAnimal {}
sig Goat extends GWAnimal {}
sig Wolf extends GWAnimal {}

one sig GWBoat {
    var gwlocation: one GWPosition
}

pred GWvalidState {
    // TODO: Fill me in!
    all m: GWPosition.gw | {
        m in GWNear.gw implies m not in GWFar.gw
        m in GWFar.gw implies m not in GWNear.gw
    }
    GWBoat.gwlocation = GWNear implies GWBoat.gwlocation != GWFar
    GWBoat.gwlocation = GWFar implies GWBoat.gwlocation != GWNear

    // For this problem, valid states are ones 
    // which are physically reasonable:
    // - animals should be on one side or the other.
    // - the GWBoat should be on one side or the other. 
}

// Each of the predicates below should *assume* valid states
// but should *not enforce* valid states.

pred GWinitState {
    // TODO: Fill me in!
    GWBoat.gwlocation = GWNear
    all m: GWAnimal | {
        m in GWNear.gw
        m not in GWFar.gw
    }
    // All of the gw and the GWBoat should start on the GWNear side
}

pred GWfinalState {
    // TODO: Fill me in!
    all m: GWAnimal | {
        m in GWFar.gw
        m not in GWNear.gw
    }
    // We want to see all of the gw reach the GWFar side.
}

pred GWmove[to, from: GWPosition] {
    // TODO: Fill me in!
    GWBoat.gwlocation = from
    GWBoat.gwlocation' = to 
    some m, n: GWAnimal | {
        (m+n) in from.gw
        (m+n) not in to.gw
        from.gw' = from.gw - (m + n)
        to.gw' = to.gw + (m + n)
    }
    // The GWBoat can carry at most two animals each way,
    // but it can't travel across the river on its own.
    // In particular:
    //  - the GWBoat must move
    //  - exactly 1 or 2 animals cross with the GWBoat 
    //  - every other animal stays in place
}

-----------------------------------------

pred GWneverEating {
    // TODO: Fill me in!
    (some g: Goat | g in GWNear.gw) implies 
    (#{s: Goat | s in GWNear.gw} >= #{w: Wolf | w in GWNear.gw})
    (some g: Goat | g in GWFar.gw) implies  
    (#{s: Goat | s in GWFar.gw} >= #{w: Wolf | w in GWFar.gw})
    // If the sheep are out numbered on one of the sides,
    // then the wolves can overpower and eat them!
    // Check to see if we can avoid that.
}

pred GWtraces { 
    // TODO: Fill me in!
    always{GWvalidState}
    GWinitState
    always{
        GWmove[GWNear, GWFar] or GWmove[GWFar, GWNear] 
    }
    always{GWneverEating}
    eventually {GWfinalState}
     
}

run {
    GWtraces
} for exactly 6 GWAnimal, exactly 3 Goat, exactly 3 Wolf

// FOR AFTER YOU FINISH:

// What happens if you change "{min, max}_tracelength" to "11"? 
// Are there any shorter solutions?
// Write down your findings!
// I found that 12 is the shortest solution i could find, I ran and got unsat on 11,
// I tried numbers lower than this to be sure but I found all to be unsat as well

