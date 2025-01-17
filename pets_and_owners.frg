#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

---------- Definitions ----------

abstract sig POPosition {
    var po: set POAnimal
}
one sig PONear extends POPosition {}
one sig POFar extends POPosition {}

abstract sig POAnimal {}
sig Owner extends POAnimal {}
sig Pet extends POAnimal {
    // Note that the pet's Owner field is not "var" 
    // because we do not want it to change across states.
    owner: one Owner 
}

one sig POBoat {
    var polocation: one POPosition
}

pred POvalidState {
    // TODO: Fill me in!
    all m: POAnimal | {
        m in PONear.po implies m not in POFar.po
        m in POFar.po implies m not in PONear.po
    }
    POBoat.polocation = PONear implies POBoat.polocation != POFar
    POBoat.polocation = POFar implies POBoat.polocation != PONear

    all disj p1, p2: Pet | {
        p1.owner != p2.owner 
    }
    // all o: Owner | one p: Pet {p.owner = o}

    // Include the "physically reasonable" constraints here,
    // as well as the constraints on the "owns" relation.
}

pred POinitState {
    // TODO: Fill me in!
    POBoat.polocation = PONear
    all m: POAnimal | {
        m in PONear.po
        m not in POFar.po
    }
    // All of the po and the POBoat should start on the near side
}

pred POfinalState {
    // TODO: Fill me in!
    all m: POAnimal | {
        m not in PONear.po
        m in POFar.po
    }
    // We want to see all of the po reach the far side.
}

pred POmove[to, from: POPosition] {
    // TODO: Fill me in!
    POBoat.polocation = from
    POBoat.polocation' = to
    some m, n: POAnimal | {
        (m+n) in from.po
        (m+n) not in to.po
        from.po' = from.po - (m + n)
        to.po' = to.po + (m + n)
    }
    // The POBoat can carry at most two po each way,
    // but it can't travel across the river on its own.
    // In particular:
    //  - the POBoat must move
    //  - exactly 1 or 2 po cross with the POBoat 
    //  - every other animal stays in place
}

-----------------------------------------

pred neverStealing {
    // TODO: Fill me in!
    all p: Pet | {
        (p in PONear.po  and (some o: Owner | o in PONear.po)) implies (p.owner in PONear.po) }
    all p: Pet | {
        (p in POFar.po and (some o: Owner | o in POFar.po)) implies (p.owner in POFar.po) }
    
    // If an owner sees another owner's pet
    // and the other owner isn't around,
    // they might steal the pet!!
}

pred POtraces {
    // TODO: Fill me in!
    always{ POvalidState }
    POinitState
    always{
        POmove[PONear, POFar]  or  POmove[POFar, PONear]
    }
    always {neverStealing}
    eventually {POfinalState}   
}

run {
    POtraces
} for exactly 6 POAnimal, exactly 3 Pet, exactly 3 Owner, 5 Int 


// FOR AFTER YOU FINISH:
// Are there any solutions shorter than 12?
// Write down your findings!
//The same as goats and wolves I found that 12 was the shortest solution I could find.