#lang forge/temporal

open "goats_and_wolves.frg"
open "pets_and_owners.frg"


option max_tracelength 12
option min_tracelength 12

 

-- Decide what this correspondence is, informally, and write it down as precisely as you can
-- TODO: 
--   Pets correspond to Wolves and Owners correspond to Goats. A solution gives a state 
--   progression where, if there are any owners, there are at least as many owners as pets. 
--   By correspondence, this gives a G&W state progression where there are at least as many 
--   goats as wolves. This is exactly a solution to G&W.

/*
It is the responsibility of the transition function to preserve the identity of the animals.
 What is more important for correspondence is that the puzzle is in a similar state after a transition.
 Therefore, it is more improtant that we can show a more general correspondence, witht the shape of the state corresponding in GW and PO (i.e. the counts of goats and wolves between states is the same)
rather than directly corresponding a specific wolf to a specific pet and a specific goat to a specific owner. 
*/
one sig Correspondence{
    position: func POPosition -> GWPosition
}
// pred Correspondence{
pred Corresponds {
    all poPos: POPosition, gwPos: GWPosition | {
        (poPos = PONear <=> gwPos = GWNear) 
        (poPos = POFar <=> gwPos = GWFar) 
        (Correspondence.position[poPos] = gwPos) => {
            #{g: Goat | g in gwPos.gw} = #{o: Owner | o in poPos.po}
            #{w: Wolf | w in gwPos.gw} = #{p: Pet | p in poPos.po}   

            POBoat.polocation = PONear  <=> GWBoat.gwlocation = GWNear
            POBoat.polocation = POFar  <=> GWBoat.gwlocation = GWFar
        }
        
    }
}
pred tracesWithCorrespondence {
    always {Corresponds}
    POtraces
    GWtraces
    eventually {!Corresponds => (!POtraces and !GWtraces)}
}
/*******************TESTS*******************/

test expect {
    verifyCorrespondenceHolds: {
        tracesWithCorrespondence => always{Corresponds}
    }is sat
    notCorrespondenceForPOTraces: {
        tracesWithCorrespondence => (!Corresponds => !POtraces)
    }is sat
    notCorrespondenceForGWTraces: {
        tracesWithCorrespondence => (!Corresponds => !GWtraces)
    }is sat
    misMatchAnials: {
       (#{g: Goat | g in GWNear.gw} != #{o: Owner | o in PONear.po} or #{g: Goat | g in GWFar.gw} != #{o: Owner | o in POFar.po})=> !Corresponds
    }is sat
    misMatchAnials2: {
       some g1, g2: Goat, o1, o2: Owner | {
        (g1 + g2) in GWNear and (o1+o2) in GWFar => !Corresponds}
    }is sat
    isMatchAnimalsunsat: {
        Corresponds
        some g1, g2: Wolf, o1, o2: Pet | {
        (g1 + g2) in GWNear and (o1+o2) in GWFar}
    }is unsat
    correspondenceNecessaryForMoves: {
        always {tracesWithCorrespondence => (POmove[PONear, POFar] <=> GWmove[GWNear, GWFar])}
    } is sat
    correspondenceNecessaryForMoves2: {
        always {!tracesWithCorrespondence => (POmove[PONear, POFar] <=> GWmove[GWFar, GWNear])}
    } is sat
    moveMismatch: {
        always {
            (POmove[PONear, POFar] and GWmove[GWFar,GWNear]) => !tracesWithCorrespondence
        }
    } is sat
    moveMismatch2: {
        always {
            (GWmove[GWNear, GWFar] and POmove[POFar,PONear]) => !tracesWithCorrespondence
        }
    } is sat
    validStateCorresponence: {
        always {(GWvalidState and POvalidState) => tracesWithCorrespondence}
    } is sat //could be a theorem?
    initStateCorresponence: {
       (GWinitState and POinitState) => tracesWithCorrespondence
    }is sat
    neverStealingCorrespondence: {
        always {(neverStealing and GWneverEating) => tracesWithCorrespondence}
    }is sat
    finalStateCorrespondence: {
        eventually {(POfinalState and GWfinalState) => tracesWithCorrespondence}
    }is sat
    
}
