#lang forge

option problem_type temporal

---------- Definitions ----------

sig Node {
	next: lone Node
}

one sig Root extends Node {}

pred isList {
	-- all nodes are reachable from the root
	Root->(Node - Root) in ^next
}

abstract sig Pointer {
	var position: lone Node
}

one sig Tortoise extends Pointer {}
one sig Hare extends Pointer {}

---------- The Model ----------

pred init {
	-- TODO: Fill me in!
	-- Describe the initial state of the algorithm
		Tortoise.position = Root
		Hare.position = Root.next
		//ensure we don't have single node lists, nodes should be able to loop back on themselves, 
		// but the root shouldnt
		Root != Root.next

}

pred move {
	-- TODO: Fill me in!
	-- Whenever the hare is not at the end, the two pointers should move
	-- The hare should move forward two nodes if possible, one node if not
	all b, e: Node | {
		(e in b.^next and no e.next)	
		Hare.position != e
		(Hare.position.next = e) => (Hare.position' = e) 
		else (Hare.position' = Hare.position.next.next)
		Tortoise.position' = Tortoise.position.next
		
	}

}

pred hareAtEnd {
	-- TODO: Fill me in!
	-- The tortoise and hare should not move in this event
	no Hare.position.next
	Tortoise.position' = Tortoise.position
	Hare.position' = Hare.position
}

pred traces {
	-- TODO: Fill me in!
	init
	always {move}
	eventually{hareAtEnd}
	
}

--------------- Verification ----------------

pred cyclic {
	-- check if there is a cycle in the list
	some iden & ^next
}

pred acyclic {
	not cyclic
}

pred keepMoving {
	-- TODO: Fill me in!
	-- Show that the tortoise and hare move forever when the list is cyclic
	cyclic => always{move}
}

pred hareReachesEnd {
	-- TODO: Fill me in!
	-- Show that the hare is guaranteed to reach the end when the list is acyclic
	 acyclic => eventually{hareAtEnd}
}

pred noCatchUpIfAcyclic {
	-- TODO: Fill me in!
	//ask how to negate always, eventually, etc
	acyclic => always{Hare.position != Tortoise.position}
}

pred catchUpIfCyclic {
	-- TODO: Fill me in!
	cyclic => eventually {Hare.position = Tortoise.position}
}

-- TODO: Write tests to verify the properties described by the above predicates.

test expect {
	initTestTHM: {
		(init and isList) => {
			Hare.position = Tortoise.position.next
		}
	}is theorem
	initTestSAT: {
		(init and isList)
		all n: Node | {
			n = Root
			n.next = Hare.position
			n = Tortoise.position
		}
	}is sat
	initTestUNSAT: {
		(init and isList)
		Tortoise.position != Root
		Hare.position = Root.next
	} is unsat
	initTestUNSAT2: {
		(init and isList)
		Tortoise.position = Root
		Hare.position = Root
	} is unsat
	
	testMoveTHMharePos: {
		move => {
		all b, e: Node | {
			(e in b.^next and no e.next)	
			(Hare.position.next != e and Hare.position != e) => Hare.position' = Hare.position.next.next
			}
		}
	}is theorem
	testMoveTHMharePos2: {
		move => {
			all b, e: Node | {
				(e in b.^next and no e.next)	
				(Hare.position.next = e and Hare.position != e) => Hare.position' = Hare.position.next
			}
		}
	}is theorem
	testMoveTHMtortoisePos:{
		move => {
			Tortoise.position' = Tortoise.position.next
		}
	}is theorem
	testMoveUNSAT1: {
		move 
		all b, e: Node | {
			(e in b.^next and no e.next)	
			(Hare.position.next = e and Hare.position != e) => Hare.position' = Hare.position.next.next
		}
		
	} is unsat
	testMoveUNSAT2: {
		move 
		all b, e: Node | {
			(e in b.^next and no e.next)	
			(Hare.position.next != e and Hare.position != e) => Hare.position' = Hare.position.next
		}
	} is unsat
	
	testHareAtEndTHM: {
		hareAtEnd => {
			isList
			no n: Node | Hare.position.next = n
			Tortoise.position' != Tortoise.position.next
			Hare.position' != Hare.position.next
		}
	} is theorem
	testHareAtEndTHM2: {
		hareAtEnd => {
			isList
			no Hare.position.next
			not move
		}
	} is theorem
	testHareAtEndUNSAT: {
		hareAtEnd
		some n: Node | {
			isList
			n = Hare.position.next
			Hare.position' = n
		}
	} is unsat
	testHareAtEndUNSAT2: {
		hareAtEnd
		isList
		acyclic
		some n, m: Node | Tortoise.position = n and Tortoise.position.next = m
		Tortoise.position' = Tortoise.position.next
	}is unsat
	testTracesTHM: {
		traces => {
			not hareAtEnd => always{move}
		}
	}is theorem
	testTracesSAT: { 
		eventually{hareAtEnd} => acyclic
	}is sat
	testTracesUNSAT: { 
		traces
		always{hareAtEnd}
	}is unsat
	testTracesUNSAT2: {
		traces
		Hare.position = Root
	} is unsat
	//Verification tests below: since verification preds are so short, 
	//will test for cyclicness and asyclicness
	//not 100% sure this test is doing what i want it to
	tortCatchUp: {
		keepMoving => catchUpIfCyclic
	} is theorem 
	//Doesnt work on 2 element lists
	tortNotCatchUP: {
		hareReachesEnd => noCatchUpIfAcyclic
	} is theorem
	//These keep finding counterexample, unsure of if its the tests or the preds theyre testing that are wrong
	tortCatchUpUNSAT: {
		cyclic
		keepMoving
		noCatchUpIfAcyclic
	} is unsat  
	tortNotCatchUPUNSAT: {
		acyclic
		hareReachesEnd
		catchUpIfCyclic
	} is unsat
	notAcyclic: {
		not acyclic => cyclic
	} is theorem
	notCyclic: {
		not cyclic => acyclic
	} is theorem
	notAcyclic2: {
		(not acyclic and isList) => catchUpIfCyclic
	} is theorem
	notCyclic2: {
		(not cyclic and isList) => hareReachesEnd
	} is theorem
	notAcyclic3: {
		(not acyclic and isList) => keepMoving
	} is theorem
	notCyclic3: {
		(not cyclic and isList) => noCatchUpIfAcyclic
	} is theorem
	notAcyclic2UNSAT: {
		(not acyclic and isList) 
		hareReachesEnd
	} is unsat
	notCyclic2UNSAT: {
		(not cyclic and isList)
		catchUpIfCyclic
	} is unsat
	notAcyclic3UNSAT: {
		(not acyclic and isList)
		noCatchUpIfAcyclic
	} is unsat
	notCyclic3UNSAT: {
		(not cyclic and isList)
		keepMoving
	} is unsat
	
}
