#lang forge/temporal

open "goats_and_wolves.frg"
open "pets_and_owners.frg"


option max_tracelength 12
option min_tracelength 12
-- Let's show that a solution to pets and owners always corresponds to 
--   a solution to goats and wolves!

//TODO: In your own words, give a simple definition for correspondence 
/*
    YOUR ANSWER HERE
*/
//TODO: Fill in the sig below, think about how we might represent the mapping between the two solutions
one sig Correspondence{
    //HINT: Think about what properties are shared between the two solutions
    
}
//TODO: Write a predicate to enforce correspondence between the two River Crossing problems
pred Corresponds {
   
}
//TODO: Incorporate correspondence with your traces (feel free to change the way POtraces and GWtraces are incorporated)
pred tracesWithCorrespondence {
    POtraces
    GWtraces
}

//TODO: Write a few tests to verify your correspondence holds throughout traces
//Hint: You likely wont have any is checked tests for this section, but that's okay!
// You should focus on some basic edge cases and making sure your implementation preserves correspondence 
test expect {

}