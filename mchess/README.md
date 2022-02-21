# Mutilated Chessboard Problem

Experimental resulsts for the mutilated chessboard problem.
Find complete proofs by learning units (failed literals or
PR units) and PR binary clauses, keeping the units and 
deleting the PR binary clauses, then repeating.

formulas, dpr proofs, and proof logs for n=8,12,16,20,24 included

Configuration:

--pre_iterations=10 --pre_neighbors_depth=5 --pre_both_phases=0


Script: 

  sh mches_complete_proof.sh mches-formulas/mc[n].cnf

1. Run PReLearn with the above configuration.
2. Append unit clauses to the formula and delete binary clauses from the proof.
2.1 deletions.py used to delete binary clauses from proof.
3. Append proof to the cumulative proof.
4. If top-level conflict is reached, return. Else, resteart at step 1.

Note for n>24 the number of executions [$it] should be increased,
and the pre_neighbor_depth may need to be increased. Additionally,
the depth parameter can alternated per execution using the 
built-in for loop assigning [$clos].

output:

  mchess.dpr - complete dpr proof
  chess.cnf  - original formula with cumulative learned units appended 
               (pcnf header not updated)
  all PReLearn output files for last iteration


Verify with

  ./dpr-trim mchess-formulas/mc[n].cnf chess.dpr