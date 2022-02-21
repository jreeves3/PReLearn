# PReLearn
Preprocessor for Propagation Redundant Clause Learning

PReLearn is a SAT preprocessor built from the SDCL solver SaDiCaL. 
(found at http://fmv.jku.at/sadical/)
PReLearn modifies the outer solver of SaDiCaL to find and learn PR clauses.
The PR clauses are written to a file along with the PR proof 
(associating a witness with each clause). Proofs can be verified with dpr-trim.
(found at https://github.com/marijnheule/dpr-trim)
The PR clauses can be appended to the original formula and solved by a SAT 
solver such as Kissat. 
(found at https://github.com/arminbiere/kissat)

This respository contains evaluation results for the mutilated chessboard 
problem and some SAT competition benchmarks.

To build use

  cd PReLearn
  ./configure.sh && make 


To run on a CNF formula use
  
  ./sadical [--pre_{option}] formula

Default options correspond with the CADE '22 submission other than
--pre_iterations=50.

For extending depth of neighbors use
--pre_neighbors_depth=[i] \\ default i=0
Note i=0 corresponds with a single call to neighbors, denoted neighbors(1)
in the paper.

For the reduced heuristic to construct candidates instead of neighbors use
--pre_reduced=1

For only negative literals (-p) in the frist variable of a PR clause use
--pre_both_phases=0

For batch learning use
--pre_addinstant=0 \\ default addinstant=1 learns clauses as they are found
--pre_batch_size=[i]
and to determine how clauses are added per batch
--pre_batch_random=1
or
--pre_batch_sort=1

For learning clauses up to length i
--pre_length_end=[i] \\ default 3, so only binary clauses or units learned


Output files include

pr_units.cnf        - list of units (pr units and failed literals) learned
pr_units_full.dpr   - units with witnesses (dpr proof format)
pr_clauses.cnf      - list of clauses learned
pr_clauses_full.dpr - list of clauses and witnesses (dpr proof format)

Additional output information included in the terminal ouptut for 
every completed iteration and upon exiting. This output contains
commulative resulsts after each iteration.


To solve an instance use

  timeout 100s ./sadical [--pre_<options>] formula
  cat formula pr_clauses.cnf > formula_with_PR.cnf
  ./kissat formula_with_PR.cnf --relaxed 


To solve and verify a complete refutation proof use

  timeout 100s ./sadical [--pre_<options>] formula
  cat formula pr_clauses.cnf > formula_with_PR.cnf
  ./kissat formula_with_PR.cnf proof --relaxed 
  cat pr_clauses_full.pr proof > complete_proof.pr
  ./dpr-trim formula complete_proof.pr


To verify PReLearn proof is a correct derivation use
  
  timeout 100s ./sadical [--pre_<options>] formula
  ./dpr-trim formula pr_clauses_full.pr -f