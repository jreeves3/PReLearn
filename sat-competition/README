# sat-competition

SAT competition formulas and results used in the PReLearn evaluation.

Text files contain the names of formulas used, separated by those 
containing 0-10k clauses, and 10k-50k clauses. These formulas
come from the ’13, ’15, ’16, ’19, ’20, and ’21 SAT competitions.
Found at: http://satcompetition.org/

data: data for the default PReLearn configuration with a 100s timeout 
and 50 iterations. Compares execution time with (w/pr) and without (wo/pr) 
PReLearn preprocessing for the SAT solver Kissat. Execution time (with) 
includes preprocessing time. Ran with a 5,000 second timeout and 64 GB 
memory on StarExec cluster. In the spreadsheet, time of 5,0000 denotes
a timeout.

selected-formulas: some formulas solved exclusively with or exclusively 
without PReLearn with options (--pre_iterations=50) and 100s preprocessing.
SAT solver used to solve formulas with PR clauses was Kissat.

To solve and verify UNSAT proof for a formula:

  timeout 100s ./../PReLearn/sadical [formula] --pre_iterations=50
  cat [formula] pr_clauses.cnf > formula_with_PR.cnf
  ./kissat formula_with_PR.cnf proof --relaxed --no-binary
  cat pr_clauses_full.pr proof > complete_proof.pr
  ./dpr-trim [formula] complete_proof.pr

Note (--relaxed) for running kissat since catting the pr clauses would
not update the header of the cnf.
