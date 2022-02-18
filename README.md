# PReLearn
Preprocessor for Propagation Redundant Clause Learning

This repository will be updated in the following days with source code and experimental data.

PReLearn is a SAT preprocessor built from the SDCL solver SaDiCaL. (found at http://fmv.jku.at/sadical/)
PReLearn modifies the outer solver of SaDiCaL to find and learn PR clauses.
The PR clauses are written to a file along with the PR proof (associating a witness with each clause).
The PR clauses can be appended to the original CNF and solved by a SAT solver such as Kissat (https://github.com/arminbiere/kissat).

This respository containts data for the mutilated chessboard problem and SAT competition benchmarks.

