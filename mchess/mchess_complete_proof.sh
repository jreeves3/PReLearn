#!/bin/bash


old="chess.cnf"
cp $1 $old
proof="chess.dpr"

rm $proof

for it in {1..30}
do
echo $it
  for clos in 5
  do
  ./../PReLearn/sadical $old --pre_iterations=10 --pre_both_phases=0 --pre_neighbors_depth=$clos > out.txt

  cat out.txt

  cat $old pr_units.cnf > temp.txt
  cp temp.txt $old

  rm temp.txt

  python3 deletions.py -f pr_clauses_full.dpr > temp.dpr

  cat $proof temp.dpr > full.dpr
  cp full.dpr $proof
  
  rm temp.dpr full.dpr

  fini=$(grep "TOP LEVEL CONFLICT" out.txt)
  rm out.txt
  if [[ $fini != "" ]]
  then
    exit
  fi

  done
done
