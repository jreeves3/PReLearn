#ifndef _extract_h_INCLUDED
#define _extract_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "internal.h"

/*------------------------------------------------------------------------*/

typedef struct Partial_PR Partial_PR;
typedef struct Candidate_PR Candidate_PR;
typedef struct Candidate_Queue Candidate_Queue;

/*------------------------------------------------------------------------*/

struct Partial_PR
{
  STACK (int) decisions;
  STACK (int) vals;      // Current assignment (-1, 0, 1).
  STACK (int) trail;      // Trail of assigned variables.
};

/*------------------------------------------------------------------------*/

struct Candidate_PR
{
  int idx;    // variable idx that started BFS for this candidate
  STACK (Partial_PR*) partial_prs;
  
  int pr_found;   // data if PR clause is found for this candidate
  int * pr_clause; // includes idx (first decision)
  int pr_size;
  int * witness;  // assignment from the pruning predicate
  int wit_size;
  int * trail;
  int trail_size;
};

/*------------------------------------------------------------------------*/

struct Candidate_Queue
{
  int * seen;   // Variables seen in BFS
  STACK (int) next_frontier;  // Variables added to frontier for next round
  STACK (Candidate_PR*) candidate_prs; // PR candidates of current round
  Solver * solver;
  
  int count;      // Number of pr candidates
  int frontier_count;   // Number of variables on frontier
  int cutoff;   // cutoff size (number of decisions) for candidate_prs
};

/*------------------------------------------------------------------------*/

// TODO: partial_pr->vals not used?

Partial_PR * new_partial_pr(Solver * solver) {
  Partial_PR * partial_pr = malloc (sizeof (Partial_PR));
//  if (!partial_pr) DIE ("out-of-memory allocating partial_pr");
  INIT (partial_pr->decisions);
  INIT (partial_pr->vals);
  INIT (partial_pr->trail);
  return partial_pr;
}

Partial_PR * new_copy_pr (Solver * solver, Partial_PR * part_pr) {
  SaDiCaL * sadical = solver->sadical;
  Partial_PR * copy_pr = new_partial_pr (solver);
  for (int i = 0; i < SIZE (part_pr->decisions); i++)
    PUSH (copy_pr->decisions, PEEK (part_pr->decisions, i));
//  for (int i = 0; i < SIZE (part_pr->decisions); i++)
//    PUSH (copy_pr->decisions, PEEK (part_pr->decisions, i));
  for (int i = 0; i < SIZE (part_pr->trail); i++)
    PUSH (copy_pr->trail, PEEK (part_pr->trail, i));
  return copy_pr;
}

void delete_partial_pr(Solver * solver, Partial_PR * partial_pr) {
  SaDiCaL * sadical = solver->sadical;
  RELEASE (partial_pr->decisions);
  RELEASE (partial_pr->vals);
  RELEASE (partial_pr->trail);
  free (partial_pr);
}

Candidate_PR * new_candidate_pr(Solver * solver, int idx) {
  Candidate_PR * candidate_pr = malloc (sizeof (Candidate_PR));
//  if (!candidate_pr) DIE ("out-of-memory allocating candidate_pr");
  candidate_pr->idx = idx;
  candidate_pr->pr_found = 0;
  candidate_pr->pr_size = 0;
  candidate_pr->wit_size = 0;
  candidate_pr->trail_size = 0;
  INIT (candidate_pr->partial_prs);
  return candidate_pr;
}

void delete_candidate_pr(Solver * solver, Candidate_PR * candidate_pr) {
  for (int i = 0; i < SIZE (candidate_pr->partial_prs); i++) {
    delete_partial_pr (solver, PEEK (candidate_pr->partial_prs, i));
  }
  SaDiCaL * sadical = solver->sadical;
  if (SIZE (candidate_pr->partial_prs) > 0)
    CLEAR (candidate_pr->partial_prs);
  RELEASE (candidate_pr->partial_prs);
  if (candidate_pr->pr_size) free (candidate_pr->pr_clause);
  if (candidate_pr->wit_size) free (candidate_pr->witness);
  if (candidate_pr->trail_size) free (candidate_pr->trail);
  free (candidate_pr);
}

Candidate_Queue * new_candidate_queue(Solver * solver, int max_var, int cutoff) {
  Candidate_Queue * candidate_queue = malloc (sizeof (Candidate_Queue));
//  if (!candidate_queue) DIE ("out-of-memory allocating candidate_queue");
  candidate_queue->seen = malloc (sizeof (int) * max_var);
  for (int i = 0; i < max_var; i++) candidate_queue->seen[i] = -1;
  candidate_queue->count = 0;
  candidate_queue->frontier_count = 0;
  candidate_queue->cutoff = cutoff;
  candidate_queue->solver = solver;
  INIT (candidate_queue->next_frontier);
  INIT (candidate_queue->candidate_prs);
  
  return candidate_queue;
}

void delete_candidate_queue(Solver * solver, Candidate_Queue * candidate_queue) {
  for (int i = 0; i < SIZE (candidate_queue->candidate_prs); i++) {
    delete_candidate_pr (solver, POP (candidate_queue->candidate_prs));
  }
  SaDiCaL * sadical = solver->sadical;
  RELEASE (candidate_queue->next_frontier);
  RELEASE (candidate_queue->candidate_prs);
  free (candidate_queue->seen);
  free (candidate_queue);
}

/*------------------------------------------------------------------------*/




#endif
