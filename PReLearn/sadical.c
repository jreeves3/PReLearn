// Copyright (C) 2018 by Armin Biere JKU Linz and Marijn Heule UT Austin.

/*------------------------------------------------------------------------*/

#include "sadical.h"
#include "internal.h"
#include "extract.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <string.h>
#include <stddef.h>

/*------------------------------------------------------------------------*/

#define MODE_LOOKAHEAD  3
#define MODE_RELEVANT   5

/*------------------------------------------------------------------------*/

// Get the variable index of a literal which in essence is just computing
// the absolute value of the integer representing the literal.  We want to
// to make sure though that the literal is a valid literal.  This helps to
// find many bugs which often lead to access inconsistent literals.

inline static int literal_index (Solver * solver, int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int res = abs (lit);
  assert (res <= solver->max_var);
  return res;
}

inline static int variable_index (Solver * solver, Var * v) {
  assert (solver->vars < v);
  assert (v <= solver->vars + solver->max_var);
  return v - solver->vars;
}

inline static Var * var (Solver * solver, int lit) {
  return solver->vars + literal_index (solver, lit);
}

inline static int val (Solver * solver, int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) <= solver->max_var);
  return solver->vals[lit];
}

inline static Watches * watches (Solver * solver, int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) <= solver->max_var);
  return &solver->watches[lit];
}

inline static Score * score (Solver * solver, int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) <= solver->max_var);
  return &solver->scores[lit];
}

/*------------------------------------------------------------------------*/

// Marking of literals for checking tautological clauses and analysis.

static void mark (Solver * solver, int lit) {
  Var * v = var (solver, lit);
  assert (labs (v->stamp) < solver->stamp);
  v->stamp = lit < 0 ? -solver->stamp : solver->stamp;
}

static int marked (Solver * solver, int lit) {
  Var * v = var (solver, lit);
  if (labs (v->stamp) < solver->stamp) return 0;
  int res = v->stamp < 0 ? -1 : 1;
  if (lit < 0) res = -res;
  return res;
}

/*------------------------------------------------------------------------*/

static Clause * new_clause (Solver * solver, bool redundant, int glue) {
  SaDiCaL * sadical = solver->sadical;
  size_t size = SIZE (solver->clause);
  assert (size > 1);	// No unit nor empty clauses.
  size_t bytes = sizeof (Clause) + size * sizeof (int);
  Clause * res = malloc (bytes);
  if (!res) DIE ("out-of-memory allocating clause");
  ADD_ALLOCATED (bytes);
  ADD_STATS (clauses.allocated, bytes);
  res->added = solver->local.clauses.added;
  res->redundant = redundant;
  res->garbage = false;
  res->reason = false;
  res->used = true;
  res->glue = glue;
  res->size = size;
  res->search = size;
  for (int i = 0; i < size; i++)
    res->literals[i] = PEEK (solver->clause, i);
  INC_STATS (clauses.added);
  if (redundant) INC_STATS (clauses.redundant);
  else INC_STATS (clauses.irredundant);
  PUSH (solver->clauses, res);
  CLEAR (solver->clause);
  return res;
}

static long delete_clause (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  size_t bytes = sizeof (Clause) + c->size * sizeof (int);
  ADD_STATS (clauses.collected, bytes);
  SUB_ALLOCATED (bytes);
  if (c->redundant) DEC_STATS (clauses.redundant);
  else DEC_STATS (clauses.irredundant);
  free (c);
  return bytes;
}

/*------------------------------------------------------------------------*/

static void watch_literal (Solver * solver, int lit, int blit, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  Watches * ws = watches (solver, lit);
  Watch w = { blit, c->size, c };
  PUSH (*ws, w);
  LOGCLS (c, "watching %d with blocking literal %d in", lit, blit, c);
}

static void watch_clause (Solver * solver, Clause * c) {
  assert (c->size > 1);
  watch_literal (solver, c->literals[0], c->literals[1], c);
  watch_literal (solver, c->literals[1], c->literals[0], c);
}

static int
remove_falsified_literals_from_clause (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  assert (!solver->level);
  int j = 0;
  for (int i = 0; i < c->size; i++) {
    int lit = c->literals[i];
    int tmp = val (solver, lit);
    if (tmp < 0) continue;
    c->literals[j++] = lit;
  }
  int removed = c->size - j;
  assert (removed > 0);
  size_t bytes = removed * sizeof (int);
  SUB_ALLOCATED (bytes);
  c->size = j;
  if (c->search > c->size) c->search = j;
  LOGCLS (c, "shrunken clause");
  return removed;
}

/*------------------------------------------------------------------------*/

// Carefully initialized exponential moving averages as in 'Cadical.EMA'.

static void init_average (Solver * solver,
                          Average * a, const char * name, double alpha) {
  a->name = name;
  a->alpha = alpha;
  a->beta = 1.0;
  a->wait = 0;
  a->period = 0;
  LOG ("initialized %s average with alpha %g",  name, alpha);
}

static void update_average (Solver * solver, Average * a, double y) {
  a->val += a->beta * (y - a->val);
  LOG ("update average %s with %g beta %g yields %g",
    a->name,  y, a->beta, a->val);
  if (a->beta <= a->alpha || a->wait--) return;
  a->wait = a->period = 2 * (a->period + 1) - 1;
  a->beta *= 0.5;
  if (a->beta < a->alpha) a->beta = a->alpha;
  LOG ("new average %s wait = period = %ld, beta = %g",
    a->name, a->wait, a->beta);
}

/*------------------------------------------------------------------------*/

static void init_limits (Solver * solver) {

  SaDiCaL * sadical = solver->sadical;

  LOG ("initializing limits");

  solver->lim.reduce = solver->local.conflicts + sadical->opts.reduceinit;
  solver->inc.reduce = sadical->opts.reduceinit;
  MSG (2, "initial reduce limit %ld increment %ld",
    solver->lim.reduce, solver->inc.reduce);

  solver->lim.restart = solver->local.conflicts + sadical->opts.restartint;
  MSG (2, "initial restart limit %ld interval %ld",
    solver->lim.restart, sadical->opts.restartint);

  init_average (solver,
    &solver->avg.glue.fast, "fast glue", sadical->opts.alphafast);
  init_average (solver,
    &solver->avg.glue.slow, "slow glue", sadical->opts.alphaslow);
  init_average (solver,
    &solver->avg.jump, "jump", sadical->opts.alphaslow);
  init_average (solver,
    &solver->avg.size, "size", sadical->opts.alphaslow);
}

/*------------------------------------------------------------------------*/

// Allocate and initialize new solver(s)

static Solver * new_solver (SaDiCaL * sadical) {

  Solver * solver = malloc (sizeof * solver);
  if (!solver) DIE ("out-of-memory allocating solver");
  memset (solver, 0, sizeof *solver);
  ADD_ALLOCATED (sizeof *solver);
  solver->sadical = sadical;

  // Initialize decision stack (always one larger than 'level').

  Frame frame;
  memset (&frame, 0, sizeof frame);
  PUSH (solver->frames, frame);

  solver->mode = MODE_LOOKAHEAD;
  solver->balance = 1;

  return solver;
}

SaDiCaL * sadical_new (void) {

  SaDiCaL * sadical = malloc (sizeof * sadical);
  if (!sadical) DIE ("out-of-memory allocating SaDiCaL");
  memset (sadical, 0, sizeof *sadical);
  ADD_GLOBAL_ALLOCATED (sizeof *sadical);

  // Initialize options.

#define OPTION(NAME,TYPE,VAL,MIN,MAX,DESCRIPTION) \
  assert (MIN <= VAL), assert (VAL <= MAX); \
  sadical->opts.NAME = VAL;
  OPTIONS
#undef OPTION

  sadical->inner = new_solver (sadical);
  sadical->outer = new_solver (sadical);

  return sadical;
}

/*------------------------------------------------------------------------*/

static void assign (Solver * solver, int lit, Clause * reason) {
  SaDiCaL * sadical = solver->sadical;
#ifndef NLOG
  if (reason) LOGCLS (reason, "assign %d reason", lit);
  else if (!solver->level) LOG ("assign %d unit", lit);
  else LOG ("assign %d decision", lit);
#endif
  assert (!val (solver, lit));
  PUSH (solver->trail, lit);
  if (!solver->level) {
    solver->local.units++, reason = 0;
//    MSG (1, "assign unit at level 0 %d",lit);
  }
  int sign = lit < 0 ? -1 : 1;
  int idx = literal_index (solver, lit);
  solver->vals[idx] = sign;
  solver->vals[-idx] = -sign;
  Var * v = var (solver, lit);
  v->val = sign;
  if (!solver->do_not_save_phases) v->phase = sign;
  v->level = solver->level;
  v->reason = reason;
  if (reason) reason->reason = true;
}

static void unassign (Solver * solver, int lit) {
  LOG ("unassign %d", lit);
  assert (val (solver, lit) > 0);
  int idx = literal_index (solver, lit);
  assert (solver->vals[idx]);
  solver->vals[idx] = 0;
  assert (solver->vals[-idx]);
  solver->vals[-idx] = 0;
  Var * v = solver->vars + idx;
  assert (v->val);
  v->val = 0;
  if (v->reason) {
    assert (v->reason->reason);
    v->reason->reason = false;
  }
  if (v->enqueued > var (solver, solver->queue.searched)->enqueued)
    solver->queue.searched = idx;
}

static void backtrack (Solver * solver, int jump) {
  assert (0 <= jump);
  assert (jump < solver->level);
  while (!EMPTY (solver->trail)) {
    int lit = TOP (solver->trail);
    Var * v = var (solver, lit);
    if (v->level == jump) break;
    (void) POP (solver->trail);
    solver->level = v->level - 1;
    unassign (solver, lit);
  }
  solver->next_to_propagate = SIZE (solver->trail);
  RESIZE (solver->frames, jump + 1);
}

/*------------------------------------------------------------------------*/

static Clause * propagate (Solver * solver) {
  Clause * conflict = 0;
  while (!conflict && solver->next_to_propagate < SIZE (solver->trail)) {
    int lit = -PEEK (solver->trail, solver->next_to_propagate);
    solver->next_to_propagate++;
    LOG ("propagate %d", -lit);
    assert (val (solver, lit) < 0);
    INC_STATS (propagations);
    Watches * ws = watches (solver, lit);
    Watch * p, * q = ws->begin;
    for (p = q; !conflict && p < ws->end; p++) {
      Watch w = *q++ = *p;
      UNREACHABLE (w.size == 1);	// Not unit (nor empty) clauses!
      int blit = w.blit;
      int blit_val = val (solver, blit);
      if (blit_val > 0) continue;
      Clause * c = w.clause;
      if (c->garbage) continue; // Joseph
      if (w.size == 2) {
	if (blit_val < 0) conflict = c;
	else assign (solver, blit, c);
      } else {
	assert (w.size > 2);
	int * lits = c->literals;
	int other = lits[0]^lits[1]^lit;
	lits[0] = other, lits[1] = lit;
	int other_val = (other == blit ? blit_val : val (solver, other));
	if (other_val > 0) { q[-1].blit = other; continue; }
	int i, replacement = 0, replacement_val = -1, size = c->size;
	int search = c->search;
	assert (2 <= search), assert (search <= size);
	for (i = search; replacement_val < 0 && i < size; i++)
	  replacement_val = val (solver, replacement = lits[i]);
	if (replacement_val < 0) {
	  for (i = 2; replacement_val < 0 && i < search; i++)
	    replacement_val = val (solver, replacement = lits[i]);
	}
	c->search = i;
	if (replacement_val >= 0) {
	  LOGCLS (c, "unwatching %d in", lit);
	  lits[1] = replacement;
	  lits[i-1] = lit;
	  watch_literal (solver, replacement, lit, c);
	  q--;
	} else if (other_val < 0) conflict = c;
	else assign (solver, other, c);
      }
    }
    while (p < ws->end) *q++ = *p++;
    ws->end = q;
  }
  if (conflict) {
    LOGCLS (conflict, "conflict");
    INC_STATS (conflicts);
  }
  return conflict;
}

/*------------------------------------------------------------------------*/

static void import_literal (Solver *, int lit);

// Map an outer literal to an inner literal, using a new literal if it the
// outer one was not mapped yet.

static int map (Solver * solver, int lit) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->outer == solver);
  Var * v = var (solver, lit);
  assert (v->stamp <= solver->stamp);
  if (v->stamp < solver->stamp) {
    Solver * inner = sadical->inner;
    int outer_idx = abs (lit);
    int inner_idx = inner->max_var + 1;
    v->mapped = inner_idx;
    v->stamp = solver->stamp;
    LOG ("mapping outer variable %d to inner %d", outer_idx, inner_idx);
    import_literal (inner, inner_idx);
    Var * u = var (inner, inner_idx);
    u->mapped = outer_idx;			// Currently not used.
  }
  int res = v->mapped;
  if (lit < 0) res = -res;
  return res;
}

/*------------------------------------------------------------------------*/

static void trace_binary_literal (int lit, FILE * proof) {
  assert (lit != INT_MIN);
  unsigned x = 2*abs (lit) + (lit < 0);
  unsigned char ch;
   while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    putc (ch, proof);
    x >>= 7;
  }
  ch = x;
  putc (ch, proof);
}

static void
trace_clause (Solver * solver,
              int * lits, int size, bool add, bool skip_falsified) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->outer == solver);
  bool binary = sadical->opts.binary;
  FILE * proof = sadical->proof;
  assert (proof);
  if (binary) putc (add ? 'a' : 'd', proof);
  else if (!add) fputs ("d ", proof);
  for (int i = 0; i < size; i++) {
    int lit = lits[i];
    if (skip_falsified && val (solver, lit) < 0) continue;
    if (binary) trace_binary_literal (lit, proof);
    else fprintf (proof, "%d ", lit);
  }
  if (binary) putc (0, proof);
  else fputs ("0\n", proof);
  if (!sadical->close_proof) fflush (proof);
}

static void trace_empty_clause_addition (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOG ("tracing added empty clause");
  trace_clause (solver, 0, 0, true, false);
}

static void trace_unit_clause_addition (Solver * solver, int unit) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOG ("tracing added unit clause %d", unit);
  trace_clause (solver, &unit, 1, true, false);
}

static void trace_clause_addition (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOGCLS (c, "tracing added");
  trace_clause (solver, c->literals, c->size, true, false);
}

static void trace_clause_deletion (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOGCLS (c, "tracing deleted");
  trace_clause (solver, c->literals, c->size, false, false);
}

static void trace_simplified_clause_addition (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOGLITS (solver->clause.begin,
    SIZE (solver->clause), "tracing added simplified");
  trace_clause (solver, solver->clause.begin,
    SIZE (solver->clause), true, false);
}

static void trace_original_clause_deletion (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOGLITS (solver->original.begin,
    SIZE (solver->original), "tracing deleted original");
  trace_clause (solver, solver->original.begin,
    SIZE (solver->original), false, false);
}

static void trace_clause_shrinking (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->proof) return;
  if (sadical->inner == solver) return;
  LOGCLS (c, "tracing added shrunken");
  trace_clause (solver, c->literals, c->size, true, true);
  LOGCLS (c, "tracing deleted before shrinking");
  trace_clause (solver, c->literals, c->size, false, false);
}

/*------------------------------------------------------------------------*/

static int cmp_analyzed (const void * p, const void * q) {
  Var * u = * (Var **) p;
  Var * v = * (Var **) q;
  if (u->enqueued < v->enqueued) return -1;
  if (u->enqueued > v->enqueued) return 1;
  UNREACHABLE (u->enqueued == v->enqueued);
  return 0;					// unreachable ...
}

static void dequeue (Solver * solver, int idx) {
  Var * v = var (solver, idx);
  if (solver->queue.searched == idx) {
    if (v->prev) solver->queue.searched = v->prev;
    else solver->queue.searched = v->next;
  }
  if (v->prev) {
    Var * prev = var (solver, v->prev);
    assert (prev->next == idx);
    prev->next = v->next;
  } else {
    assert (solver->queue.first == idx);
    solver->queue.first = v->next;
  }
  if (v->next) {
    Var * next = var (solver, v->next);
    assert (next->prev == idx);
    next->prev = v->prev;
  } else {
    assert (solver->queue.last == idx);
    solver->queue.last = v->prev;
  }
}

static void enqueue_first (Solver * solver, int idx) {
  Var * v = var (solver, idx);
  if (solver->queue.first) {
    Var * first = var (solver, solver->queue.first);
    assert (!first->prev);
    first->prev = idx;
  } else {
    assert (!solver->queue.last);
    solver->queue.last = idx;
  }
  v->next = solver->queue.first;
  v->prev = 0;
  solver->queue.first = idx;
  v->enqueued = solver->queue.enqueued++;
  if (!solver->queue.searched) {
    assert (!v->next);
    assert (solver->queue.last == idx);
    solver->queue.searched = idx;
  }
}

static void enqueue_last (Solver * solver, int idx) {
  Var * v = var (solver, idx);
  if (solver->queue.last) {
    Var * last = var (solver, solver->queue.last);
    assert (!last->next);
    last->next = idx;
  } else {
    assert (!solver->queue.first);
    solver->queue.first = idx;
  }
  v->prev = solver->queue.last;
  v->next = 0;
  solver->queue.last = idx;
  v->enqueued = solver->queue.enqueued++;
  if (!v->val) solver->queue.searched = idx;
}

static void bump_analyzed (Solver * solver) {
  LOG ("bumping %ld analyzed variables", (long) SIZE (solver->analyzed));
  qsort (solver->analyzed.begin,
    SIZE (solver->analyzed), sizeof (Var*), cmp_analyzed);
  for (Var ** p = solver->analyzed.begin; p < solver->analyzed.end; p++) {
    Var * v = *p;
    int idx = variable_index (solver, v);
    LOG ("bumping variable %d enqueued %ld", idx, v->enqueued);
    if (idx == solver->queue.last) continue;
    dequeue (solver, idx);
    enqueue_last (solver, idx);
  }
}

static void learn_empty_clause (Solver * solver) {
  LOG ("learning empty clause");
  assert (!solver->inconsistent);
  assert (!solver->level);
  solver->inconsistent = true;
  trace_empty_clause_addition (solver);
}

static void update_learned_clause_stats (Solver * solver,
                                         int glue, int size, int jump) {
  LOG ("glue %d", glue);
  LOG ("size %d", size);
  LOG ("jump %d", jump);
  update_average (solver, &solver->avg.glue.slow, glue);
  update_average (solver, &solver->avg.glue.fast, glue);
  update_average (solver, &solver->avg.size, size);
  update_average (solver, &solver->avg.jump, jump);
}

static int analyze (Solver * solver, Clause * conflict) {
  if (!solver->level) { learn_empty_clause (solver); return 20; }
  assert (EMPTY (solver->clause));
  assert (EMPTY (solver->analyzed));
  SaDiCaL * sadical = solver->sadical;
  PUSH (solver->clause, 0);
  int i = SIZE (solver->trail);
  Clause * reason = conflict;
  int uip = 0, open = 0;
  solver->stamp++;
  for (;;) {
    assert (reason);
    reason->used = true;
    LOGCLS (reason, "analyzing");
    for (int j = 0; j < reason->size; j++) {
      int lit = reason->literals[j];
      if (marked (solver, lit)) continue;
      Var * v = var (solver, lit);
      UNREACHABLE (solver == sadical->outer && !v->level);
      if (!v->level) continue;
      LOG ("analyzing literal %d at level %d",
        lit, var (solver, lit)->level);
      assert (val (solver, lit) < 0);
      PUSH (solver->analyzed, v);
      mark (solver, lit);
      if (v->level < solver->level) {
	LOG ("adding literal %d to learned clause", lit);
	PUSH (solver->clause, lit);
      } else open++;
    }
    do {
      i--;
      uip = PEEK (solver->trail, i);
    } while (!marked (solver, uip));
    if (!--open) break;
    reason = var (solver, uip)->reason;
  }
  LOG ("1st UIP %d", uip);
  POKE (solver->clause, 0, -uip);
  int size = SIZE (solver->clause), jump = 0, glue = 1;
  LOG ("pulling in decision level %d", solver->level);
  for (int j = 1; j < size; j++) {
    int lit = PEEK (solver->clause, j);
    int tmp = var (solver, lit)->level;
    assert (tmp < solver->level);
    assert (tmp < SIZE (solver->frames));
    Frame * f = solver->frames.begin + tmp;
    if (f->stamp != solver->stamp) {
      assert (f->stamp < solver->stamp);
      LOG ("pulling in decision level %d", tmp);
      f->stamp = solver->stamp;
      glue++;
    }
    if (tmp <= jump) continue;
    SWAP (int, solver->clause.begin[1], solver->clause.begin[j]);
    jump = tmp;
  }
  update_learned_clause_stats (solver, glue, size, jump);
  Clause * c;
  if (size > 1) {
    c = new_clause (solver, true, glue);
    LOGCLS (c, "learned");
    watch_clause (solver, c);
    trace_clause_addition (solver, c);
  } else {
    LOG ("new learned unit clause %d", -uip);
    assert (!jump);
    trace_unit_clause_addition (solver, -uip);
    CLEAR (solver->clause);
    c = 0;
  }
  backtrack (solver, jump);
  assign (solver, -uip, c);
  if (sadical->opts.bump) bump_analyzed (solver);
  CLEAR (solver->analyzed);
  return 0;
}

/*------------------------------------------------------------------------*/



static bool all_propagated (Solver * solver) {
  return solver->next_to_propagate == SIZE (solver->trail);
}

#ifndef NDEBUG

static bool all_simplified (Solver * solver) {
  return solver->local.units == solver->lim.simplify;
}

#endif

static bool all_assigned (Solver * solver) {
  assert (all_propagated (solver));
  return solver->max_var == SIZE (solver->trail);
}

static Var * next_relevant_variable (Solver * solver) {
  Var * res = 0;
  int idx = solver->queue.searched;
  for (;;) {
    assert (idx);
    res = var (solver, idx);
    if (!res->val) break;
    idx = res->prev;
  }
  solver->queue.searched = idx;
  assert (var (solver, idx) == res);
  return res;
}

static int next_relevant_literal (Solver * solver) {
  Var * v = next_relevant_variable (solver);
  int res = variable_index (solver, v);
  if (v->phase < 0) res = -res;
  return res;
}
/*------------------------------------------------------------------------*/

static bool restarting (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->opts.restart) return false;
  if (!solver->level) return false;
  if (!solver->balance) { solver->balance = 1; return true; }
  if (solver->lim.restart >= solver->local.conflicts) return false;
  double fast = solver->avg.glue.fast.val;
  double slow = solver->avg.glue.slow.val;
  double limit = slow * sadical->opts.restartmargin;
  bool res = fast > limit;
  MSG (4,
    "fast glue %.2f %s limit %.2f = %.2f * slow glue %.2f",
    fast, res ? ">" : "<=", limit, sadical->opts.restartmargin, slow);
  return fast > limit;
}

static int reuse_trail (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->opts.reuse) return 0;
  int reuse = 0, level = 0;
  Var * u = next_relevant_variable (solver);
  while (level < solver->level) {
    Frame * f = solver->frames.begin + level + 1;
    if (!f->lookahead) {
//      if (!sadical->opts.reuse) break;
      Var * v = var (solver, f->decision);
      if (v->enqueued < u->enqueued) break;
      reuse++;
    }
    level++;
  }
  if (reuse) {
    MSG (3, "reusing %d levels %.0f%% out of %d",
      reuse, PERCENT (reuse, solver->level), solver->level);
    INC_STATS (reused);
  }
  return level;
}

static void restart (Solver * solver) {
  INC_STATS (restarts);
  SaDiCaL * sadical = solver->sadical;
  MSG (3, "restart %ld at %ld conflicts",
    solver->local.restarts,  solver->local.conflicts);
  assert (!all_assigned (solver));
  int reuse = reuse_trail (solver);
  if (reuse < solver->level) backtrack (solver, reuse);
  solver->lim.restart = solver->local.conflicts + sadical->opts.restartint;
  MSG (3, "new restart limit %ld", solver->lim.restart);
}

static void trace_pruned_clause (Solver * solver) {

  SaDiCaL * sadical = solver->sadical;
  FILE * proof = sadical->proof;
  if (!proof) return;

  assert (sadical->outer == solver);
  Solver * inner = sadical->inner;

  Ints line;		// Save all literals to reuse 'trace_clause'.
  INIT (line);

  // First find a 'flipped' decision satisfying the negated trail, which
  // starts both the clause and the witness part of proof line.
  //
  int flipped = 0;
  for (int level = solver->level; !flipped && level > 0; level--) {
    Frame * f = solver->frames.begin + level;
    int decision = f->decision;
    int mapped = map (solver, decision);
    int tmp = val (inner, mapped);
    assert (tmp);
    if (tmp < 0) flipped = decision;
  }
  UNREACHABLE (!flipped);
  assert (flipped);
  assert (val (solver, flipped) > 0);
  assert (val (inner, map (solver, flipped)) < 0);
  PUSH (line, -flipped);

  // Now trace the rest of the decisions.
  //
  for (int level = solver->level; level > 0; level--) {
    Frame * f = solver->frames.begin + level;
    int decision = f->decision;
    if (decision == flipped) continue;
    PUSH (line, -decision);
  }

  // Finally trace the inner satisfying assignment (omega) starting again
  // with '-flipped', which marks the start of omega.
  //
  PUSH (line, -flipped);
  for (int * p = solver->trail.begin; p < solver->trail.end; p++) {
    int outer_lit = *p;
    if (outer_lit == flipped) continue;
    assert (outer_lit != -flipped);
    Var * v = var (solver, outer_lit);
    assert (v->stamp <= solver->stamp);
    if (v->stamp < solver->stamp) continue;	// Not mapped.
    int inner_lit = map (solver, outer_lit);
    int tmp = val (inner, inner_lit);
    int lit = tmp < 0 ? -outer_lit : outer_lit;
    PUSH (line, lit);
  }

  LOGLITS (line.begin, SIZE (line), "tracing pruned");
  trace_clause (solver, line.begin, SIZE (line), true, false);
  RELEASE (line);
} 

/*------------------------------------------------------------------------*/

// This function computes all interesting scores we have so far, which are
// based on the number of occurrences 'count', the 'weights', i.e., the
// sum of occurrences using the Jeroslow-Wang approach, the sum of all
// 'sizes' of clauses and the minimum size 'minsize' of a clause in which
// the literal occurs.  Except for the root level only reduced clauses are
// considered.

static void compute_scores (Solver * solver) {

  // First reset all scores.
  //
  size_t bytes = (2l * solver->max_var + 1l) * sizeof (Score);
  memset (solver->scores - solver->max_var, 0, bytes);

  // Now go over all clauses and updates scores of literals.
  //
  SaDiCaL * sadical = solver->sadical;
  bool autarky = sadical->opts.autarky;
  long counted = 0;
  for (Clause ** p = solver->clauses.begin; p < solver->clauses.end; p++) {

    Clause * c = *p;

    int falsified = 0, satisfied = 0;

    for (int i = 0; !satisfied && i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (tmp > 0) satisfied++;
      if (tmp < 0) falsified++;
    }

    // Skip all satisfied clauses (there are none on the root level).
    //
    if (satisfied) { assert (solver->level > 0); continue; }

    // Skip clauses which are neither reduced nor satisfied.  This is the
    // autarky decision heuristic used in look-ahead solvers.
    //
    if (autarky && solver->level > 0 && !falsified) continue;

    int size = c->size - falsified;	// Actual current size.
    assert (size > 1);

    // Compute weighted sum (JWH score).
    //
    double w = 1;
    for (int i = 0; i < size; i++) w *= 0.5;

    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (tmp < 0) continue;
      assert (!tmp);
      Score * s = score (solver, lit);
      s->count++;
      s->sizes += size;
      s->weights += w;

      // There should not be any unary or empty clauses in the formula,
      // thus '!s->minsize' actually means not clause found yet.
      //
      if (!s->minsize || size < s->minsize)
	s->minsize = size;
    }

    counted++;
  }

  LOG ("computed scores over %ld unsatisfied clauses", counted);
}

/*------------------------------------------------------------------------*/

static void collect_negated_decisions (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  for (int i = solver->level; i > 0; i--) {
    Frame * f = solver->frames.begin + i;
    PUSH (solver->clause, -f->decision);
  }
}

/*------------------------------------------------------------------------*/

// Root-level pure literals should be treated explicitly.

static void pure_literal (Solver * solver, int lit) {
  assert (!solver->level);
  assert (!score (solver, -lit)->count);
  LOG ("pure literal %d in %d clauses", lit, score (solver, lit)->count);
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->outer == solver);
  sadical->pure++;
  trace_unit_clause_addition (solver, lit);
  assign (solver, lit, 0);
}

/*------------------------------------------------------------------------*/

// This is the standard 'literal individual sum' (LIS) heuristic.  It
// simply use the 'count' score computed by 'compute_score', which gives
// the number of unsatisfied clauses in which a literal occurs (restricted
// to the autarky heuristics, i.e., to reduced clauses for non-root
// decision level).

static int look_ahead_lis (Solver * solver) {
  compute_scores (solver);
  SaDiCaL * sadical = solver->sadical;
  int max_var = solver->max_var, res = 0, best = -1, pure = 0;
  for (int lit = -max_var; !pure && lit <= max_var; lit++) {
    if (!lit) continue;
    if (val (solver, lit)) continue;
    Score * s = score (solver, lit);
    if (!solver->level && !s->count) pure = -lit;
    if (s->flipped <= best) continue;
    best = s->flipped;
    res = abs(lit);
  }
  if (pure) pure_literal (solver, pure), res = INT_MIN;
  else MSG (3, "best LIS literal %d occurs maximum %ld times", res, best);
  return res;
}

/*------------------------------------------------------------------------*/

// The same but using the weight sum (JWH).

static int look_ahead_jwh (Solver * solver) {
  compute_scores (solver);
  SaDiCaL * sadical = solver->sadical;
  int max_var = solver->max_var, res = 0, pure = 0;
  double best = -1;
  for (int lit = -max_var; !pure && lit <= max_var; lit++) {
    if (!lit) continue;
    if (val (solver, lit)) continue;
    Score * s = score (solver, lit);
    if (!solver->level && !s->count) pure = -lit;
    if (s->weights <= best) continue;
    best = s->weights;
    res = lit;
  }
  if (pure) pure_literal (solver, pure), res = INT_MIN;
  else MSG (3, "best JWH literal %d with weighted sum %g", res, best);
  return res;
}

/*------------------------------------------------------------------------*/

// The heuristic we used for root level decisions in our implementation
// for our HVC'17 paper, which worked for pigeon hole 'PHP' formulas
// (smallest 'count' first then largest 'sizes/count' - see also
// 'lglprunedecidefirst').

static int root_look_ahead_php (Solver * solver) {
  compute_scores (solver);
  assert (!solver->level);
  SaDiCaL * sadical = solver->sadical;
  int max_var = solver->max_var, res = 0, pure = 0, bestcount = INT_MAX;
  double bestratio = INT_MIN;
  for (int lit = -max_var; lit <= max_var; lit++) {
    if (!lit) continue;
    if (val (solver, lit)) continue;
    Score * s = score (solver, lit);
    if (!s->count) { pure = -lit; break; }
    if (s->count > bestcount) continue;
    double tmp = s->sizes / s->count;
    if (s->count == bestcount && tmp <= bestratio) continue;
    bestcount = s->count;
    bestratio = tmp;
    res = lit;
  }
  if (pure) pure_literal (solver, pure), res = INT_MIN;
  else MSG (3,
	 "best root PHP literal %d with count %d sizes/count ratio %g",
	 res, bestcount, bestratio);
  return res;
}

/*------------------------------------------------------------------------*/

// The heuristic we used for non-root level decisions in our
// implementation for our HVC'17 paper, which worked for pigeon hole 'PHP'
// formulas (occurs in smallest reduced clause - see 'lglprunedecidelater').

static int non_root_look_ahead_php (Solver * solver) {
  compute_scores (solver);
  assert (solver->level > 0);
  SaDiCaL * sadical = solver->sadical;
  int max_var = solver->max_var, res = 0;
  int best = INT_MAX;
  for (int lit = -max_var; lit <= max_var; lit++) {
    if (!lit) continue;
    if (val (solver, lit)) continue;
    Score * s = score (solver, lit);
    if (s->minsize >= best) continue;	// TODO What about '!s->count'?
    best = s->minsize;
    res = abs(lit);
  }
  MSG (3, "best non-root PHP literal %d with min-size %d", res, best);
  return res;
}

/*------------------------------------------------------------------------*/

static int root_look_ahead_tseitin (Solver * solver) {
  return root_look_ahead_php (solver);			// TODO ?
}

static int non_root_look_ahead_tseitin (Solver * solver) {
  return non_root_look_ahead_php (solver);		// TODO ?
}

/*------------------------------------------------------------------------*/

static int next_root_look_ahead_literal (Solver * solver) {

  SaDiCaL * sadical = solver->sadical;
  if (!sadical->opts.prune) return 0;
  
  int res, heuristic = sadical->opts.root;

       if (solver->mode == MODE_LOOKAHEAD) heuristic = 3;
  else if (solver->mode == MODE_RELEVANT)  heuristic = 5;

  switch (heuristic) {
    case 1: res = look_ahead_lis (solver); break;
    case 2: res = look_ahead_jwh (solver); break;
    case 3: res = root_look_ahead_php (solver); break;
    case 4: res = root_look_ahead_tseitin (solver); break;
    default: res = next_relevant_literal (solver); break;
  }

  MSG (3, "root selected %i", res);

  return res;
}

static int next_non_root_look_ahead_literal (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  int res;

  if (sadical->opts.prune) {
    if (solver->mode == MODE_LOOKAHEAD) sadical->opts.nonroot = 3;
    if (solver->mode == MODE_RELEVANT)  sadical->opts.nonroot = 5;
  }

  switch (sadical->opts.nonroot) {
    case 1: res = look_ahead_lis (solver); break;
    case 2: res = look_ahead_jwh (solver); break;
    case 3: res = non_root_look_ahead_php (solver); break;
    case 4: res = non_root_look_ahead_tseitin (solver); break;
    default:
      res = next_relevant_literal (solver);
      break;
  }
  MSG (3, "nonroot selected %i", res);
  return res;
}

static bool use_look_head (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (solver == sadical->inner) return false;
  if (!sadical->opts.prune) return false;
  if (solver->level >= sadical->opts.level) return false;
  return true;
}

static int next_look_ahead_literal (Solver * solver) {
  double start = sadical_process_time ();
  SaDiCaL * sadical = solver->sadical;
  assert (solver == sadical->outer);
  sadical->lookaheads++;
  int lit;
  if (!solver->level) lit = next_root_look_ahead_literal (solver);
  else lit = next_non_root_look_ahead_literal (solver);
  sadical->time.looking += sadical_process_time () - start;
  return lit;
}

static void decide (Solver * solver) {
  assert (all_propagated (solver));
  assert (!all_assigned (solver));
  assert (!solver->inconsistent);
  int lit;
  Frame frame;
  memset (&frame, 0, sizeof frame);
  frame.trail = SIZE (solver->trail);
  if (use_look_head (solver)) {
    lit = next_look_ahead_literal (solver);
    if (lit == INT_MIN) return;
    solver->level++;
    LOG ("decide %d look-ahead based", lit);
    frame.lookahead = true;
  } else {
    lit = next_relevant_literal (solver);
    solver->level++;
    LOG ("decide %d relevance based", lit);
    frame.lookahead = false;
  }
  frame.decision = lit;
  SaDiCaL * sadical = solver->sadical;
  PUSH (solver->frames, frame);
  assert (SIZE (solver->frames) == solver->level + 1);
  INC_STATS (decisions);
  assign (solver, lit, 0);
}

/*------------------------------------------------------------------------*/

static void flush_garbage_watches (Watches * ws) {
  Watch * q = ws->begin;
  for (Watch * p = q; p < ws->end; p++) {
    Watch w = *p;
    Clause * c = w.clause;
    if (!c->garbage) *q++ = w;
  }
  ws->end = q;
}

static void flush_garbage (Solver * solver) {
  for (int lit = -solver->max_var; lit <= solver->max_var; lit++)
    if (lit) flush_garbage_watches (watches (solver, lit));
  long collected = 0;
  Clause ** q = solver->clauses.begin;
  for (Clause ** p = q; p < solver->clauses.end; p++) {
    Clause * c = *p;
    if (c->garbage) {
      if (c->reason) *q++ = c;
      else {
	trace_clause_deletion (solver, c);
	collected += delete_clause (solver, c);
      }
    } else *q++ = c;
  }
  solver->clauses.end = q;
  SaDiCaL * sadical = solver->sadical;
  MSG (2, "collected %.1f KB (%ld Bytes)",
    collected / (double)(1<<10), collected);
}

/*------------------------------------------------------------------------*/

static bool simplifying (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (sadical->inner == solver) return false;
  assert (!solver->inconsistent);
  assert (all_propagated (solver));
  return solver->local.units > solver->lim.simplify;
}

// Propagate root level units and flush them from the formula.

static void simplify (Solver * solver) {
  double start = sadical_process_time ();
  long units = solver->local.units - solver->lim.simplify;
  SaDiCaL * sadical = solver->sadical;
  MSG (2, "simplifying formula after %ld unit clauses", units);
  INC_STATS (simplifications);
  solver->mode = MODE_LOOKAHEAD;
  assert (!solver->level);
  assert (units > 0);
  assert (!solver->inconsistent);
  assert (all_propagated (solver));
  int ccnt = -1;
  long garbage = 0, removed = 0;
  for (Clause ** p = solver->clauses.begin; p < solver->clauses.end; p++) {
    Clause * c = *p;
    ccnt++;
    bool satisfied = false, falsified = false;
    for (int i = 0; !satisfied && i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (tmp > 0) satisfied = true;
      if (tmp < 0) falsified = true;
    }
    if (satisfied) {
      LOGCLS (c, "root level satisfied");
      c->garbage = true;
      garbage++;
      MSG (3, "garb %d", ccnt);
    } else if (falsified) {
      LOGCLS (c, "shrinking");
      trace_clause_shrinking (solver, c);
      removed += remove_falsified_literals_from_clause (solver, c);
      MSG (3, "reduced %d", ccnt);
    }
  }
  LOG ("marked %ld clauses as garbage", garbage);
  LOG ("removed %ld literals", removed);
  ADD_STATS (clauses.collected, removed * sizeof (int));
  flush_garbage (solver);
  solver->lim.simplify = solver->local.units;
  sadical->time.simplifying += sadical_process_time () - start;
  sadical_report (sadical, 's');
}

/*------------------------------------------------------------------------*/

static bool reducing (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  if (!sadical->opts.reduce) return false;
  return solver->lim.reduce < solver->local.conflicts;
}

static int cmp_reduce (const void * p, const void * q) {
  Clause * c = * (Clause **) p;
  Clause * d = * (Clause **) q;
  if (c->glue < d->glue) return 1;		// large glue first
  if (c->glue > d->glue) return -1;
  if (c->size < d->size) return 1;		// large size first
  if (c->size > d->size) return -1;
  if (c->added < d->added) return -1;		// high age first
  if (c->added > d->added) return 1;
  UNREACHABLE (c->added == d->added);
  return 0;					// unreachable
}

static void reduce (Solver * solver) {
  INC_STATS (reductions);
  SaDiCaL * sadical = solver->sadical;
  MSG (3, "reduce %ld at %ld conflicts",
    solver->local.reductions,  solver->local.conflicts);
  Clauses candidates;
  INIT (candidates);
  for (Clause ** p = solver->clauses.begin;
                 p < solver->clauses.end; p++) {
    Clause * c = *p;
    bool used = c->used;
    c->used = false;
    if (used) continue;
    if (c->garbage) continue;
    if (!c->redundant) continue;
    if (c->reason) continue;
    if (c->size <= sadical->opts.keepsize) continue;
    if (c->glue <= sadical->opts.keepglue) continue;
    PUSH (candidates, c);
  }
  long size = SIZE (candidates);
  MSG (2, "found %ld reduction candidates", size);
  qsort (candidates.begin, size, sizeof (Clause*), cmp_reduce);
  long target = size/2;
  MSG (2, "reducing %ld clauses", target);
  for (long i = 0; i < target; i++) {
    Clause * c = PEEK (candidates, i);
    LOGCLS (c, "reducing");
    c->garbage = true;
  }
  RELEASE (candidates);
  flush_garbage (solver);
  solver->lim.reduce = solver->local.conflicts + solver->inc.reduce;
  solver->inc.reduce += sadical->opts.reduceinc;
  MSG (2, "new reduce limit %ld increment %ld",
    solver->lim.reduce, solver->inc.reduce);
  sadical_report (sadical, '-');
}

/*------------------------------------------------------------------------*/

static void delete_clauses (Solver * solver) {
  while (!EMPTY (solver->clauses)) {
    Clause * c = POP (solver->clauses);
    delete_clause (solver, c);
  }
}

/*------------------------------------------------------------------------*/

static void assume (Solver * solver, int lit) {
  SaDiCaL * sadical = solver->sadical;
  Frame frame;
  memset (&frame, 0, sizeof frame);
  frame.decision = lit;
  frame.trail = SIZE (solver->trail);
  PUSH (solver->frames, frame);
  solver->level++;
  assert (SIZE (solver->frames) == solver->level + 1);
  sadical->reduct.filter.assumed++;
  LOG ("assume %d", lit);
  assign (solver, lit, 0);
}

static bool filter_clause (Solver * solver, Clause * c) {
  double start = sadical_process_time ();
  SaDiCaL * sadical = solver->sadical;
  LOGCLS (c, "filtering");
  sadical->reduct.filter.checked++;
  LOG ("switching off phase saving");
  assert (!solver->do_not_save_phases);
  solver->do_not_save_phases = true;
  int level = solver->level;
  long props = solver->local.propagations;
//  printf ("c filtering: ");
  for (int i = 0; i < c->size; i++) {
    int lit = c->literals[i];
//    printf ("%i ", lit);
    int tmp = val (solver, lit);
    if (tmp) continue;
    assume (solver, -lit);
  }
  Clause * conflict = propagate (solver);
//  printf ("0 (%i)\n", conflict == 0);

  backtrack (solver, level);
  props = solver->local.propagations - props;
  LOG ("filtering used %ld propagations", props);
  sadical->reduct.filter.propagations += props;
  sadical->time.filtering += sadical_process_time () - start;
  LOG ("switching on phase saving");
  assert (solver->do_not_save_phases);
  solver->do_not_save_phases = false;
  return conflict != 0;
}

/*------------------------------------------------------------------------*/

static void add_literal (Solver *, int lit);

// Copy the (filtered) positive reduct to the inner solver.

static void generate_reduct (Solver * solver) {
  double start = sadical_process_time ();
  SaDiCaL * sadical = solver->sadical;
  assert (solver == sadical->outer);
  Solver * inner = sadical->inner;
  assert (!inner->max_var);

  INC_STATS(reducts_generated);
  
  bool filter = sadical->opts.filter;
  if (filter) LOG ("generating filtered positive reduct");
  else LOG ("generating positive reduct");
  sadical->reduct.generated++;

  LOG ("adding negation of current trail of size %ld",
    (long) SIZE (solver->trail));
  solver->stamp++;
  for (int level = solver->level; level > 0; level--) {
    Frame * f = solver->frames.begin + level;
    int decision = f->decision;
    int mapped = map (solver, decision);
    add_literal (inner, -mapped);
  }
  add_literal (inner, 0);

//  printf ("c trail: ");
//  for (int * p = solver->trail.begin; p < solver->trail.end; p++) {
//    printf ("%i ", *p); }
//  printf ("0\n");

  LOG ("adding all satisfied clauses to reduct");
  for (Clause ** p = solver->clauses.begin;
       !inner->inconsistent && p < solver->clauses.end;
       p++) {

    sadical->reduct.clauses.considered++;

    Clause * c = *p;
    if (c->garbage) { // Joseph
//      MSG (c, "skipping garbage");
      continue;
    }
//    if (c->redundant) {
//      LOGCLS (c, "skipping redundant");
//      continue;
//    }
    int satisfied = 0, unassigned = 0;
    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (tmp > 0) satisfied++;
      if (!tmp) unassigned++;
    }

    if (!satisfied) {
      LOGCLS (c, "skipping unsatisfied");
      continue;
    }

    if (filter) {
      if (unassigned) {
	if (filter_clause (solver, c)) {
	  LOGCLS (c, "filtered");
	  sadical->reduct.clauses.filtered++;
	  continue;
	}
      } else LOGCLS (c, "skipping filtering for all assigned");
    }

    LOGCLS (c, "copying to positive reduct");
    sadical->reduct.clauses.copied++;

    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (!tmp) continue;		// Skip unassigned outer literals.
      int mapped = map (solver, lit);
      add_literal (inner, mapped);
    }
    add_literal (inner, 0);
  }
  
//  if (!filter) {
//    // propagate top-level units
//    for (int i = 0; i < SIZE (solver->units); i++) {
//      int lit = PEEK (solver->units, i);
//      assign (inner, lit, 0);
//      propagate (inner);
//    }
//  }
  sadical->time.generating += sadical_process_time () - start;
}

static void clear_inner_solver (Solver *);
static int solve (Solver *);

static bool reduct_satisfiable (Solver * solver) {
  double start = sadical_process_time ();
  SaDiCaL * sadical = solver->sadical;
  assert (solver == sadical->outer);
  int res = (solve (sadical->inner) == 10);
  if (res) INC_STATS(reducts_satisfiable);
  sadical->time.pruning += sadical_process_time () - start;
  return res;
}

static bool prune (Solver * solver) {
  if (!solver->level) return false;
  assert (solver->level < SIZE (solver->frames));
  Frame * f = solver->frames.begin + solver->level;
  if (!f->lookahead) {
    LOG ("will not prune non-look-ahead decision level %d", solver->level);
    return false;
  }
  double start = sadical_process_time ();
  SaDiCaL * sadical = solver->sadical;
  LOG ("pruning");
  assert (sadical->outer == solver);
  assert (sadical->opts.prune);
  assert (solver->level <= sadical->opts.level);
  assert (all_propagated (solver));
  assert (all_simplified (solver));
  generate_reduct (solver);
  bool res;
  if (reduct_satisfiable (solver)) {
    LOG ("pruning successful");
    MSG (3, "pruning successful");
    sadical->pruned++;
    INC_STATS (conflicts);
    int glue = solver->level;
    int size = solver->level;
    int jump = solver->level - 1;

    update_learned_clause_stats (solver, glue, size, jump);
    int last = PEEK (solver->frames, solver->level).decision;
    Clause * c;
    if (size > 1) {
      assert (EMPTY (solver->clause));
      collect_negated_decisions (solver);
      c = new_clause (solver, true, glue);
      LOGCLS (c, "pruned");
      watch_clause (solver, c);
    } else {
      assert (size == 1);
      LOG ("pruned unit clause %d", -last);
      c = 0;
    }

    // The order in which flipped variables are bumped is highly important
    // for the performance. This is likely caused by learning PR clauses
    // that can be resolved with each other. The order below bumps all
    // flipped variables, but keeps them in order.

    Solver * inner = sadical->inner;
    int count = 0, decisions = 0, assigned = 0;
    for (int * p = solver->trail.end - 1; p >= solver->trail.begin; p--) {
      assigned++;
      int outer_lit = *p;
      int mapped = map (solver, outer_lit);
      int tmp = val (inner, mapped);
      if (tmp >= 0) continue;
      count++;
      MSG (3, "flipped %i", outer_lit);
      if (solver->level <= 2) continue;
      int idx = variable_index (solver, var (solver, outer_lit));
      if (idx == solver->queue.last) continue;
      dequeue (solver, idx);
      enqueue_last (solver, idx);
    }
    MSG (3, "flipped %i out of %i literals", count, assigned);

    count = 0;
    for (int level = solver->level; level > 0; level--) {
      decisions++;
      Frame * f = solver->frames.begin + level;
      int decision = f->decision;
      int mapped = map (solver, decision);
      int tmp = val (inner, mapped);
      assert (tmp);
      if (tmp < 0) { count++; MSG (3, "decision flipped %i", decision); }
    }

    if (count != decisions) {
      MSG (3,
        "unbalanced prune (%i/%i): restart before next decision",
	count, decisions);
      solver->balance = 0;
    }

    if (solver->level > 2) {
      solver->mode = MODE_RELEVANT;
      MSG (3, "switching to 'RELEVANT MODE' at decision level '%d",
        solver->level);
    }

    trace_pruned_clause (solver);

    backtrack (solver, jump);
    assign (solver, -last, c);

    res = true;

  } else {
    LOG ("pruning failed");
    MSG (3, "pruning failed");
    sadical->reduct.unsat++;
    res = false;
  }
  clear_inner_solver (sadical->inner);
  sadical->time.pruning += sadical_process_time () - start;
  return res;
}

//------------------------------------------------------------------------------

// START OF PR EXTRACT

// Writing clauses and witnesses and adding learned clauses to the outer solver
// pr_units.cnf       - list of units learned
// pr_units_full.dpr  - units with witnesses (dpr proof format)
// pr_clauses.cnf     - list of clauses learned
// pr_clauses_full.dpr - list of clauses and witnesses (dpr proof format)

void prext_write_clause
(Solver * solver, Candidate_PR * cand_pr , int pr, int lit) {
  assert (!solver->level);
  SaDiCaL * sadical = solver->sadical;
  solver->new_pr++;
  if (!pr) { // learned a unit
    INC_STATS(added_units);
    PUSH (solver->units, lit);
    fprintf(solver->pr_clause_out, "%d 0\n", lit);
    fprintf(solver->pr_clause_full_out, "%d 0\n", lit);
    fprintf(solver->pr_units, "%d 0\n", lit);
    fprintf(solver->pr_units_full, "%d 0\n", lit);
    MSG (1, "Adding unit idx %d", lit);
    assign (solver, lit, 0);
    Clause *conflict = propagate (solver);
    if (!conflict) simplify (solver);       // remove variable from formula
    else solver->top_level_conflict = true; // unit caused conflict, UNSAT
    fflush (solver->pr_clause_out);
    fflush (solver->pr_clause_full_out);
    fflush (solver->pr_units);
    fflush (solver->pr_units_full);
    return;
  }
  
  int * cls = cand_pr->pr_clause;
  int cls_size = cand_pr->pr_size;
  int * wit = cand_pr->witness;
  int wit_size = cand_pr->wit_size;
  MSG(1, "ADDING PR Clause: ");
  
  if (cls_size == 1) { // learned PR unit
    PUSH (solver->units, cls[0]);
    INC_STATS(added_units_pr);
    assign (solver, cls[0], 0);
    Clause *conflict = propagate (solver);
    if (!conflict) simplify (solver);       // remove variable from formula
    else solver->top_level_conflict = true; // unit caused conflict, UNSAT
    fprintf(solver->pr_units, "%d 0\n", cls[0]);
  }
  if (cls_size == 2) INC_STATS(added_binaries_pr);
  if (cls_size == 3) INC_STATS(added_trinaries_pr);
  
  int flipped = 0;
  for (int j = 0; j < cls_size; j++) {  // flipped literal appears first in wit
    for (int z = 0; z < wit_size; z++) {
      if (cls[j] == wit[z]) {
        flipped = cls[j];
        break;
      }
    }
    if (flipped) break;
  }
  if (flipped) {
    fprintf(solver->pr_clause_out, "%d ", flipped);
    fprintf(solver->pr_clause_full_out, "%d ", flipped);
    if (cls_size == 1) fprintf(solver->pr_units_full, "%d ", flipped);
    PUSH (solver->clause, flipped);
  }
  for (int j = 0; j < cls_size; j++) {
    if (flipped != cls[j]) {
      fprintf(solver->pr_clause_out, "%d ", cls[j]);
      fprintf(solver->pr_clause_full_out, "%d ", cls[j]);
      PUSH (solver->clause, cls[j]);
    }
  }
  if (flipped) {
    fprintf(solver->pr_clause_full_out, "%d ", flipped);
    if (cls_size == 1) fprintf(solver->pr_units_full, "%d ", flipped);
    for (int j = 0; j < wit_size; j++) {
      if (flipped != wit[j])
      {
        fprintf(solver->pr_clause_full_out, "%d ", wit[j]);
        if (cls_size == 1) fprintf(solver->pr_units_full, "%d ", wit[j]);
      }
    }
  }
  fprintf(solver->pr_clause_out, "0\n");
  fprintf(solver->pr_clause_full_out, "0\n");
  if (cls_size == 1 ) fprintf(solver->pr_units_full, "0\n");
  
  if (cls_size > 1) { // Add pr clause to solver
    Clause * c = new_clause (solver, false, 0);
    watch_clause (solver, c);
  }
  CLEAR (solver->clause);
  fflush (solver->pr_clause_out);
  fflush (solver->pr_clause_full_out);
  fflush (solver->pr_units);
  fflush (solver->pr_units_full);
}


/*------------------------------------------------------------------------*/

// Solver related functions

// Called when a pruning predicate is solved and satisfiable.
// Stores the PR clause (clause that blocks the assignment) only
// including decision variables, the witness, and the trail
// in cand_pr.
void prext_store_pruned_clause_witness
(Solver * solver, Candidate_PR * cand_pr) {
  SaDiCaL * sadical = solver->sadical;
  Solver * inner = sadical->inner;
  Ints line;    // Save all literals to reuse 'trace_clause'.
  INIT (line);
  cand_pr->wit_size = 0;
  cand_pr->pr_size = 0;
  
  // Trace decisions to construct PR clause
  for (int level = solver->level; level > 0; level--) {
    Frame * f = solver->frames.begin + level;
    int decision = f->decision;
    PUSH (line, -decision);
    cand_pr->pr_size++;
  }
  cand_pr->pr_clause = malloc (sizeof (int) * cand_pr->pr_size);
  for (int i = 0; i < cand_pr->pr_size; i++) cand_pr->pr_clause[i] = PEEK (line, i);
  CLEAR (line);
  
  cand_pr->trail_size = SIZE (solver->trail);
  cand_pr->trail = malloc (sizeof (int) * cand_pr->trail_size);
  
  int ts = 0;
  // Finally trace the inner satisfying assignment (omega) starting again
  // with '-flipped', which marks the start of omega.
  for (int * p = (solver->trail.begin); p < solver->trail.end; p++) {
    int outer_lit = *p;
    cand_pr->trail[ts++] = outer_lit;
    Var * v = var (solver, outer_lit);
    assert (v->stamp <= solver->stamp);
    if (v->stamp < solver->stamp) continue;  // Not mapped.
    int inner_lit = map (solver, outer_lit);
    int tmp = val (inner, inner_lit);
    int lit = tmp < 0 ? -outer_lit : outer_lit;
    PUSH (line, lit);
    cand_pr->wit_size++;
  }
  
  cand_pr->witness = malloc (sizeof (int) * cand_pr->wit_size);
  for (int i = 0; i < cand_pr->wit_size; i++) cand_pr->witness[i] = PEEK (line, i);
  
  RELEASE (line);
}

// Assigns a literal as if it were a decision in the outer solver
void prext_assign_lit(Solver * solver, int lit) {
  assert (all_propagated (solver));
  assert (!all_assigned (solver));
  assert (!solver->inconsistent);
  assert (!val (solver, lit));
  SaDiCaL * sadical = solver->sadical;
  MSG (1, "PR assigning decsision lit %d",lit);
  Frame frame;
  memset (&frame, 0, sizeof frame);
  frame.trail = SIZE (solver->trail);
  solver->level++;
  frame.lookahead = true;
  frame.decision = lit;
  PUSH (solver->frames, frame);
  assert (SIZE (solver->frames) == solver->level + 1);
  assign (solver, lit, 0);
}

// Checks if lit is a unit or a PR unit
// If so, adds the unit to the formula and simplifies the formula
bool prext_check_unit (Solver * solver, int lit) {
  assert (!solver->level);
  prext_assign_lit (solver, lit);
  Clause * conflict = propagate (solver);
  SaDiCaL * sadical = solver->sadical;
  
  if (conflict) { // Found Uni
    backtrack (solver, solver->level-1);
    prext_write_clause(solver, NULL, 0, -lit);
    return true;
  }
  if (sadical->opts.pre_unit) {
    MSG (1, "Generate Unit Pr reduct");
    generate_reduct (solver);
    if (reduct_satisfiable (solver)) {
      LOG ("pruning successful");
      Candidate_PR * cand_pr = new_candidate_pr(solver,lit);
      prext_store_pruned_clause_witness (solver, cand_pr);
      backtrack (solver, solver->level-1);
      prext_write_clause(solver, cand_pr, 1, 0);
      clear_inner_solver (sadical->inner);
      delete_candidate_pr (solver, cand_pr);
      return true;
    }
    clear_inner_solver (sadical->inner);
  }
  backtrack (solver, solver->level-1);
  return false;
}

int cmpfunc (const void * a, const void * b) {
  return ( *(int*)b - *(int*)a );
}


//------------------------------------------------------------------------------

// Pr Extraction "finding PR clauses"
// touched (i) and reduced heuristics that return a set of variables given an
// input asignment
// find () selects the heuritic and returns the set of variables

int * prext_get_neighbors
(Solver * solver, Partial_PR * part_pr, int * ntouched) {
  SaDiCaL * sadical = solver->sadical;
  double start = sadical_process_time ();
  
  int depth_i = sadical->opts.pre_neighbors_depth;
  int lit, tch;
  *ntouched = 0;
  STACK (int) touched_ls;
  INIT (touched_ls);
  int * touched = 0;
  long time = solver->find_time;
  
  for (int t = 0; t < SIZE (solver->trail); t++) { // touched from trail
    lit = PEEK (solver->trail, t);
    for (int i = 0; i < SIZE (solver->touched_list[abs(lit)]); i++) {
      tch = PEEK (solver->touched_list[abs(lit)], i);
      if (solver->find_vars[abs(tch)] != time) {
        PUSH (touched_ls, tch);
        (*ntouched)++;
        solver->find_vars[abs(tch)] = time;
      }
    }
  }
  
  for (int s = 0; s < depth_i; s++) { // expand touched depth_i times
    int orig_size = SIZE (touched_ls);
    for (int t = 0; t < orig_size ; t++) {
      lit = PEEK (touched_ls, t);
      for (int i = 0; i < SIZE (solver->touched_list[abs(lit)]); i++) {
        tch = PEEK (solver->touched_list[abs(lit)], i);
        if (solver->find_vars[abs(tch)] != time) {
          PUSH (touched_ls, tch);
          (*ntouched)++;
          solver->find_vars[abs(tch)] = time;
        }
      }
    }
  }
  
  if (*ntouched) { // store variables in touched[]
    touched = malloc (sizeof (int) * (*ntouched));
    for (int j = 0; j < SIZE (touched_ls); j++) {
      touched[j] = PEEK (touched_ls, j);
    }
  }

  RELEASE (touched_ls);
  sadical->time.exploring += sadical_process_time () - start;
  solver->find_time++;
  return touched;
}

// Returns the set of variables from reduced but not satisfied clauses
// This heuristic is meant to guide decisions towards conditional autarkies
int * prext_get_reduced
 (Solver * solver, Partial_PR * part_pr, int * ntouched) {
  SaDiCaL * sadical = solver->sadical;
  double start = sadical_process_time ();
  STACK (int) touched_ls;
  INIT (touched_ls);
  int tch,satisfied = 0, reduced=0;;
  *ntouched = 0;
  long time = solver->find_time;
  int * touched = 0;
  
  for (Clause ** p = solver->clauses.begin; p < solver->clauses.end; p++) {
    Clause * c = *p;
    reduced = 0;
    satisfied = 0;
    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      int tmp = val (solver, lit);
      if (tmp > 0) {satisfied=1;
        break;
      }
      if (tmp < 0) reduced = 1;
    }
    if (!satisfied && reduced) {
      for (int i = 0; i < c->size; i++) {
        tch = c->literals[i];
        if (val (solver, tch)) continue;
        if (solver->find_vars[abs(tch)] != time) {
          PUSH (touched_ls, tch);
          (*ntouched)++;
          solver->find_vars[abs(tch)] = time;
        }
      }
    }
  }

  if (*ntouched) { // store variables in touched[]
    touched = malloc (sizeof (int) * (*ntouched));
    for (int j = 0; j < SIZE (touched_ls); j++) touched[j] = PEEK (touched_ls, j);
  }
  RELEASE (touched_ls);
  sadical->time.exploring += sadical_process_time () - start;
  solver->find_time++;
  return touched;
}

int * neighbors_cnt;

int neighbor_cmp (const void *a, const void *b) {
  int * first = (int *) a;
  int * secon = (int *) b;
  
  if (neighbors_cnt[abs(*first)] < neighbors_cnt[abs(*secon)]) return 1;
  else if (neighbors_cnt[abs(*first)] > neighbors_cnt[abs(*secon)]) return -1;
  else return 0;
}

// touched (i) giving variables touched but counting how often they are touched by the trail
// +1 for every literal on the trail touching it

// would like a hashmap implmentation (lit, count)
// will settle for vector with variable map using a timestamp?
// Array (lit, timestamp), Map (lit, mapID), vector (mapID, Cnt)
int * prext_get_neighbors_count
(Solver * solver, Partial_PR * part_pr, int * ntouched) {
  SaDiCaL * sadical = solver->sadical;
  double start = sadical_process_time ();
  
  int depth_i = sadical->opts.pre_neighbors_depth;
  int lit, tch;
  *ntouched = 0;
  STACK (int) touched_ls;
  INIT (touched_ls);
  int * touched = 0;
  long time = solver->find_time;
  
  for (int t = 0; t < SIZE (solver->trail); t++) { // touched from trail
    lit = PEEK (solver->trail, t);
    for (int i = 0; i < SIZE (solver->touched_list[abs(lit)]); i++) {
      tch = PEEK (solver->touched_list[abs(lit)], i);
      if (solver->find_vars[abs(tch)] != time) {
        PUSH (touched_ls, abs(tch));
        (*ntouched)++;
        solver->find_vars[abs(tch)] = time;
      }
      neighbors_cnt[abs(tch)] += 1;
    }
  }
  
  for (int s = 0; s < depth_i; s++) { // expand touched depth_i times
    int orig_size = SIZE (touched_ls);
    for (int t = 0; t < orig_size ; t++) {
      lit = PEEK (touched_ls, t);
      for (int i = 0; i < SIZE (solver->touched_list[abs(lit)]); i++) {
        tch = PEEK (solver->touched_list[abs(lit)], i);
        if (solver->find_vars[abs(tch)] != time) {
          PUSH (touched_ls, abs(tch));
          (*ntouched)++;
          solver->find_vars[abs(tch)] = time;
        }
        neighbors_cnt[abs(tch)] += 1;
      }
    }
  }
  
  if (*ntouched) { // store variables in touched[]
    touched = malloc (sizeof (int) * (*ntouched));
    for (int j = 0; j < SIZE (touched_ls); j++) {
      touched[j] = PEEK (touched_ls, j);
    }
  }
  
  // sort touched based on solver list
  qsort (touched, *ntouched, sizeof (int), neighbor_cmp);
  
  // cutoff some from touched if you so choose
  int cutoff_cnt = 0, cutoff_pos = 0;
  
  for (int j = 0; j < SIZE (touched_ls); j++) {
    if (neighbors_cnt[touched[j]] < cutoff_cnt) break;
    cutoff_pos++;
  }
  
//  cutoff_pos = 2;
  
  if (cutoff_pos < *ntouched) {
    *ntouched = cutoff_pos;
    if (*ntouched == 0) free (touched);
  }
  
  // reset counts
  for (int j = 0; j < SIZE (touched_ls); j++) {
    neighbors_cnt[PEEK (touched_ls, j)] = 0;
  }

  RELEASE (touched_ls);
  sadical->time.exploring += sadical_process_time () - start;
  solver->find_time++;
  
  return touched;
}

// Returns a ser of literals for generating candidate PR clauses
// Returns either reduced, neighbors by count, or neighbors (i)
int * prext_find
(Solver * solver, Partial_PR * part_pr, int * ntouched) {
  SaDiCaL * sadical = solver->sadical;
  int *touched;
  
  if (sadical->opts.pre_reduced)
    touched = prext_get_reduced (solver, part_pr, ntouched);
  else if (sadical->opts.pre_neighbors_count)
    touched = prext_get_neighbors_count (solver, part_pr, ntouched);
  else
    touched = prext_get_neighbors (solver, part_pr, ntouched);
  
  if (!sadical->opts.pre_neighbors_count && ntouched) {
    // standard order under shuffled clauses
    qsort (touched, *ntouched, sizeof (int), cmpfunc);
  }
  
  return touched;
}


// Find the candidate PR clauses given a variable x.
// Candiate PR clauses are constructing starting from x and adding variables
// from find ().
// With learning configuration addinstant, PR clauses are learned as they are
// found.
// Before and after finding clauses, x is checked to see if it is unit.
Candidate_Queue * prext_find_candidates
 (Solver * solver, Candidate_Queue * candidate_queue, int i) {
  Candidate_PR * cand_pr = PEEK (candidate_queue->candidate_prs,i);
  Partial_PR *part_pr, *copy_pr;
  Clause * conflict;
  SaDiCaL * sadical = solver->sadical;
  candidate_queue->seen[abs(cand_pr->idx)] = 1;
  int * touched;
  int ntouched, last_trail;
  int cand_idx = i;
  int back_jump = 0;
  
  if (val (solver, abs(cand_pr->idx))) return 0;
  assert (!solver->level);
  
  INC_STATS(variables_expanded);
  MSG (1, "Beggining search for idx %d", cand_pr->idx);
  
  if (prext_check_unit (solver, cand_pr->idx) || prext_check_unit (solver, -cand_pr->idx)) return 0;

  part_pr = new_partial_pr (solver);
  STACK (Partial_PR*) switch_cand;
  INIT (switch_cand);

  prext_assign_lit (solver, cand_pr->idx);
  propagate (solver);
  PUSH (part_pr->decisions, cand_pr->idx);
  for (int p = 0; p < SIZE (solver->trail); p++) {
    PUSH (part_pr->trail, PEEK (solver->trail, p));
  }
  PUSH (cand_pr->partial_prs, part_pr);
  for (int i = 1; i < candidate_queue->cutoff; i++) {
    MSG (1, "adding variales at length %d", i);
    for (int j = 0; j < SIZE (cand_pr->partial_prs); j++) { // expand partial prs
      assert (solver->level == 1);
      part_pr = PEEK (cand_pr->partial_prs, j);
      back_jump = 0;
      for (int d = 1; d < SIZE (part_pr->decisions); d++) { // assign decisions
        back_jump++;
        prext_assign_lit (solver, PEEK (part_pr->decisions, d));
        conflict = propagate (solver);
        if (conflict) { // could learn this clause (RUP)
          goto PARTIAL;
        }
      }
      last_trail = solver->next_to_propagate;
      
      touched = prext_find (solver, part_pr, &ntouched);
      MSG (3, "ntouched %d", ntouched);
      
      if (ntouched) { // touched variables that may be added to pr candidate
        
        for (int t = 0; t < ntouched; t++) {
          if (candidate_queue->seen[abs(touched[t])] == -1) { // add to forntier
            MSG (3, "adding %d to frontier", abs(touched[t]));
            candidate_queue->seen[abs(touched[t])] = 0;
            PUSH (candidate_queue->next_frontier, abs(touched[t]));
            candidate_queue->frontier_count++;
          }
          // stops expansion on already seen variables for candidates
          // will be seen in following iterations
          if (!sadical->opts.pre_add_seen && candidate_queue->seen[abs(touched[t])]) continue;
          // cannot use assigned literal in pr clause
          if (val (solver, abs(touched[t]))) continue;
          
          
          // Assign literal to True
          prext_assign_lit (solver, touched[t]);
          conflict = propagate (solver);
          if (!conflict) { // no conlfict means it can be added to candidate PR
            MSG (1, "Adding lit %d to partial candidate %d",touched[t],j);
            copy_pr = new_copy_pr(solver, part_pr);
            PUSH (copy_pr->decisions, touched[t]);
            for (int p = last_trail; p < SIZE (solver->trail); p++) {
              MSG (3, "copying trail %d",PEEK (solver->trail, p));
              PUSH (copy_pr->trail, PEEK (solver->trail, p));
            }
            PUSH (switch_cand, copy_pr);
          } else { // could learn conflict clause here (RUP)
            MSG (1, "Conflict adding %d to candidate %d",touched[t],j);
          }
          backtrack (solver, solver->level-1);
          
          // Assign literal to False
          prext_assign_lit (solver, -touched[t]);
          conflict = propagate (solver);
          if (!conflict) { // no conlfict means it can be added to candidate PR
            MSG (1, "Adding lit %d to candidate %d",-touched[t],j);
            copy_pr = new_copy_pr(solver, part_pr);
            PUSH (copy_pr->decisions, -touched[t]);
            for (int p = last_trail; p < SIZE (solver->trail); p++) {
              MSG (3, "copying trail %d",PEEK (solver->trail, p));
              PUSH (copy_pr->trail, PEEK (solver->trail, p));
            }
            PUSH (switch_cand, copy_pr);
          } else { // could learn conflict clause here (RUP)
            MSG (1, "Conflict adding %d to candidate %d",-touched[t],cand_idx);
          }
          backtrack (solver, solver->level-1);
        }
        free (touched);
      }
    PARTIAL:
      MSG (2, "Solver Level %d bj %d",solver->level, back_jump);
      if (back_jump) backtrack (solver, solver->level-back_jump); // unassign part pr
      delete_partial_pr(solver, part_pr);
    }
    CLEAR(cand_pr->partial_prs);
    MSG (1, "Number of candidates added %d", SIZE (switch_cand));
    for (int j = 0; j < SIZE (switch_cand); j++) {
      PUSH (cand_pr->partial_prs, PEEK (switch_cand, j));
    }
    CLEAR (switch_cand);
  }
  RELEASE (switch_cand);
  backtrack (solver, solver->level-1); // candidate variable assigned at top
  assert (!solver->level);
  
  Candidate_Queue * tempQ;
  if (!sadical->opts.pre_addinstant) tempQ = new_candidate_queue (solver, solver->max_var+1, candidate_queue->cutoff);
  // check reducts for candidates
  for (int j = 0; j < SIZE (cand_pr->partial_prs); j++) {
    part_pr = PEEK (cand_pr->partial_prs, j);
    back_jump = 0;
    for (int d = 0; d < SIZE (part_pr->decisions); d++) {
      if (val (solver, abs (PEEK (part_pr->decisions, d))))
        goto FAILED;
      back_jump++;
      prext_assign_lit (solver, PEEK (part_pr->decisions, d));
      conflict = propagate (solver);
      MSG (3, "Assigning %d to generate reduct", PEEK (part_pr->decisions, d));
      if (conflict) {
        if (!d) {
          if (back_jump) backtrack (solver, solver->level-back_jump);
          goto UNIT;
        }
        MSG (1, "Conflict adding %d to candidate %d",PEEK (part_pr->decisions, d),cand_idx);
        goto FAILED;
      }
    }
    MSG (1, "Generating Reduct");
    generate_reduct (solver);
    if (reduct_satisfiable (solver)) { // set this as the candidate pr clause
      LOG ("pruning successful");
      MSG (1, "pruning successful");
      Candidate_PR * temp = new_candidate_pr (solver, cand_pr->idx);
      prext_store_pruned_clause_witness (solver, temp);
      assert (temp->pr_size == candidate_queue->cutoff);

      if (sadical->opts.pre_addinstant) { // add to formula, free candidate pr
        if (back_jump) {
          backtrack (solver, solver->level-back_jump);
          back_jump = 0;
        }
        prext_write_clause (solver, temp, 1, 0);
      }
      else { // store for batch learning
        temp->pr_found = 1;
        PUSH (tempQ->candidate_prs, temp);
      }
      
      // print
      int * first_cls = temp->pr_clause;
      int first_size = temp->pr_size;
      MSG (1, "Found Candidate PR Clause: ");
      for (int j = 0; j < first_size; j++)
        MSG (1, "%d ", first_cls[j]);
      first_cls = temp->witness;
      first_size = temp->wit_size;
      for (int j = 0; j < first_size; j++)
        MSG (1, "%d ", first_cls[j]);
      MSG (1, "\n");
      if (sadical->opts.pre_addinstant) delete_candidate_pr (solver,temp);
    } else MSG (1, "Reduct unsatisfiable");
    
    clear_inner_solver (sadical->inner);
  FAILED:
    MSG (1, "back");
    if (back_jump) backtrack (solver, solver->level-back_jump);
    MSG (2, "Solver Level %d bj %d",solver->level, back_jump);
  }
  assert (!solver->level);

UNIT:
  // UNIT CHECK AGAIN
  if (prext_check_unit (solver, -cand_pr->idx) || prext_check_unit (solver, cand_pr->idx)) {
    MSG (1, "Unit after adding prs");
    if (!sadical->opts.pre_addinstant) delete_candidate_queue (solver, tempQ);
  }
  return tempQ;
}



//------------------------------------------------------------------------------

// Pr Extraction "learning PR clauses"
// Given a set of found PR clauses, determines conflicts and learns a
// non-conflicting subset of clauses.

void prext_learn_prs(Solver * solver, Candidate_Queue * candidate_queue) {
  SaDiCaL * sadical = solver->sadical;
  assert (!solver->level);
  double start = sadical_process_time ();
  MSG (3, "selecting clauses to add from %d found",SIZE (candidate_queue->candidate_prs));
  Candidate_PR *first, *second;
  int satisfied, touched, first_size, cand_cnt;
  int * first_cls;
  cand_cnt = SIZE (candidate_queue->candidate_prs);
  bool conflicts[cand_cnt][cand_cnt]; // likely extremely sparse...
  int conflict_cnts[cand_cnt], added[cand_cnt], blocked[cand_cnt], blocking[cand_cnt],overlapped[cand_cnt];
  for (int i = 0; i < cand_cnt; i++) {
    conflict_cnts[i] = added[i] = blocked[i] = blocking[i] = overlapped[i] = 0;
    for (int j = 0; j < cand_cnt; j++) {
      conflicts[i][j] = 0;
    }
  }
  
  // find conflicts between candidate pr clauses
  for (int f = 0; f < SIZE (candidate_queue->candidate_prs); f++) {
    first = PEEK (candidate_queue->candidate_prs, f);
    if (!first->pr_found) {blocked[f]=1; continue;}
    first_cls = first->pr_clause;
    first_size = first->pr_size;
    for (int k = 0; k < first_size; k++) { // no variables have been set by unit
      if (val (solver, first_cls[k])) {
        blocked[f] = 1;
        break;
      }
    }
    if (blocked[f]) continue;
    for (int k = 0; k < first->wit_size; k++) { // no variables have been set by unit
      if (val (solver, first->witness[k]) == -1) {
        blocked[f] = 1;
        break;
      }
    }
    if (blocked[f]) continue;
    for (int s = 0; s < SIZE (candidate_queue->candidate_prs); s++) {
      if (f == s) continue;
      if (blocked[s]) continue;
      second = PEEK (candidate_queue->candidate_prs, s);
      if (!second->pr_found) continue;
      satisfied = 0;
      touched = 0;
      int count_s = 0;
      // check if same clause (simple because clauses are length < 4)
      for (int i = 0; i < second->pr_size; i++) {
        for (int j = 0; j < first_size; j++) {
          if (first_cls[j] == second->pr_clause[i]) {
            count_s++;
            break;
          }
        }
      }
      if (count_s == second->pr_size) { // same pr clause
        conflict_cnts[f]++;
        conflicts[f][s] = 1;
        continue;
      }
      // chech if the first clause would appear in second's reduct
      for (int i = 0; i < second->trail_size; i++) {
        for (int j = 0; j < first_size; j++) {
          if (first_cls[j] == second->trail[i]) {
            touched = 1;
            break;
          }
        } if (touched) break;
      }
      if (touched) { // check if first clause satisfied by second's witness
        for (int i = 0; i < second->wit_size; i++) {
          for (int j = 0; j < first_size; j++) {
            if (first_cls[j] == second->witness[i]) {
              satisfied = 1;
              break;
            }
          } if (satisfied) break;
        }
        if (!satisfied) { // conflict, first clause prevents second
          // TODO: make conflict case stronger (could find new satisfying assignment for second)
          conflict_cnts[f]++;
          conflicts[f][s] = 1;
          blocking[f]++;
        }
      }
    }
  }

  if (sadical->opts.pre_batch_sort) { // sort then learn non-conflicting clauses
    int minB, minO, nextpr;
    for (int i = 0; i < cand_cnt; i++) INC_STATS(candidates_processed);
    do { // sorting based on number of pr clauses one clause will block
         // experimental, need better data structure for larger set of clauses
      nextpr = -1;
      for (int i = 0; i < cand_cnt; i++) { // select next pr clause
        
        if (added[i] || blocked[i]) continue;
        if (nextpr > -1) {
          if (blocking[i] < minB || (blocking[i] == minB && overlapped[i] < minO)) {
            nextpr = i;
            minB = blocking[i];
            minO = overlapped[i];
          }
        } else {
          nextpr = i;
          minB = blocking[i];
          minO = overlapped[i];
        }
      }
      if (nextpr>-1) { // add pr clause
        added[nextpr] = 1;
        first = PEEK (candidate_queue->candidate_prs, nextpr);
        prext_write_clause (solver, first, 1, 0);
        for (int j = 0; j < cand_cnt; j++) { // O(N^2) update, could be faster
          if (conflicts[nextpr][j]) {
            if (!blocked[j] && !added[j]) { // skip already blocked
              INC_STATS(candidates_blocked);
              blocked[j] = 1;
              for (int z = 0; z < cand_cnt; z++) {
                if (conflicts[z][j]) {
                  blocking[z]--;
                  overlapped[z]++;
                }
              }
            }
          }
        }
      }
    } while (nextpr > -1);
  } else { // learn non-conflicting PR clauses in order they are given
    int add_order[cand_cnt];
    for (int i = 0; i < cand_cnt; i++) add_order[i] = i;
    int j, temp;
    if (sadical->opts.pre_batch_random) {
    for (int i = 0; i < cand_cnt; i++) {
      j = rand() % (i+1);
      temp = add_order[j];
      add_order[j] = add_order[i];
      add_order[i] = temp; // bug fix
    }}
    
    for (int p = 0; p < cand_cnt; p++) {
      int i = add_order[p];
      INC_STATS(candidates_processed);
      if (blocked[i]) {
        INC_STATS(candidates_blocked);
        continue;
      }
      first = PEEK (candidate_queue->candidate_prs, i);
      prext_write_clause (solver, first, 1, 0);
      added[i] = 1;
      for (int j = 0; j < cand_cnt; j++) {
        if (conflicts[i][j]) blocked[j] = 1;
      }
    }
  }
  sadical->time.adding += sadical_process_time () - start;
}



//------------------------------------------------------------------------------

// Pr Extraction Control Flow

// Return the first unassigned variable
int pr_get_starting_var (Solver * solver) {
  for (int i = 1; i < solver->max_var+1; i++) {
    if (!val (solver, i) && (PEEK (solver->vars_in_formula , i))) return i;
  }
  return 0;
}
// Return the first unassigned variable that has not been seen
int pr_get_next (Solver * solver, Candidate_Queue * candidate_queue) {
  for (int i = 1; i < solver->max_var+1; i++) {
    if (candidate_queue->seen[i] < 1 && !val (solver, i)  && (PEEK (solver->vars_in_formula , i))) return i;
  }
  return 0;
}
// initialize candidate_queue frontier candidate_prs with starting_var
void prext_start (Solver * solver, Candidate_Queue * candidate_queue, int starting_var) {
  SaDiCaL * sadical = solver->sadical;
  PUSH (candidate_queue->next_frontier, starting_var);
  candidate_queue->frontier_count = 1;
}


// add to touched lists clauses start:last_clause
// could order touched lists for faster insertion. Or make Btree...
void add_clauses_to_touched_lists (Solver * solver, int start) {
  SaDiCaL * sadical = solver->sadical;
  Clause * cls;
  int allin;
  int last_clause = SIZE (solver->clauses);

  for (int c = start; c < last_clause; c++) {
    cls = PEEK (solver->clauses, c); // add lits <- cls to each variables touched list
    for (int v = 0; v < cls->size; v++) {
      for (int t = 0; t < cls->size; t++) {
        if (v == t) continue;
        allin = 0;
        for (int s = 0; s < SIZE (solver->touched_list[abs(cls->literals[v])]); s++) {
          if (cls->literals[t] == PEEK (solver->touched_list[abs(cls->literals[v])], s)) {
            allin = 1;
            break;
          }
        }
        if (!allin) PUSH (solver->touched_list[abs(cls->literals[v])], cls->literals[t]);
      }
    }
  }
  MSG (1, "Computed touched lists");
}


// initialize output files, data structures, and propagate top level units
void pr_init (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;

  MSG (1, "Initializing PR EXTRACT");

  solver->pr_clause_out = fopen("pr_clauses.cnf", "w");
  solver->pr_clause_full_out = fopen("pr_clauses_full.dpr", "w");
  solver->pr_units = fopen("pr_units.cnf", "w");
  solver->pr_units_full = fopen("pr_units.dpr", "w");
  solver->top_level_conflict = false;
  solver->find_time = 1;
  solver->find_vars = malloc (sizeof (long) * (solver->max_var+1));
  neighbors_cnt = malloc (sizeof (long) * (solver->max_var+1));
  for (int i = 0; i < solver->max_var+1; i++) {solver->find_vars[i] = neighbors_cnt[i] = 0;}
  INIT (solver->units);
  
  // touched lists (can be more efficient)
  if (!sadical->opts.pre_reduced) {
    solver->touched_list = malloc (sizeof (Ints) * (solver->max_var+1));
    for (int i = 0; i < solver->max_var+1; i++) INIT (solver->touched_list[i]);
    add_clauses_to_touched_lists (solver, 0);
  }

  propagate (solver); // propagate and simplify all units (necessary for pruning)
  if (simplifying (solver)) simplify (solver);
  
}

// Initializes data structures including touched lists
// Iterates over variables in formula, calling find and learn functions
void pr_extract (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  
  int starting_var;
  int cutoff = sadical->opts.pre_length_init;
  Candidate_Queue * candidate_queue, *found_queue, * cumulative_found_queue;

  pr_init (solver);
  
  for (int sweeps = 0; sweeps < sadical->opts.pre_iterations; sweeps++) {
    cutoff = sadical->opts.pre_length_init;         // initial cutoff
    while (cutoff < sadical->opts.pre_length_end) { // iterate through PR sizes
      MSG (1, "Beggining outer loop for cutoff %d", cutoff);
      candidate_queue = new_candidate_queue (solver, solver->max_var+1, cutoff);
      cumulative_found_queue = new_candidate_queue (solver, solver->max_var+1, cutoff);
      starting_var = pr_get_starting_var (solver);
      prext_start (solver, candidate_queue, starting_var);
      while (candidate_queue->frontier_count) {// BFS over all variables in formula
        for (int i = 0; i < SIZE (candidate_queue->next_frontier); i++) {
          int var = PEEK (candidate_queue->next_frontier, i);
          Candidate_PR * cand_pr = new_candidate_pr (solver, var);
          PUSH (candidate_queue->candidate_prs, cand_pr);
          candidate_queue->count++;
          if (sadical->opts.pre_both_phases) {
            Candidate_PR * cand_pr1 = new_candidate_pr (solver, -var);
            PUSH (candidate_queue->candidate_prs, cand_pr1);
            candidate_queue->count++;
          }
        }
        candidate_queue->frontier_count = 0;
        CLEAR (candidate_queue->next_frontier);
        // find candidate pr clauses one variable at a time
        for (int i = 0; i < SIZE (candidate_queue->candidate_prs); i++) {
          found_queue = prext_find_candidates(solver, candidate_queue, i);
          if (solver->top_level_conflict) { // a learned unit causes a conflict
            printf( "TOP LEVEL CONFLICT\n");
            return;
          }
          if (!sadical->opts.pre_addinstant && found_queue) { // learn clauses
            // add to cumulative found clauses
            for (int i = 0; i < SIZE (found_queue->candidate_prs); i++) {
              PUSH (cumulative_found_queue->candidate_prs, PEEK (found_queue->candidate_prs, i));
            }
            CLEAR (found_queue->candidate_prs);
            delete_candidate_queue (solver, found_queue);
            
            if (sadical->opts.pre_batch_size <= SIZE (cumulative_found_queue->candidate_prs)) {
              // learn and reset cumulative found clauses
              prext_learn_prs (solver, cumulative_found_queue);
              for (int i = 0; i < SIZE (cumulative_found_queue->candidate_prs); i++) { //free
                delete_candidate_pr (solver, PEEK (cumulative_found_queue->candidate_prs, i));
              }
              cumulative_found_queue->count = 0;
              CLEAR (cumulative_found_queue->candidate_prs);
            }
          }
        }
        for (int i = 0; i < SIZE (candidate_queue->candidate_prs); i++) { //free
          delete_candidate_pr (solver, PEEK (candidate_queue->candidate_prs, i));
        }
        candidate_queue->count = 0;
        CLEAR (candidate_queue->candidate_prs);
        if (!candidate_queue->frontier_count) {
          int rem = pr_get_next (solver, candidate_queue);
          if (rem) { // some variable wasn't touched by the BFS
            prext_start (solver, candidate_queue, rem);
          }
        }
      }
      
      if (SIZE (cumulative_found_queue->candidate_prs)) { // learn from remaining found clauses
        prext_learn_prs (solver, cumulative_found_queue);
        for (int i = 0; i < SIZE (cumulative_found_queue->candidate_prs); i++) { //free
          delete_candidate_pr (solver, PEEK (cumulative_found_queue->candidate_prs, i));
        }
        cumulative_found_queue->count = 0;
        CLEAR (cumulative_found_queue->candidate_prs);
      }
      
      delete_candidate_queue (solver, candidate_queue);
      delete_candidate_queue (solver, cumulative_found_queue);
      cutoff++;
    }
    printf("c Iteration %d\n", sweeps);
    
    if (!solver->new_pr) break; // saturation: no new PR clauses learned in this iteration
    
    
    // new modification
//    if (!sadical->opts.pre_reduced) { // update touched list after learning new PR clauses
//      add_clauses_to_touched_lists (solver, SIZE (solver->clauses) - solver->new_pr);
//    }

    solver->new_pr = 0;
    sadical_pr_stats (sadical) ;

  }
  
  // add all propagated units not yet added
  for (int i = 0; i < SIZE (solver->trail); i++) {
    bool allin = false;
    for (int l = 0; l < SIZE (solver->units); l++) {
      if (PEEK (solver->units,l) == PEEK (solver->trail, i)) {
        allin=true;
        break;
      }
    }
    if (!allin) {
      int lit = PEEK (solver->trail, i);
      fprintf(solver->pr_clause_out, "%d 0\n", lit);
      fprintf(solver->pr_clause_full_out, "%d 0\n", lit);
      fprintf(solver->pr_units, "%d 0\n", lit);
      fprintf(solver->pr_units_full, "%d 0\n", lit);
    }
  }
}

void sadical_pr_extract (SaDiCaL * sadical) {
  srand(sadical->opts.pre_seed); // random seed
  pr_extract (sadical->outer);
}

/*------------------------------------------------------------------------*/

static int solve (Solver * solver) {
  LOG ("solving");
  int res = solver->inconsistent ? 20 : 0;
  if (!res) {
    init_limits (solver);
    while (!res) {
      Clause * conflict = propagate (solver);
      if (conflict) res = analyze (solver, conflict);
      else if (all_assigned (solver)) res = 10;
      else if (reducing (solver)) reduce (solver);
      else if (restarting (solver)) restart (solver);
      else if (simplifying (solver)) simplify (solver);
      else if (!prune (solver)) decide (solver);
    }
  }
  if (res == 10) LOG ("satisfiable");
  if (res == 20) LOG ("unsatisfied");
  return res;
}

int sadical_solve (SaDiCaL * sadical) {
  int res = solve (sadical->outer);
  if (res == 10) sadical_report (sadical, '1');
  else if (res == 20) sadical_report (sadical, '0');
  else sadical_report (sadical, '?');
  return res;
}

/*------------------------------------------------------------------------*/

static bool tautological (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  int size = SIZE (solver->original);
  assert (!solver->level);
  assert (EMPTY (solver->clause));
  bool res = false;
  solver->stamp++;
  for (int i = 0; !res && i < size; i++) {
    int lit = PEEK (solver->original, i);
    int tmp = marked (solver, lit);
    if (tmp > 0) LOG ("removing duplicated literal %d", lit);
    else if (tmp < 0) {
      LOG ("original clause contains both %d and %d", -lit, lit);
      res = true;
    } else if ((tmp = val (solver, lit)) < 0) {
      LOG ("removing falsified literal %d", lit);
    } else if (tmp > 0) {
      LOG ("original clause satisfied by literal %d", lit);
      res = true;
    } else {
      PUSH (solver->clause, lit);
      mark (solver, lit);
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

// We keep variables, values, watches and scores in different stacks.
// While variables are indexed from 1..max_var, the other three arrays are
// indexed from -max_var...max_var (skipping '0') for faster access.  As
// usual with stacks we pre-allocate more memory geometrically increasing,
// controlled by the global solver size.  We need dynamic increasing
// memory here.

static void enlarge_variables (Solver * solver, long new_size) {
  long old_size = solver->size;
  SaDiCaL * sadical = solver->sadical;
  Var * old_vars = solver->vars;
  size_t old_bytes = old_size * sizeof (Var);
  size_t new_bytes = new_size * sizeof (Var);
  SUB_ALLOCATED (old_bytes);
  solver->vars = realloc (old_vars, new_bytes);
  if (!solver->vars) DIE ("out-of-memory enlarging variables");
  ADD_ALLOCATED (new_bytes);
}

static void enlarge_values (Solver * solver, long new_size) {
  long old_size = solver->size;
  SaDiCaL * sadical = solver->sadical;
  size_t old_bytes = 2 * old_size * sizeof (Val);
  size_t new_bytes = 2 * new_size * sizeof (Val);
  Val * vals = malloc (new_bytes);
  if (!vals) DIE ("out-of-memory enlarging values");
  ADD_ALLOCATED (new_bytes);
  vals += new_size;
  for (int lit = -solver->max_var; lit <= solver->max_var; lit++)
    if (lit) vals[lit] = solver->vals[lit];
  solver->vals -= old_size;
  free (solver->vals);
  solver->vals = vals;
  SUB_ALLOCATED (old_bytes);
}

static void enlarge_watches (Solver * solver, long new_size) {
  long old_size = solver->size;
  SaDiCaL * sadical = solver->sadical;
  size_t old_bytes = 2 * old_size * sizeof (Watches);
  size_t new_bytes = 2 * new_size * sizeof (Watches);
  Watches * watches = malloc (new_bytes);
  if (!watches) DIE ("out-of-memory enlarging watches");
  ADD_ALLOCATED (new_bytes);
  watches += new_size;
  for (int lit = -solver->max_var; lit <= solver->max_var; lit++)
    if (lit) watches[lit] = solver->watches[lit];
  solver->watches -= old_size;
  free (solver->watches);
  solver->watches = watches;
  SUB_ALLOCATED (old_bytes);
}

static void enlarge_scores (Solver * solver, long new_size) {
  long old_size = solver->size;
  SaDiCaL * sadical = solver->sadical;
  size_t old_bytes = 2 * old_size * sizeof (Score);
  size_t new_bytes = 2 * new_size * sizeof (Score);
  SUB_ALLOCATED (old_bytes);
  solver->scores = realloc (solver->scores - old_size, new_bytes);
  if (!solver->scores) DIE ("out-of-memory enlarging scores");
  ADD_ALLOCATED (new_bytes);
  solver->scores += new_size;
}

static void enlarge_size (Solver * solver, int new_max_var) {
  long old_size = solver->size;
  long new_size = old_size ? 2*old_size : 2;
  while (new_size <= (size_t) new_max_var)
    new_size *= 2;
  LOG ("enlarging size from %zd to %zd for new maximum variable %d",
    old_size, new_size, new_max_var);
  enlarge_variables (solver, new_size);
  enlarge_values (solver, new_size);
  enlarge_watches (solver, new_size);
  enlarge_scores (solver, new_size);
  solver->size = new_size;
}

// After allocating enough space for variables etc. we still need to
// enqueue a new variable to the decision queue.  This is constant time
// though and can be called every time a new variable is seen for the
// first time without introducing an accumulated quadratic complexity.

static void new_variable (Solver * solver) {
  int idx = ++solver->max_var;
  assert (solver->size > (size_t) solver->max_var);
  SaDiCaL * sadical = solver->sadical;
  LOG ("new variable %d", idx);
  Var * v = var (solver, idx);
  memset (v, 0, sizeof *v);
  if (sadical->opts.reverse) enqueue_first (solver, idx);
  else enqueue_last (solver, idx);
  solver->vals[idx] = 0;
  solver->vals[-idx] = 0;
  INIT (solver->watches[idx]);
  INIT (solver->watches[-idx]);
}

// Make sure that every literal added has a corresponding variable.

static void import_literal (Solver * solver, int lit) {
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx <= solver->max_var) return;
  if (solver->size <= (size_t) idx) enlarge_size (solver, idx);
  do new_variable (solver); while (idx > solver->max_var);
}

static void add_literal (Solver * solver, int lit) {
  assert (!solver->level);
  SaDiCaL * sadical = solver->sadical;
  import_literal (solver, lit);
  
  if (lit) {
    int varIDX = abs (lit);
    if (SIZE (solver->vars_in_formula) <= varIDX) {
      for (int i = SIZE (solver->vars_in_formula); i <= varIDX; i++) PUSH (solver->vars_in_formula, 0);
    }
    POKE (solver->vars_in_formula, varIDX, 1);
  }
  
  if (lit) PUSH (solver->original, lit);
  else {
    int original_size = SIZE (solver->original);
    LOGLITS (solver->original.begin, original_size, "original");
    if (solver->inconsistent) LOG ("skipping clause since CNF inconsistent");
    else if (!original_size) {
      LOG ("found empty original clause");
      solver->inconsistent = true;
    } else if (tautological (solver)) {
      LOG ("skipping tautological clause");
      trace_original_clause_deletion (solver);
    } else {
      int size = SIZE (solver->clause);
      if (!size) learn_empty_clause (solver);
      else {
	if (sadical->proof &&
	    sadical->outer == solver &&
	    original_size != size) {
	  assert (size < original_size);
	  trace_simplified_clause_addition (solver);
	  trace_original_clause_deletion (solver);
	}
	if (size == 1) {
	  int unit = POP (solver->clause);
	  LOG ("simplified unit clause %d", unit);
	  assign (solver, unit, 0);
	  if (propagate (solver)) {
	    LOG ("CNF becomes inconsistent after propagating unit");
	    learn_empty_clause (solver);
	  }
	} else {
	  assert (size > 1);
	  Clause * c = new_clause (solver, false, 0);
	  LOGCLS (c, "simplified");
	  watch_clause (solver, c);
	}
      }
    }
    CLEAR (solver->original);
    CLEAR (solver->clause);
  }
}

/*------------------------------------------------------------------------*/

// This is the IPASIR function to add clauses.

void sadical_add_literal (SaDiCaL * sadical, int lit) {
  REQUIRE (lit != INT_MIN);
  REQUIRE (!sadical->outer->level);		// Not incremental yet.
  add_literal (sadical->outer, lit);
}

/*------------------------------------------------------------------------*/

int sadical_max_var (SaDiCaL * sadical) {
  return sadical->outer->max_var;
}

/*------------------------------------------------------------------------*/

int sadical_val (SaDiCaL * sadical, int lit) {
  REQUIRE (lit != 0);
  REQUIRE (lit != INT_MIN);
  Solver * solver = sadical->outer;
  int idx = abs (lit);
  if (idx > solver->max_var) return 0;
  return val (solver, lit);
}

/*------------------------------------------------------------------------*/

static void delete_variables (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  size_t bytes = solver->size * sizeof (Var);
  free (solver->vars);
  SUB_ALLOCATED (bytes);
}

static void delete_values (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  size_t bytes = 2l * solver->size * sizeof (Val);
  free (solver->vals - solver->size);
  SUB_ALLOCATED (bytes);
}

static void delete_watches (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  for (int lit = -solver->max_var; lit <= solver->max_var; lit++)
    if (lit) RELEASE (*watches (solver, lit));
  size_t bytes = 2l * solver->size * sizeof (Watches);
  free (solver->watches - solver->size);
  SUB_ALLOCATED (bytes);
}

static void delete_scores (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  size_t bytes = 2l * solver->size * sizeof (Score);
  free (solver->scores - solver->size);
  SUB_ALLOCATED (bytes);
}

static void release_reporting (SaDiCaL * sadical) {
  for (int i = 0; i < NUM_HEADERS; i++)
    GRELEASE (sadical->reporting.header[i]);
  GRELEASE (sadical->reporting.columns);
}

static void delete_solver (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  delete_clauses (solver);
  RELEASE (solver->clauses);
  delete_variables (solver);
  delete_values (solver);
  delete_watches (solver);
  delete_scores (solver);
  RELEASE (solver->clause);
  RELEASE (solver->original);
  RELEASE (solver->trail);
  RELEASE (solver->frames);
  RELEASE (solver->analyzed);
  SUB_ALLOCATED (sizeof *solver);
//  assert (getenv ("SADICALEAK") || !solver->local.heap.current);
  free (solver);
}

static void clear_inner_solver (Solver * solver) {
  LOG ("clear");
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->inner == solver);
  delete_solver (sadical->inner);
  sadical->inner = new_solver (sadical);
}

void sadical_delete (SaDiCaL * sadical) {
  delete_solver (sadical->outer);
  delete_solver (sadical->inner);
  release_reporting (sadical);
  SUB_GLOBAL_ALLOCATED (sizeof *sadical);
//  assert (getenv ("SADICALEAK") || !sadical->total.heap.current);
  if (sadical->proof && sadical->close_proof)
    fclose (sadical->proof);
  free (sadical);
}
