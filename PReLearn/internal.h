#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

/*------------------------------------------------------------------------*/

// Long Options with Values.

#define OPTIONS \
OPTION(alphafast,double,1e-03,0,1,"alpha for fast moving average") \
OPTION(alphaslow,double,1e-05,0,1,"alpha for slow moving average") \
OPTION(autarky,bool,true,0,1,"non-root autarky decision heuristic") \
OPTION(binary,bool,true,0,1,"use binary proof format") \
OPTION(bump,bool,true,0,1,"bump analyzed variables") \
OPTION(filter,bool,false,0,1,"filtered positive reduct") \
OPTION(force,bool,false,0,1,"force overwriting proof file") \
OPTION(keepglue,int,3,0,INT_MAX,"keep redundant clauses of this size") \
OPTION(keepsize,int,3,0,INT_MAX,"keep redundant clauses with this glue") \
OPTION(level,int,2000,1,INT_MAX,"maximum pruning decision level") \
LOGOPT(logging,bool,false,0,1,"logging enabled") \
OPTION(nonroot,int,3,0,4,"0=VMTF,1=LIS,2=JWH,3=PHP,4=Tseitin") \
OPTION(prune,bool,true,0,1,"pruning enabled (SDCL)") \
OPTION(pre_addinstant,bool,true,0,1,"learn PR clause immediately as reducts satisfied") \
OPTION(pre_add_seen,bool,false,0,1,"include already seen variables in candidate PR consrtuction") \
OPTION(pre_batch_sort,bool,false,0,1,"sort PR candidates by conflicts for batch learning") \
OPTION(pre_batch_random,bool,0,0,1,"add PR candidates in random order for batch learning") \
OPTION(pre_batch_size,int,1,1,INT_MAX,"Number of found PR clauses before batch learning begins") \
OPTION(pre_both_phases,bool,true,0,1,"use both phases for initial variable of pr candidate construction") \
OPTION(pre_length_end,int,3,0,INT_MAX,"find PR clauses up to this length") \
OPTION(pre_length_init,int,2,0,INT_MAX,"start finding PR clauses at this length") \
OPTION(pre_iterations,int,1,1,INT_MAX,"number of iterations extracting pr clauses") \
OPTION(pre_neighbors_depth,int,0,0,INT_MAX,"number of iterations for expanding neighbor vars") \
OPTION(pre_reduced,bool,false,0,1,"expansion on reduced but not satisfied clauses") \
OPTION(pre_seed,int,1,1,INT_MAX,"random number generator seed") \
OPTION(pre_unit,bool,true,0,1,"solve pruning predicate for units") \
OPTION(root,int,3,0,4,"0=VMTF,1=LIS,2=JWH,3=PHP,4=Tseitin") \
OPTION(reduce,bool,true,0,1,"enable forgetting learned clauses") \
OPTION(reduceinc,int,300,1,INT_MAX,"reduce interval increment") \
OPTION(reduceinit,int,2000,0,INT_MAX,"initial reduce interval") \
OPTION(restart,bool,true,0,1,"enable restarts") \
OPTION(restartint,int,10,1,INT_MAX,"restart interval") \
OPTION(restartmargin,double,1.1,1,INT_MAX,"restart slow / fast margin") \
OPTION(reverse,bool,false,0,1,"reverse initial variable order") \
OPTION(reuse,bool,false,0,1,"reuse trails during restart") \
OPTION(verbose,int,0,0,5,"verbose level") \
OPTION(witness,bool,true,0,1,"print satisfying assignment") \

/*------------------------------------------------------------------------*/

// Filter out logging options without logging code included.

#ifndef NLOG
#define LOGOPT OPTION
#else
#define LOGOPT(...) /**/
#endif

/*------------------------------------------------------------------------*/

// For testing coverage.

#define COVER(COND) \
do { \
  if (!(COND)) break; \
  fflush (stdout); \
  fprintf (stderr, \
    "dualiza: %s:%d: %s: Coverage target `%s' reached.\n", \
    __func__, __LINE__, __FILE__, # COND); \
  fflush (stderr);  \
  abort (); \
} while (0)

/*------------------------------------------------------------------------*/

// Condition for hit assumed unreachable code.

#define UNREACHABLE(COND) \
do { \
  if (!(COND)) break; \
  fflush (stdout); \
  fprintf (stderr, \
    "dualiza: %s:%d: %s: Unreachable condition `%s' actually reached.\n", \
    __func__, __LINE__, __FILE__, # COND); \
  fflush (stderr);  \
  abort (); \
} while (0)

/*------------------------------------------------------------------------*/

// API conformance checking.

#define REQUIRE(COND) \
do { \
  if ((COND)) break; \
  fflush (stdout); \
  fprintf (stderr, \
    "dualiza: %s:%d: %s: API requirement `%s' failed.\n", \
    __func__, __LINE__, __FILE__, # COND); \
  fflush (stderr);  \
  abort (); \
} while (0)

/*------------------------------------------------------------------------*/

#define SWAP(T,A,B) \
do { \
  T TMP = (A); \
  (A) = (B); \
  (B) = TMP; \
} while (0)

/*------------------------------------------------------------------------*/

// Keep accurate count of allocated heap memory.

#define ADD_LOCAL_ALLOCATED(BYTES) \
do { \
  if (!solver) break; \
  solver->local.heap.current += (BYTES); \
  solver->local.heap.allocated += (BYTES); \
  if (solver->local.heap.max < solver->local.heap.current) \
    solver->local.heap.max = solver->local.heap.current; \
} while (0)

#define ADD_GLOBAL_ALLOCATED(BYTES) \
do { \
  sadical->total.heap.current += (BYTES); \
  sadical->total.heap.allocated += (BYTES); \
  if (sadical->total.heap.max < sadical->total.heap.current) \
    sadical->total.heap.max = sadical->total.heap.current; \
} while (0)

#define ADD_ALLOCATED(BYTES) \
do { \
  ADD_LOCAL_ALLOCATED (BYTES); \
  ADD_GLOBAL_ALLOCATED (BYTES); \
} while (0)

#define SUB_LOCAL_ALLOCATED(BYTES) \
do { \
  if (!solver) break; \
  assert (solver->local.heap.current >= (BYTES)); \
  solver->local.heap.current -= (BYTES); \
} while (0)

#define SUB_GLOBAL_ALLOCATED(BYTES) \
do { \
  assert (sadical->total.heap.current >= (BYTES)); \
  sadical->total.heap.current -= (BYTES); \
} while (0)

#define SUB_ALLOCATED(BYTES) \
do { \
  SUB_LOCAL_ALLOCATED ((BYTES)); \
  SUB_GLOBAL_ALLOCATED (BYTES); \
} while (0)

/*------------------------------------------------------------------------*/

// New and delete for pointers.

#define NEW(PTR) \
do { \
  size_t BYTES = sizeof *(PTR); \
  (PTR) = malloc (BYTES); \
  if (!(PTR)) DIE ("out-of-memory in '%s'", __func__); \
  memset ((PTR), 0, BYTES); \
  INC (BYTES); \
} while (0)

#define DELETE(PTR) \
do { \
  size_t BYTES = sizeof *(PTR); \
  SUB_ALLOCATED (BYTES); \
  free ((PTR)); \
} while (0)

/*------------------------------------------------------------------------*/

// Generic stack implementations similar to the C++ vector template class.

#define STACK(TYPE) struct { TYPE * begin; TYPE * end; TYPE * allocated; }

#define INIT(S) do { (S).begin = (S).end = (S).allocated = 0; } while (0)

#define SIZE(S) ((S).end - (S).begin)
#define ALLOCATED(S) ((S).allocated - (S).begin)

#define EMPTY(S) ((S).end == (S).begin)
#define FULL(S) ((S).end == (S).allocated)

#define CLEAR(S) do { (S).end = (S).begin; } while (0)

#define RELEASE(S) \
do { \
  size_t BYTES = ALLOCATED(S) * sizeof *(S).begin; \
  SUB_ALLOCATED (BYTES); \
  free ((S).begin); \
  INIT (S); \
} while (0)

#define GRELEASE(S) \
do { \
  Solver * solver = 0; /* mark as only globally allocated */ \
  RELEASE (S); \
} while (0)

#define POP(S) \
  (assert (!EMPTY (S)), *--(S).end)

#define ENLARGE(S) \
do { \
  size_t OLD_SIZE = SIZE (S); \
  size_t OLD_ALLOCATED = ALLOCATED (S); \
  size_t NEW_ALLOCATED = OLD_ALLOCATED ? 2*OLD_ALLOCATED : 1; \
  size_t OLD_BYTES = OLD_ALLOCATED * sizeof *(S).begin; \
  size_t NEW_BYTES = NEW_ALLOCATED * sizeof *(S).begin; \
  SUB_ALLOCATED (OLD_BYTES); \
  (S).begin = realloc ((S).begin, NEW_BYTES); \
  if (!(S).begin) \
    DIE ("out-of-memory enlarging stack in '%s'", __func__); \
  ADD_ALLOCATED (NEW_BYTES); \
  (S).end = (S).begin + OLD_SIZE; \
  (S).allocated = (S).begin + NEW_ALLOCATED; \
} while (0)

#define PUSH(S,E) \
do { \
  if (FULL (S)) ENLARGE (S); \
  *(S).end++ = (E); \
} while (0)

#define GPUSH(S,E) \
do { \
  Solver * solver = 0; /* mark as only globally allocated */ \
  PUSH (S,E); \
} while (0)

#define TOP(S) \
  (assert (!EMPTY (S)), (S).end[-1])

#define BEGIN(S) ((S).begin)
#define END(S) ((S).end)

#define PEEK(S,I) \
  (assert (0 <= (I)), assert ((I) < SIZE (S)), (S).begin[I])

#define POKE(S,I,E) \
do { \
  assert (0 <= (I)); \
  assert ((I) < SIZE (S)); \
  (S).begin[I] = (E); \
} while (0)

#define RESIZE(S,N) \
do { \
  assert ((N) <= SIZE (S)); \
  (S).end = (S).begin + (N); \
} while (0)

/*------------------------------------------------------------------------*/

#define DIE(...) sadical_die (__VA_ARGS__)
#define MSG(...) sadical_msg (sadical, __VA_ARGS__)

/*------------------------------------------------------------------------*/

typedef struct Average Average;
typedef struct Clause Clause;
typedef struct Frame Frame;
typedef struct SaDiCaL SaDiCaL;
typedef struct Solver Solver;
typedef struct Stats Stats;
typedef struct Score Score;
typedef signed char Val;
typedef struct Var Var;
typedef struct Watch Watch;

typedef STACK (char) Buffer;
typedef STACK (Clause *) Clauses;
typedef STACK (int) Ints;
typedef STACK (Watch) Watches;

/*------------------------------------------------------------------------*/

struct Var
{
  Val val;			// Copy of 'vals[idx]' (-1,0,1).
  Val phase;			// Previous assigned value.
  int mapped;			// Mapped to this inner/outer index.
  int level;			// Frame level.
  long stamp;			// Time stamp for marking.
  long enqueued;		// Time stamp for decision queue.
  int prev, next;		// Links for decision queue.
  Clause * reason;		// Reason (antecedent) clause.
};

/*------------------------------------------------------------------------*/

struct Score
{
  int count;			// Number of clauses.
  int flipped;			// Number of times flipped.
  double sizes;			// Sum of sizes of clauses.
  double weights;		// Weighted sum of clauses (JWH).
  int minsize;			// Smallest clause size.
};

/*------------------------------------------------------------------------*/

struct Clause
{
  long added;			// Identify clause uniquely.
  bool redundant;		// Redundant so not irredundant.
  bool garbage;			// Marked garbage thus collect.
  bool reason;			// Active reason clause.
  bool used;			// Used since last reduction.
  int glue;			// Glucose level if redundant.
  int size;			// Actual size of clause.
  int search;			// Last search position.
  int literals[];		// Inlined literals.
};

/*------------------------------------------------------------------------*/

struct Watch {
  int blit;			// Blocking literal.
  int size;			// Size of clause.
  Clause * clause;		// Watched clause.
};

/*------------------------------------------------------------------------*/

struct Frame
{
  int decision;			// Frame literal.
  int trail;			// Trail at time of decision.
  bool lookahead;		// Is this is a look-ahead decision?
  long stamp;			// Time stamp for computing glue.
};

/*------------------------------------------------------------------------*/

struct Average {
  SaDiCaL * sadical;
  const char * name;
  double val;			// Current average value.
  double alpha;			// Percentage contribution of new values.
  double beta;			// Current upper approximation of alpha.
  long wait;			// Count-down 'beta' instead of 'alpha'.
  long period;			// Length of current waiting phase.
};

/*------------------------------------------------------------------------*/

// Statistics.

struct Stats
{
  long added_units; // added for pr-extraction
  long added_units_pr;
  long added_binaries_pr;
  long added_trinaries_pr;
  long reducts_generated;
  long reducts_satisfiable;
  long candidates_processed;
  long candidates_blocked;
  long variables_expanded; // end stats for pr-extraction
  long conflicts;
  long decisions;
  long propagations;
  long simplifications;
  long reductions;
  long restarts;
  long reused;
  struct {
    long added;			// Added clauses.
    long redundant;		// Current redundant clauses.
    long irredundant;		// Current irredundant clauses.
    long collected;		// Collected bytes of clauses.
    long allocated;		// Allocated bytes of clauses.
  } clauses;
  long units;
  struct {
    long current;		// Currently allocated heap memory.
    long allocated;		// Allocated heap memory in total.
    long max;			// Maximum allocated heap memory.
  } heap;
};

/*------------------------------------------------------------------------*/

struct Solver {			// Extends until "END of 'struct Solver'".

  STACK (int) units;
  STACK (int) * touched_list;
  FILE * pr_clause_out;
  FILE * pr_clause_full_out;
  FILE * pr_units;
  FILE * pr_units_full;
  bool top_level_conflict;
  long * find_vars;
  long find_time;
  int new_pr;
  
  SaDiCaL * sadical;

  size_t size;			// Number of allocated variables.
  int max_var;			// Maximum variable index used.

  Var * vars;			// Table of all variables.
  Val * vals;			// Current assignment (-1, 0, 1).

  Watches * watches;		// Table of all watched literals.
  Score * scores;		// Table of all literal scores.

  Clauses clauses;		// Stack of pointers to all clauses.
  bool inconsistent;		// CNF already inconsistent.
  bool do_not_save_phases;

  long stamp;			// Time stamp for marking.
  Ints original;		// Temporary original clause.
  Ints clause;			// Temporary simplified clause.

  Ints trail;			// Trail of assigned variables.
  int next_to_propagate;	// Position of literal on trail.

  int level;			// Frame level.
  int balance;                  // PR balance.
  int mode;			// Heuristic mode.
  STACK (Frame) frames;		// Decision frames.

  STACK (Var *) analyzed;	// Analyzed variables.

  struct {
    int first, last;		// Head and tail of list.
    int searched;		// Last searched decision variable.
    long enqueued;		// Time stamp for decision queue.
  } queue;

  /*----------------------------------------------------------------------*/

  Stats local;			// Local stats of this solver.

  /*----------------------------------------------------------------------*/

  // Limits.

  struct {
    long reduce;
    long restart;
    int simplify;
  } lim;

  struct {
    long reduce;
  } inc;

  /*----------------------------------------------------------------------*/

  // Moving averages.

  struct {
    struct { Average fast, slow; } glue;
    Average jump;
    Average size;
  } avg;

};	// END of 'struct Solver'.

/*------------------------------------------------------------------------*/

struct SaDiCaL {	// Extends until "END of 'struct SaDiCaL'".

  Solver * inner;
  Solver * outer;

  /*----------------------------------------------------------------------*/

  // Options.

  struct {
#   define OPTION(NAME,TYPE,VAL,MIN,MAX,DESCRIPTION) \
    TYPE NAME;
    OPTIONS
#   undef OPTION
  } opts;


  /*----------------------------------------------------------------------*/

  // Statistics.

  Stats total;			// Total stats of both solvers.

  // Pruning statistics gathered only here.

  long lookaheads, pure, pruned;
  struct { double looking, filtering, pruning, simplifying, generating, adding, exploring; } time;
  struct {
    long generated, unsat;
    struct { long considered, filtered, copied; } clauses;
    struct { long checked, assumed, propagations; } filter;
  } reduct;

  /*----------------------------------------------------------------------*/

  FILE * proof;
  const char * proof_path;
  bool close_proof;

  /*----------------------------------------------------------------------*/

# define NUM_HEADERS 3

  struct {
    long reports;
    int entries;
    Buffer header[NUM_HEADERS];
    Buffer columns;
  } reporting;

  /*----------------------------------------------------------------------*/

  // Parsing.

  const char * input_path;	// DIMACS input file path.
  int close_input;		// 0=no, 1=fclose, 2=pclose
  FILE * input;			// Actual DIMACS input file.
  int lineno;			// Line number for error messages.

  /*----------------------------------------------------------------------*/

  // Buffer for printing witness.

  Buffer witness_buffer;

}; // END of 'struct Solver'.

/*------------------------------------------------------------------------*/

#define INC_STATS(NAME) \
do { \
  solver->local.NAME++; \
  solver->sadical->total.NAME++; \
} while (0)

#define ADD_STATS(NAME, NUM) \
do { \
  long TMP = (NUM); \
  solver->local.NAME += TMP; \
  solver->sadical->total.NAME += TMP; \
} while (0)


#define DEC_STATS(NAME) \
do { \
  assert (solver->local.NAME >= 0); \
  solver->local.NAME--; \
  assert (solver->sadical->total.NAME >= 0); \
  solver->sadical->total.NAME--; \
} while (0)

/*------------------------------------------------------------------------*/

#define RELATIVE(A,B) ((double)((B) ? (A) / (double)(B) : 0))
#define PERCENT(A,B) (!(A) && !(B) ? 100 : RELATIVE (100.0*(A), (B)))

/*------------------------------------------------------------------------*/

// Logging code is only included if 'NLOG' is not defined.  If you
// configure the code with './configure -l' or just './configure -g' then
// 'NLOG' remains undefined ans logging code is included.  Logging still
// needs to be enabled at run time (option 'logging' or '-l' on the
// command line).  This is very useful for debugging.

#ifndef NLOG

void sadical_log_prefix (Solver *, const char * fmt, ...);
void sadical_log_suffix (Solver *);

void sadical_log_literals (Solver *, int* lits, int size);
void sadical_log_clause (Solver *, Clause *);

#ifdef LOG
#undef LOG
#endif

#define LOG(...) \
do { \
  if (!solver->sadical->opts.logging) break; \
  sadical_log_prefix (solver, __VA_ARGS__); \
  sadical_log_suffix (solver); \
} while (0)

// Use 'printf' style formatting to log clauses (adds " ... clause").

#define LOGCLS(C,...) \
do { \
  assert ((C)); \
  if (!solver->sadical->opts.logging) break; \
  sadical_log_prefix (solver, __VA_ARGS__); \
  sadical_log_clause (solver, C); \
  sadical_log_suffix (solver); \
} while (0)

// Same with integer literals (adds " ... clause").

#define LOGLITS(INTS,SIZE,...) \
do { \
  assert ((INTS) || !(SIZE)); \
  if (!solver->sadical->opts.logging) break; \
  sadical_log_prefix (solver, __VA_ARGS__); \
  sadical_log_literals (solver, INTS, SIZE); \
  sadical_log_suffix (solver); \
} while (0)

#else

#define LOG(...) do { } while (0)
#define LOGCLS(...) do { } while (0)
#define LOGLITS(...) do { } while (0)

#endif

/*------------------------------------------------------------------------*/

void sadical_report (SaDiCaL * sadical, char ch);

#endif
