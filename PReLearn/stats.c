#include "sadical.h"
#include "internal.h"

/*------------------------------------------------------------------------*/

#include <sys/time.h>
#include <sys/resource.h>

double sadical_process_time (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

size_t sadical_maximum_resident_set_size (void) {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  return ((size_t) u.ru_maxrss) << 10;
}

/*------------------------------------------------------------------------*/

void sadical_pr_stats (SaDiCaL * sadical) {
  double t = sadical_process_time ();
  Stats * o = &sadical->outer->local;
//  Stats * g = &sadical->total;
  
  printf ("c variables expanded: %12ld \n",
          o->variables_expanded);
  printf ("c generated reducts:  %12ld      %7.0f%% satisfiable\n",
          o->reducts_generated,
          PERCENT (o->reducts_satisfiable, o->reducts_generated));
  printf ("c satisfiable reducts:%12ld \n",
          o->reducts_satisfiable);
  printf ("c added units:        %12ld \n",
          o->added_units);
  printf ("c added pr units:     %12ld \n",
          o->added_units_pr);
  printf ("c added pr binaries:  %12ld \n",
          o->added_binaries_pr);
  printf ("c added pr trinaries: %12ld \n",
          o->added_trinaries_pr);
  printf ("c procesed candidates:%12ld \n",
          o->candidates_processed);
  printf ("c blocked candidates: %12ld \n",
          o->candidates_blocked);
//  double r = sadical_maximum_resident_set_size ();
  printf ("c filtering:          %12.2f sec %7.0f%% of process time\n",
          sadical->time.filtering, PERCENT (sadical->time.filtering, t));
  printf ("c generating:         %12.2f sec %7.0f%% of process time\n",
          sadical->time.generating, PERCENT (sadical->time.generating, t));
  printf ("c pruning:            %12.2f sec %7.0f%% of process time\n",
          sadical->time.pruning, PERCENT (sadical->time.pruning, t));
  printf ("c adding:             %12.2f sec %7.0f%% of process time\n",
          sadical->time.adding, PERCENT (sadical->time.adding, t));
  printf ("c exploring:          %12.2f sec %7.0f%% of process time\n",
          sadical->time.exploring, PERCENT (sadical->time.exploring, t));
  printf ("c total process time: %12.2f sec\n", t);
//  printf ("c maximum heap:       %12.2f MB\n",
//          o->heap.max / (double) (1<<20));
  fflush (stdout);
}

void sadical_print_statistics (SaDiCaL * sadical) {
  if (!sadical->opts.verbose) return;
  double t = sadical_process_time ();
  Stats * o = &sadical->outer->local;
  Stats * g = &sadical->total;
  printf ("c\n");
  printf ("c simplifications: %13ld     %7.0f  conflicts/simplification"
    "%5.0f%%\n",
    o->simplifications,
    RELATIVE (o->conflicts, o->simplifications),
    PERCENT (o->simplifications, g->simplifications));
  if (sadical->opts.reduce)
  printf ("c reductions:      %13ld     %7.0f  conflicts/reduction     "
    "%5.0f%%\n",
    o->reductions, RELATIVE (o->conflicts, o->reductions),
    PERCENT (o->reductions, g->reductions));
  if (sadical->opts.restart)
  printf ("c restarts:        %13ld     %7.0f  conflicts/restart       "
    "%5.0f%%\n",
    o->restarts, RELATIVE (o->conflicts, o->restarts),
    PERCENT (o->restarts, g->restarts));
  printf ("c conflicts:       %13ld     %7.0f  conflicts/sec           "
    "%5.0f%%\n",
    o->conflicts, RELATIVE (o->conflicts, t),
    PERCENT (o->conflicts, g->conflicts));
  printf ("c decisions:       %13ld     %7.0f  decisions/sec           "
    "%5.0f%%\n",
    o->decisions, RELATIVE (o->decisions, t),
    PERCENT (o->decisions, g->decisions));
  printf ("c propagations:    %13ld     %7.1f  millions/sec            "
    "%5.0f%%\n",
    o->propagations, RELATIVE (o->propagations/1e6, t),
    PERCENT (o->propagations, g->propagations));
  if (sadical->opts.prune) {
  printf ("c\n");
  printf ("c pure:            %13ld     %7.0f%% of look-aheads\n",
    sadical->pure, PERCENT (sadical->pure, sadical->lookaheads));
  printf ("c look-ahead:      %13ld     %7.0f%% of outer decisions      "
    "%5.0f%%\n",
    sadical->lookaheads,
    PERCENT (sadical->lookaheads, o->decisions),
    PERCENT (sadical->lookaheads, g->decisions));
  printf ("c pruned:          %13ld     %7.0f%% of outer conflicts      "
    "%5.0f%%\n",
    sadical->pruned,
    PERCENT (sadical->pruned, o->conflicts),
    PERCENT (sadical->pruned, g->conflicts));
  printf ("c generated reducts: %11ld     %7.0f%% satisfiable\n",
    sadical->reduct.generated, 
    PERCENT (sadical->pruned, sadical->reduct.generated));
  printf ("c average size:    %13.0f     %7.0f%% of all clauses\n",
    RELATIVE (sadical->reduct.clauses.copied, sadical->reduct.generated),
    PERCENT (sadical->reduct.clauses.copied,
      sadical->reduct.clauses.considered));
  printf ("c pruning failed:  %13ld     %7.0f%% per reduct\n",
    sadical->reduct.unsat,
    PERCENT (sadical->reduct.unsat, sadical->reduct.generated));
  if (sadical->opts.filter) {
  printf ("c filter checks:   %13ld     %7.0f%% of outer satisfied clauses\n",
    sadical->reduct.filter.checked,
    PERCENT (
      sadical->reduct.filter.checked,
      sadical->reduct.clauses.copied + sadical->reduct.clauses.filtered));
  printf ("c average filtered: %12.1f     %7.0f%% per reduct\n",
    RELATIVE (sadical->reduct.clauses.filtered, sadical->reduct.generated),
    PERCENT (sadical->reduct.clauses.filtered,
      sadical->reduct.clauses.copied + sadical->reduct.clauses.filtered));
  printf ("c assumed literals: %12ld     %7.1f  per filter check\n",
    sadical->reduct.filter.assumed,
    RELATIVE (sadical->reduct.filter.assumed,
      sadical->reduct.filter.checked));
  }
  }
  printf ("c\n");
  if (sadical->opts.reuse && sadical->opts.restart)
  printf ("c reused trails:    %12ld     %7.0f%% of outer restarts      "
    "%6.0f%%\n",
    o->reused, PERCENT (o->reused, o->restarts),
    PERCENT (o->reused, g->reused));
  printf ("c collected clauses:  %10.2f MB  %7.0f%% of allocated clauses"
    "%9.0f%%\n",
    o->clauses.collected / (double) (1<<20),
    PERCENT (o->clauses.collected, o->clauses.allocated),
    PERCENT (o->clauses.collected, g->clauses.collected));
  printf ("c allocated clauses: %11.2f MB  %7.0f%% of allocated memory "
    "%9.0f%%\n",
    o->clauses.allocated / (double) (1<<20),
    PERCENT (o->clauses.allocated, o->heap.allocated),
    PERCENT (o->clauses.allocated, g->clauses.allocated));
  double r = sadical_maximum_resident_set_size ();
  printf ("c maximum heap:      %11.2f MB  %7.0f%% of resident set size"
    "%9.0f%%\n",
    o->heap.max / (double) (1<<20),
    PERCENT (o->heap.max, r),
    PERCENT (o->heap.max, g->heap.max));
  printf ("c\n");
  if (sadical->opts.prune) {
  printf ("c looking:         %13.2f sec %7.0f%% of process time\n",
    sadical->time.looking, PERCENT (sadical->time.looking, t));
  printf ("c filtering:       %13.2f sec %7.0f%% of process time\n",
    sadical->time.filtering, PERCENT (sadical->time.filtering, t));
  printf ("c pruning:         %13.2f sec %7.0f%% of process time\n",
    sadical->time.pruning, PERCENT (sadical->time.pruning, t));
  }
  printf ("c simplifying:     %13.2f sec %7.0f%% of process time\n",
    sadical->time.simplifying, PERCENT (sadical->time.simplifying, t));
  printf ("c\n");
  printf ("c resident set size: %11.2f MB\n", r / (double)(1<<20));
  printf ("c total process time: %10.2f sec\n", t);
  fflush (stdout);
}
