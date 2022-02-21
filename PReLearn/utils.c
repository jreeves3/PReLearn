#include "sadical.h"
#include "internal.h"

/*------------------------------------------------------------------------*/

#include <stdarg.h>
#include <string.h>

/*----------------------------------------------------------------------*/

// Printing error and verbose messages.

void sadical_die (const char * fmt, ...) {
  fputs ("*** 'sadical' error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

void sadical_msg (SaDiCaL * sadical, int level, const char * fmt, ...) {
#ifndef NLOG
  if (!sadical->opts.logging)
#endif
  if (level > sadical->opts.verbose) return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

// Standard logging functions.  They use a 'printf' style format and
// argument list and add a new line.  They are all defined as macros to
// avoid evaluating the arguments if logging is disabled.

#ifndef NLOG

void sadical_log_prefix (Solver * solver, const char * fmt, ...) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->opts.logging);
  fputs ("c ", stdout);
  fputs (solver == sadical->inner ? "INNER" : "OUTER", stdout);
  printf (" %d ", solver->level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
}

void sadical_log_suffix (Solver * solver) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->opts.logging);
  fputc ('\n', stdout);
  fflush (stdout);
}

void sadical_log_literals (Solver * solver, int* lits, int size) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->opts.logging);
  printf (" size %d clause", size);
  for (int i = 0; i < size; i++)
    printf (" %d", lits[i]);
}

void sadical_log_clause (Solver * solver, Clause * c) {
  SaDiCaL * sadical = solver->sadical;
  assert (sadical->opts.logging);
  if (c->redundant) printf (" redundant glue %d", c->glue);
  else fputs (" irredundant", stdout);
  printf (" size %d clause[%ld]", c->size, c->added);
  for (int i = 0; i < c->size; i++)
    printf (" %d", c->literals[i]);
}

#endif

/*------------------------------------------------------------------------*/
#ifndef NDEBUG

// For debugging purposes at this point.

void dump (Solver * solver) {
  printf ("p cnf %d %ld\n",
    solver->max_var, (long) SIZE (solver->clauses));
  for (Clause ** p = solver->clauses.begin; p < solver->clauses.end; p++) {
    Clause * c = *p;
    for (int i = 0; i < c->size; i++)
      printf ("%d ", c->literals[i]);
    printf ("0 clause[%ld]\n", c->added);
  }
}

#endif

/*------------------------------------------------------------------------*/

static int remaining_variables (Solver * solver) {
  int fixed = 0;
  if (solver->level > 0) fixed = PEEK (solver->frames, 1).trail;
  else fixed = SIZE (solver->trail);
  assert (fixed <= solver->max_var);
  return solver->max_var - fixed;
}

/*------------------------------------------------------------------------*/

// We report the time spent, the memory used etc. after the formula is
// simplified as soon a new unit is learned ('s') and if less interesting
// learned clauses are flushed in 'reduce' ('-').  This rather complex
// code is used to have a nicely formatted table format, where the numbers
// occur in columns, without the need to change it every time a new column
// is needed (or not used).

#define LINE 80

static void column (SaDiCaL * sadical, const char * name,
                   int precision, bool percent_suffix, bool flush_right,
		   double value) {
  char tmp[LINE], fmt[32];
  const char * suffix = percent_suffix ? "%%" : "";
  sprintf (fmt, "%%.%df%s", precision, suffix);
  snprintf (tmp, LINE, fmt, value);
  tmp[LINE-1] = 0;
  size_t m = strlen (tmp);
  sprintf (fmt, "%%%zd.%df%s", m - percent_suffix, precision, suffix);
  snprintf (tmp, LINE, fmt, value);
  tmp[LINE-3] = tmp[LINE-2] = '.', tmp[LINE-1] = 0;
  GPUSH (sadical->reporting.columns, ' ');
  for (const char * p = tmp; *p; p++)
    GPUSH (sadical->reporting.columns, *p);
  GPUSH (sadical->reporting.columns, 0);
  (void) POP (sadical->reporting.columns);
  size_t n = strlen (name);
  int shift;
  if (n <= m) shift = 0;
  else if (!flush_right) shift = (n - m)/2;
  else shift = 1;
  GPUSH (sadical->reporting.header[sadical->reporting.entries], ' ');
  while (SIZE (sadical->reporting.header[sadical->reporting.entries]) + n <
         SIZE (sadical->reporting.columns) + shift)
    GPUSH (sadical->reporting.header[sadical->reporting.entries], ' ');
  for (const char * p = name; *p; p++)
    GPUSH (sadical->reporting.header[sadical->reporting.entries], *p);
  GPUSH (sadical->reporting.header[sadical->reporting.entries], 0);
  (void) POP (sadical->reporting.header[sadical->reporting.entries]);
  if (++sadical->reporting.entries == NUM_HEADERS)
    sadical->reporting.entries = 0;
}

void sadical_report (SaDiCaL * sadical, char ch) {
  if (!sadical->opts.verbose) return;
  Solver * outer = sadical->outer;
  for (int i = 0; i < NUM_HEADERS; i++)
    CLEAR (sadical->reporting.header[i]);
  column (sadical, "time", 2, 0, 0, sadical_process_time ());
  column (sadical, "space", 1, 0, 0, sadical->total.heap.max/(double)(1<<20));
  column (sadical, "level", 1, 0, 0, outer->avg.jump.val);
  if (sadical->opts.reduce)
  column (sadical, "reduced", 0, 0, 0, outer->local.reductions);
  if (sadical->opts.restart)
  column (sadical, "restarts", 0, 0, 0, outer->local.restarts);
  column (sadical, "conflicts", 0, 0, 0, outer->local.conflicts);
  column (sadical, "redundant", 0, 0, 0, outer->local.clauses.redundant);
  column (sadical, "glue", 1, 0, 0, outer->avg.glue.slow.val);
  column (sadical, "size", 1, 0, 0, outer->avg.size.val);
  column (sadical, "irredundant", 0, 0, 0, outer->local.clauses.irredundant);
  int remain = remaining_variables (outer);
  column (sadical, "variables", 0, 0, 0, remain);
  column (sadical, "remaining", 0, 1, 1, PERCENT (remain, outer->max_var));
  if (!(sadical->reporting.reports++ % 20)) {
    printf ("c\n");
    for (int i = 0; i < NUM_HEADERS; i++) {
      GPUSH (sadical->reporting.header[i], 0);
      printf ("c  %s\n", BEGIN (sadical->reporting.header[i]));
    }
    printf ("c\n");
  }
  sadical->reporting.entries = 0;
  GPUSH (sadical->reporting.columns, 0);
  printf ("c %c%s\n", ch, BEGIN (sadical->reporting.columns));
  CLEAR (sadical->reporting.columns);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

// Report result of solver and print witness 'v ...' lines nicely formatted.

static void flush_witness_buffer (SaDiCaL * sadical) {
  GPUSH (sadical->witness_buffer, 0);
  fputs (sadical->witness_buffer.begin, stdout);
  fputc ('\n', stdout);
  CLEAR (sadical->witness_buffer);
  GPUSH (sadical->witness_buffer, 'v');
}

static void print_int_for_witness (SaDiCaL * sadical, int i) {
  char str[20];
  sprintf (str, " %d", i);
  size_t len = strlen (str);
  if (len + SIZE (sadical->witness_buffer) > 74)
    flush_witness_buffer (sadical);
  for (size_t i = 0; i < len; i++)
    GPUSH (sadical->witness_buffer, str[i]);
}

static void print_witness (SaDiCaL * sadical) {
  assert (sadical->opts.witness);
  GPUSH (sadical->witness_buffer, 'v');
  int max_var = sadical_max_var (sadical);
  for (int idx = 1; idx <= max_var; idx++) {
    int tmp = sadical_val (sadical, idx);
    int i = tmp < 0 ? -idx : idx;
    print_int_for_witness (sadical, i);
  }
  print_int_for_witness (sadical, 0);
  if (!EMPTY (sadical->witness_buffer))
    flush_witness_buffer (sadical);
  GRELEASE (sadical->witness_buffer);
  fflush (stdout);
}

void sadical_print_result (SaDiCaL * sadical, int res) {
  if (sadical->opts.verbose) printf ("c\n");
  if (res == 10) printf ("s SATISFIABLE\n");
  else if (res == 20) printf ("s UNSATISFIABLE\n");
  else printf ("c UNKNOWN\n");
  fflush (stdout);
  if (res == 10 && sadical->opts.witness) print_witness (sadical);
}
