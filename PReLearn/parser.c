#include "sadical.h"
#include "internal.h"

#include <ctype.h>
#include <stdarg.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static void parse_error (SaDiCaL * sadical, const char * fmt, ...) {
  fprintf (stderr,
    "*** 'sadical' parse error in '%s' at line %d: ",
    sadical->input_path, sadical->lineno);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

// Read next character from input file and increase line number.

static int nextch (SaDiCaL * sadical) {
  int res = getc (sadical->input);
  if (res == '\n') sadical->lineno++;
  return res;
}

// Check that the string 'str' has the given 'suffix'.

static bool has_suffix (const char * str, const char * suffix) {
  int l = strlen (str), k = strlen (suffix);
  if (l < k) return false;
  return !strcmp (str + l - k, suffix);
}

// Use 'popen' to read compressed files by executing an external program.

static FILE *
open_and_read_pipe (SaDiCaL * sadical, const char * fmt, const char * path) {
  size_t bytes = strlen (fmt) + strlen (path) + 1;
  char * cmd = malloc (bytes);
  if (!cmd) DIE ("failed to allocate command string for opening pipe");
  ADD_GLOBAL_ALLOCATED (bytes);
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, "r");
  free (cmd);
  SUB_GLOBAL_ALLOCATED (bytes);
  return res;
}

void sadical_setup_input (SaDiCaL * sadical) {
  if (!strcmp (sadical->input_path, "-")) {
    sadical->input_path = "<stdin>";
    sadical->input = stdin;
    sadical->close_input = 0;
  } else {
    if (has_suffix (sadical->input_path, ".xz")) {
      sadical->input =
        open_and_read_pipe (sadical, "xz -d -c %s", sadical->input_path);
      sadical->close_input = 2;
    } else {
      sadical->input = fopen (sadical->input_path, "r");
      sadical->close_input = 1;
    }
  }
  if (!sadical->input) DIE ("can not open '%s'", sadical->input_path);
}

/*------------------------------------------------------------------------*/

#define NEXT nextch (sadical)
#define ERROR(...) parse_error (sadical, __VA_ARGS__)

void sadical_parse_dimacs (SaDiCaL * sadical) {
  sadical->lineno = 1;
  double start = sadical_process_time ();
  MSG (1, "parsing '%s'", sadical->input_path);
  int ch = NEXT;
  while (ch == 'c') {
    while ((ch = NEXT) != '\n')
      if (ch == EOF)
	ERROR ("unexpected end-of-file in header comment");
    ch = NEXT;
  }
  if (ch != 'p') ERROR ("expected 'c' or 'p'");
  if (NEXT != ' ') ERROR ("expected space after 'p'");
  if (NEXT != 'c') ERROR ("expected 'c' after 'p '");
  if (NEXT != 'n') ERROR ("expected 'n' after 'p c'");
  if (NEXT != 'f') ERROR ("expected 'f' after 'p cn'");
  if (NEXT != ' ') ERROR ("expected space after 'p cnf'");
  if (!(isdigit (ch = NEXT)))
    ERROR ("expected digit after 'p cnf '");
  int m = ch - '0';
  while (isdigit (ch = NEXT)) {
    if (INT_MAX/10 < m)
      ERROR ("maximum variable way too large");
    m *= 10;
    int digit = ch - '0';
    if (INT_MAX - digit < m)
      ERROR ("maximum variable too large");
    m += digit;
  }
  if (ch != ' ')
    ERROR ("expected space after 'p cnf %d'", m);
  if (!(isdigit (ch = NEXT)))
    ERROR ("expected digit after 'p cnf %d '", m);
  int n = ch - '0';
  while (isdigit (ch = NEXT)) {
    if (INT_MAX/10 < n)
      ERROR ("number of clauses way too large");
    n *= 10;
    int digit = ch - '0';
    if (INT_MAX - digit < n)
      ERROR ("number of clauses too large");
    n += digit;
  }
  while (ch == ' ' || ch == '\t') ch = NEXT;
  if (ch == '\r') ch = NEXT;
  if (ch != '\n')
    ERROR ("expected new line after 'p cnf %d %d'", m, n);
  MSG (1, "found 'p cnf %d %d' header", m, n);
  int lit = 0;
  for (;;) {
    ch = NEXT;
    if (ch == 'c') {
      while ((ch = NEXT) != '\n')
	if (ch == EOF)
	  ERROR ("unexpected end-of-file in comment");
      continue;
    }
    if (ch == ' ') continue;
    if (ch == '\t') continue;
    if (ch == '\r') continue;
    if (ch == '\n') continue;
    if (ch == EOF) break;
    int sign = 1;
    if (ch == '-') {
      sign = -1;
      if (!isdigit (ch = NEXT))
	ERROR ("expected digit after '-'");
      if (ch == '0')
	ERROR ("expected positive digit after '-'");
    } else if (!isdigit (ch))
      ERROR ("expected digit or '-'");
    int idx = ch - '0';
    while (isdigit (ch = NEXT)) {
      if (INT_MAX/10 < idx)
	ERROR ("literal way too large");
      idx *= 10;
      int digit = ch - '0';
      if (INT_MAX - digit < idx)
	ERROR ("literal really too large");
      idx += digit;
    }
    lit = sign * idx;
    if (ch == 'c') {
      while ((ch = NEXT) != '\n')
	if (ch == EOF)
	  ERROR (
	    "unexpected end-of-file in comment after literal %d", lit);
    } else if (ch != ' ' && ch != '\t' && ch != '\r' && ch != '\n')
      ERROR ("expected white space or comment after literal %d", lit);
    if (idx > m) ERROR ("literal %d exceeds maximum variable %d", lit, m);
//    if (!n) ERROR ("too many clauses");
    sadical_add_literal (sadical, lit);
//    if (!lit) assert (n > 0), n--;
  }
  if (lit)
    ERROR ("terminating '0' missing");
//  if (n == 1)
//    ERROR ("one clause missing");
//  if (n > 1)
//    ERROR ("%d clauses missing", n);
  if (sadical->close_input == 1) fclose (sadical->input);
  if (sadical->close_input == 2) pclose (sadical->input);
  double t = sadical_process_time () - start;
  MSG (1, "parsed DIMACS in %.2f seconds", t);
  MSG (1, "");
}

