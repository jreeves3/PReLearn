#include "sadical.h"
#include "internal.h"

#include <string.h>

// Usage message (including long options).

void sadical_print_usage (void) {
  fputs (
"usage: sadical [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where <option> is one of the following\n"
"\n"
"  -h | --help     print this command line option summary\n"
"  -V | --version  print version and exit\n"
"  -v              increase verbose level (see also '--verbose')\n"
"  -q              no verbose messages (see also '--verbose')\n"
"  -n              dot not print assignment (see also '--witness')\n"
"  -f              force overwriting proof file (see also '--force')\n"
#ifndef NLOG
"  -l              enable low-level logging\n"
#endif
"\n"
"and '<dimacs>' is a path to a CNF file in DIMACS format.  If '-'\n"
"is specified as input file then the formula is read from '<stdin>'.\n"
"If the path '<dimacs>' has a '.xz' suffix it is uncompressed first.\n"
"If '<proof>' is specified a clausal proof is traced to this file.\n"
"Now if '-' is used, then proof is written to '<stdout>'.\n"
"\n"
"More long options with explicit values are as follows\n"
"\n"
  , stdout);
  char tmp[80];
#define OPTION(NAME,TYPE,VAL,MIN,MAX,DESCRIPTION) \
  do { \
    strcpy (tmp, #NAME "=<" #TYPE ">"); \
    printf ("  --%-23s " DESCRIPTION " [" #VAL "]\n", tmp); \
  } while (0);
  OPTIONS
#undef OPTION
  fputs (
"\n"
"which also can be used in the form '--<name>' or '--no-<name>'.\n"
  , stdout);
}

/*------------------------------------------------------------------------*/

// Check whether 'file' is accessible.

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

static bool exists (const char * path) {
  struct stat buf;
  return !stat (path, &buf);
}

/*------------------------------------------------------------------------*/

static void setopt (SaDiCaL * sadical,
                    const char * arg, const char * name, double val) {
#define OPTION(NAME,TYPE,VAL,MIN,MAX,DESCRIPTION) \
  if (!strcmp (name, #NAME)) { \
    if (val < MIN) val = MIN; \
    if (val > MAX) val = MAX; \
    sadical->opts.NAME = val; \
  } else
  OPTIONS
#undef OPTION
  DIE ("invalid long option '%s' (try '-h')", arg);
}

static double parse_val (const char * str) {
  if (!strcmp (str, "false")) return 0;
  else if (!strcmp (str, "true")) return 1;
  else return atof (str);
}

// Parse command line options.

void sadical_parse_options (SaDiCaL * sadical, int argc, char ** argv) {
  for (int i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h") ||
        !strcmp (argv[i], "--help"))
      sadical_print_usage (), exit (0);
    else if (!strcmp (argv[i], "-V") ||
             !strcmp (argv[i], "--version"))
      puts (sadical_get_version ()), exit (0);
    else if (!strcmp (argv[i], "-v")) sadical->opts.verbose++;
    else if (!strcmp (argv[i], "-q")) sadical->opts.verbose = 0;
    else if (!strcmp (argv[i], "-n")) sadical->opts.witness = false;
    else if (!strcmp (argv[i], "-f")) sadical->opts.force = true;
#ifndef NLOG
    else if (!strcmp (argv[i], "-l")) sadical->opts.logging = true;
#endif
    else if (argv[i][0] == '-' && argv[i][1] == '-') {
      if (argv[i][2] == 'n' && argv[i][3] == 'o' && argv[i][4] == '-') {
	setopt (sadical, argv[i], argv[i] + 5, 0);
      } else {
	char * tmp = strdup (argv[i] + 2);
	char * p = strchr (tmp, '=');
	if (p) { *p++ = 0; setopt (sadical, argv[i], tmp, parse_val (p)); }
	else setopt (sadical, argv[i], tmp, 1);
	free (tmp);
      }
    } else if (argv[i][0] == '-' && argv[i][1])
      DIE ("invalid option '%s' (try '-h')", argv[i]);
    else if (sadical->proof_path)
      DIE ("too many files '%s', '%s' and '%s' specified",
        sadical->input_path, sadical->proof_path, argv[i]);
    else if (sadical->input_path) sadical->proof_path = argv[i];
    else sadical->input_path = argv[i];
  }
  if (!sadical->input_path) sadical->input_path = "-";
  else if (!exists (sadical->input_path))
    DIE ("can not access '%s'", sadical->input_path);
  if (sadical->proof_path &&
      !sadical->opts.force &&
      strcmp (sadical->proof_path, "/dev/null") &&
      exists (sadical->proof_path))
    DIE ("proof file '%s' already exists (use '-f')", sadical->proof_path);
}

/*------------------------------------------------------------------------*/

void sadical_setup_proof (SaDiCaL * sadical) {
  if (sadical->proof_path) {
    if (!strcmp (sadical->proof_path, "-")) {
      sadical->proof_path = "<stdout>";
      sadical->proof = stdout;
      assert (!sadical->close_proof);
      if (sadical->opts.binary) {
	MSG (1, "forced to write ASCII proof to '<stdout>'");
	sadical->opts.binary = false;
      }
    } else {
      if (!(sadical->proof = fopen (sadical->proof_path, "w")))
	DIE ("can not write proof to '%s'", sadical->proof_path);
      sadical->close_proof = true;
    }
    MSG (1, "proof path '%s'", sadical->proof_path);
  } else MSG (1, "no proof trace file given (proof tracing disabled)");
}

/*------------------------------------------------------------------------*/

static void print_bool_val (bool v) {
  if (v) printf ("true"); else printf ("false");
}

static void print_int_val (int v) { printf ("%d", v); }

static void print_double_val (double g) { printf ("%g", g); }

void sadical_print_non_default_options (SaDiCaL * sadical) {
//  assert (sadical->opts.verbose);
  int n = 0;
#define OPTION(NAME,TYPE,VAL,MIN,MAX,DESCRIPTION) \
  if ((double) VAL != (double) sadical->opts.NAME) { \
    if (!n++) printf ("c\nc non default options:\nc\n"); \
    printf ("c --" #NAME "="); \
    print_ ## TYPE ## _val (sadical->opts.NAME); \
    fputc ('\n', stdout); \
  }
  OPTIONS
#undef OPTION
  if (n) printf ("c\n");
  else printf ("c\nc all options have default values\nc\n");
  fflush (stdout);
}

