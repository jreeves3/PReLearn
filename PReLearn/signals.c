#include "sadical.h"
#include "internal.h"

/*------------------------------------------------------------------------*/

#include <signal.h>

/*------------------------------------------------------------------------*/

static bool signal_catched;
static SaDiCaL * static_solver;

#define SIGNALS \
SIGNAL(SIGINT) \
SIGNAL(SIGSEGV) \
SIGNAL(SIGABRT) \
SIGNAL(SIGTERM) \
SIGNAL(SIGBUS) \

#define SIGNAL(SIG) \
static void (*SIG ## _handler)(int);
SIGNALS
#undef SIGNAL

void sadical_reset_signals (SaDiCaL * solver) {
  assert (static_solver == solver);
#define SIGNAL(SIG) \
  (void) signal (SIG, SIG ## _handler); \
  SIG ## _handler = 0;
SIGNALS
#undef SIGNAL
  signal_catched = false;
  static_solver = 0;
}

static const char * signal_name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) return # SIG;
  SIGNALS
#undef SIGNAL
  return "SIGUNKNOWN";
}

static void catch_signal (int sig) {
  if (!signal_catched) {
    signal_catched = true;
    sadical_msg (static_solver, 1, "");
    sadical_msg (static_solver, 1,
      "CAUGHT SIGNAL %d %s", sig, signal_name (sig));
    sadical_pr_stats (static_solver);
//    sadical_print_statistics (static_solver);
  }
  sadical_msg (static_solver, 1, "");
  sadical_msg (static_solver, 1,
    "RERAISING SIGNAL %d %s", sig, signal_name (sig));
  sadical_reset_signals (static_solver);
  raise (sig);
}

void sadical_init_signals (SaDiCaL * solver) {
#define SIGNAL(SIG) \
  SIG ## _handler = signal (SIG, catch_signal);
  SIGNALS
#undef SIGNAL
  assert (!signal_catched);
  static_solver = solver;
}

/*------------------------------------------------------------------------*/

