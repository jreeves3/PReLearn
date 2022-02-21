#include "sadical.h"
#include "stats.c"

int main (int argc, char ** argv) {
  SaDiCaL * sadical = sadical_new ();
  sadical_parse_options (sadical, argc, argv);
  sadical_print_banner ();
  sadical_setup_input (sadical);
  sadical_setup_proof (sadical);
  sadical_print_non_default_options (sadical);
  sadical_init_signals (sadical);
  sadical_parse_dimacs (sadical);
  sadical_pr_extract (sadical);
  sadical_pr_stats (sadical) ;
  
//  int res = sadical_solve (sadical);
//  sadical_print_result (sadical, res);
//  sadical_reset_signals (sadical);
//  sadical_print_statistics (sadical);
  sadical_delete (sadical);
//  return res;
}
