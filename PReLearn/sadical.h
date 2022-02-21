#ifndef _sadical_h_INLCUDED
#define _sadical_h_INLCUDED

typedef struct SaDiCaL SaDiCaL;

void sadical_print_banner (void);
const char * sadical_get_version (void);
void sadical_print_usage (void);
SaDiCaL * sadical_new (void);
void sadical_parse_options (SaDiCaL *, int argc, char ** argv);
void sadical_setup_input (SaDiCaL *);
void sadical_setup_proof (SaDiCaL *);
void sadical_print_non_default_options (SaDiCaL *);
void sadical_die (const char * fmt, ...);
void sadical_msg (SaDiCaL *, int verbosity, const char * fmt, ...);
void sadical_parse_dimacs (SaDiCaL *);
void sadical_add_literal (SaDiCaL *, int lit);
int sadical_solve (SaDiCaL *);
int sadical_max_var (SaDiCaL *);
int sadical_val (SaDiCaL *, int lit);
int sadical_verbose (SaDiCaL *);
void sadical_print_result (SaDiCaL *, int);
double sadical_process_time (void);
void sadical_print_statistics (SaDiCaL *);
void sadical_delete (SaDiCaL *);
void sadical_init_signals (SaDiCaL *);
void sadical_reset_signals (SaDiCaL *);

void sadical_pr_extract (SaDiCaL *);
void sadical_pr_stats (SaDiCaL *);

#endif
