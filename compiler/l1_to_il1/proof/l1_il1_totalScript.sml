open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_il1Theory bigstep_il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory integerTheory store_equivalenceTheory l1_to_il1_compilerTheory;

val _ = new_theory "l1_il1_total";

val L1_TO_IL1_TOTAL_THM = store_thm("L1_TO_IL1_TOTAL_THM",
``!e n.?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)``,
Induct_on `e` THEN rw [l1_to_il1_pair_def]
THEN TRY (Cases_on `l` THEN EVAL_TAC THEN metis_tac []) THEN
TRY (`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
rw [] THEN `?sl e''' lc''.l1_to_il1_pair lc' e'' = (sl, e''', lc'')` by METIS_TAC [] THEN rw [])
THEN TRY (`?sl e' lc.l1_to_il1_pair n' e = (sl, e', lc)` by metis_tac [] THEN rw [] THEN FAIL_TAC "since nothing else will")
THEN
`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
`?sl e''' lc''.l1_to_il1_pair lc' e = (sl, e''', lc'')` by METIS_TAC []
THEN rw []);

val _ = export_theory ();
