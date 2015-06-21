open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_il1Theory bigstep_il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory integerTheory store_equivalenceTheory l1_to_il1_compilerTheory l1_il1_totalTheory

val _ = new_theory "comp_location"

val count_assign_def = Define `
(count_assign (IL1_Expr _) _ = Num 0) /\
(count_assign (IL1_SIf _ e2 e3) l = count_assign e2 l + count_assign e3 l) /\
(count_assign (IL1_While _ e2) l = count_assign e2 l) /\
(count_assign (IL1_Assign l1 e) l2 = if l1 = l2 then Num 1 else Num 0) /\
(count_assign (IL1_Seq e1 e2) l = count_assign e1 l + count_assign e2 l) /\
(count_assign (IL1_Tick e) l = count_assign e l)`

val count_deref_expr_def = Define `
(count_deref_expr (IL1_Deref l) l' = if l = l' then Num 1 else Num 0) /\
(count_deref_expr (IL1_Value _) _ = Num 0) /\
(count_deref_expr (IL1_Plus e1 e2) l = count_deref_expr e1 l + count_deref_expr e2 l) /\
(count_deref_expr (IL1_Geq e1 e2) l = count_deref_expr e1 l + count_deref_expr e2 l) /\
(count_deref_expr (IL1_EIf e1 e2 e3) l = count_deref_expr e1 l + count_deref_expr e2 l + count_deref_expr e3 l)`

val count_deref_def = Define `
(count_deref (IL1_Expr e) l = count_deref_expr e l) /\
(count_deref (IL1_SIf e1 e2 e3) l = count_deref_expr e1 l + count_deref e2 l + count_deref e3 l) /\
(count_deref (IL1_While e1 e2) l = count_deref_expr e1 l + count_deref e2 l) /\
(count_deref (IL1_Assign l1 e) l2 = count_deref_expr e l2) /\
(count_deref (IL1_Seq e1 e2) l = count_deref e1 l + count_deref e2 l) /\
(count_deref (IL1_Tick e) l = count_deref e l)`

val CONTAINS_SIMPED_THM = store_thm("CONTAINS_SIMPED_THM",
``!n e st ex n' l.(l1_to_il1_pair n e = (st, ex, n')) ==> (contains_a l (l1_to_il1 e n) <=> contains_a l st)``, rfs [EQ_IMP_THM,l1_to_il1_def, LET_DEF, contains_a_def])

val COMP_LOC_INCREASING_THM = store_thm("COMP_LOC_INCREASING_THM",
``!e n n' sl1 e1'.(l1_to_il1_pair n e = (sl1, e1', n')) ==> (n' >= n)``,
Induct_on `e` THEN rw []
THEN1 (Cases_on `l` THEN fs [l1_to_il1_pair_def] THEN EVAL_TAC)
THEN TRY (`?sl1 e1' lc2.l1_to_il1_pair n e = (sl1, e1', lc2)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl2 e2' lc3.l1_to_il1_pair lc2 e' = (sl2, e2', lc3)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl3 e3' lc4.l1_to_il1_pair lc3 e'' = (sl3, e3', lc4)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
fs [LET_DEF, l1_to_il1_pair_def] THEN
res_tac THEN
decide_tac)
THEN1 ((`?sl1 e1' n''.l1_to_il1_pair n' e = (sl1, e1', n'')` by metis_tac [L1_TO_IL1_TOTAL_THM]) THEN fs [l1_to_il1_pair_def, LET_DEF])
)

val COMPILER_LOC_CHANGE_THM = store_thm("COMPILER_LOC_CHANGE_THM",
``!st ex n n' e.(l1_to_il1_pair n e = (st, ex, n')) ==> (n <> n') ==> contains_a (Compiler n) (l1_to_il1 e n)``,
Induct_on `e` THEN rw []

THEN1 (Cases_on `l` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, contains_a_def])

THEN TRY (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def]
THEN rw []
THEN imp_res_tac COMP_LOC_INCREASING_THM
THEN rw [contains_a_def]
THEN res_tac

THEN Cases_on `n = rl`
THEN Cases_on `rl = rl'`
THEN Cases_on `rl' = rl''`
THEN fs [contains_a_def]
THEN FAIL_TAC "expect to fail")

THEN1 (`?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def]
THEN rw []
THEN fs [contains_a_def]))

val ALL_CO_LOCS_IN_RANGE_BA = store_thm("ALL_CO_LOCS_IN_RANGE_BA",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> contains (Compiler tn) (l1_to_il1 e n) ==> (tn >= n) /\ (tn < n')``,
Induct_on `e` THEN rw []

(* Base cases *)
THEN1 (Cases_on `l` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [])
THEN1 (Cases_on `l` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [])
(* end base cases *)

(* Most cases *)
THEN TRY (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN res_tac THEN decide_tac)
THEN `?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN res_tac THEN decide_tac)

val ALL_CO_LOCS_IN_RANGE_FOR = store_thm("ALL_CO_LOCS_IN_RANGE_FOR",
``!e n st ex n'.(l1_to_il1_pair n e = (st, ex, n')) ==> !n''.(n'' >= n) /\ (n'' < n') ==> contains_a (Compiler n'') (l1_to_il1 e n)``,
Induct_on `e` THEN rw []

THEN1 (Cases_on `l` THEN fs [l1_to_il1_pair_def] THEN rw [] THEN decide_tac)

THEN `?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN fs [contains_a_def]
THEN res_tac

THEN TRY (
Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl'` THEN rw []
THEN `n'' < rl'` by decide_tac
THEN res_tac
THEN fs [GREATER_EQ]
THEN FAIL_TAC "want to fail")

THEN1 (
Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl''` THEN rw []
THEN `n'' < rl''` by decide_tac
THEN fs [GREATER_EQ]
THEN res_tac
THEN `rl'' >= rl'` by metis_tac [COMP_LOC_INCREASING_THM]
THEN fs [GREATER_EQ]
THEN rw []
THEN Cases_on `rl' <= n''` THEN fs [NOT_LESS_EQUAL])

THEN1 (
decide_tac
)

THEN1 (
Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS, GREATER_EQ])

THEN (
Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl''` THEN rw []
THEN `n'' < n'` by decide_tac
THEN metis_tac [COMP_LOC_INCREASING_THM, GREATER_EQ, NOT_LESS_EQUAL]))

val CONTAINS_IMPLIES_COUNT_NZERO = store_thm("CONTAINS_IMPLIES_COUNT_NZERO",
``!e l.contains_a l e <=> (count_assign e l <> 0)``,
rw [EQ_IMP_THM] THEN Induct_on `e` THEN rw [contains_a_def, count_assign_def] THEN metis_tac [])

val ALL_CO_LOCS_IN_RANGE = store_thm("ALL_CO_LOCS_IN_RANGE",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> (contains (Compiler tn) (l1_to_il1 e n) <=> (tn >= n) /\ (tn < n'))``,
metis_tac [EQ_IMP_THM, ALL_CO_LOCS_IN_RANGE_BA, ALL_CO_LOCS_IN_RANGE_FOR, CONTAINS_A_SUB])

val UNCHANGED_LOC_SIMP_THM = store_thm("UNCHANGED_LOC_SIMP_THM",
``!n e st ex n' tn.(l1_to_il1_pair n e = (st,ex,n')) ⇒
     (contains_a (Compiler tn) st ⇔ tn ≥ n ∧ tn < n')``,
rw [EQ_IMP_THM] THEN metis_tac [CONTAINS_SIMPED_THM, ALL_CO_LOCS_IN_RANGE_BA, CONTAINS_A_SUB, ALL_CO_LOCS_IN_RANGE_FOR])

val _ = export_theory ()
