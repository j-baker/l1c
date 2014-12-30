open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory;

val _ = new_theory "l1_to_il1";

val l1_to_il1_pair_def = Define `
    (l1_to_il1_pair lc (B_Value (B_N n)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Integer n), lc)) /\
    (l1_to_il1_pair lc (B_Value (B_B b)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Boolean b), lc)) /\
    (l1_to_il1_pair lc (B_Value B_Skip) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value IL1_ESkip, lc)) /\
    (l1_to_il1_pair lc (B_Deref l) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Deref (User l), lc)) /\

    (l1_to_il1_pair lc (B_Assign l e) =
        let (sl, e', lc2) = l1_to_il1_pair lc e
        in
            (IL1_Seq sl (IL1_Assign (User l) e'), IL1_Value IL1_ESkip,lc2)) /\

    (l1_to_il1_pair lc (B_Seq e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in (IL1_Seq sl1 sl2, e2', lc3)) /\

    (l1_to_il1_pair lc (B_While e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2 in
        let (sl3, e3', lc4) = l1_to_il1_pair lc3 e1
        in
            (IL1_Seq sl1 (IL1_While e1' (IL1_Seq sl2 sl3)), IL1_Value IL1_ESkip, lc4)) /\

    (l1_to_il1_pair lc (B_If e1 e2 e3) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in 
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2 in
        let (sl3, e3', lc4) = l1_to_il1_pair lc3 e3
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (Compiler lc4) e1')) (IL1_SIf (IL1_Deref (Compiler lc4)) sl2 sl3), IL1_EIf (IL1_Deref (Compiler lc4)) e2' e3', lc4 + 1)) /\

    (l1_to_il1_pair lc (B_Plus e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (Compiler lc3) e1')) sl2, IL1_Plus (IL1_Deref (Compiler lc3)) e2', lc3 + 1)) /\ 

    (l1_to_il1_pair lc (B_Geq e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (Compiler lc3) e1')) sl2, IL1_Geq (IL1_Deref (Compiler lc3)) e2', lc3 + 1))
`;

val l1_to_il1_def = Define `l1_to_il1 e n = let (s, te, lc) = l1_to_il1_pair n e in IL1_Seq s (IL1_Expr te)`;

val l1_il1_val_def = Define `(l1_il1_val (B_N n) = IL1_Integer n) /\
(l1_il1_val (B_B b) = IL1_Boolean b) /\
(l1_il1_val (B_Skip) = IL1_ESkip)`;

val equiv_def = Define `equiv s1 s2 = !k.User k ∈ FDOM s1 ==> (User k ∈ FDOM s2 /\ (s1 ' (User k) = s2 ' (User k)))`;

val EQUIV_REFL_THM = store_thm("EQUIV_REFL_THM",
``!x.equiv x x``,
fs [equiv_def]);

val conv_ind_def = Define `conv_ind = !p v s1.bs_il1 p v s1 ==> !e s.((FST p = l1_to_il1 e 0) /\ (SND p = MAP_KEYS User s)) ==> !n.?s2.bs_il1 (l1_to_il1 e n, MAP_KEYS User s) v s2 /\ equiv s1 s2`;


val minimal_store_def = Define `minimal_store e s = !k.k ∈ FDOM s ==> contains_l1 k e`;

val count_assign_def = Define `
(count_assign (IL1_Expr _) _ = 0) /\
(count_assign (IL1_SIf _ e2 e3) l = count_assign e2 l + count_assign e3 l) /\
(count_assign (IL1_While _ e2) l = count_assign e2 l) /\
(count_assign (IL1_Assign l1 e) l2 = if l1 = l2 then 1 else 0) /\
(count_assign (IL1_Seq e1 e2) l = count_assign e1 l + count_assign e2 l)`;

val count_deref_expr_def = Define `
(count_deref_expr (IL1_Deref l) l' = if l = l' then 1 else 0) /\
(count_deref_expr (IL1_Value _) _ = 0) /\
(count_deref_expr (IL1_Plus e1 e2) l = count_deref_expr e1 l + count_deref_expr e2 l) /\
(count_deref_expr (IL1_Geq e1 e2) l = count_deref_expr e1 l + count_deref_expr e2 l) /\
(count_deref_expr (IL1_EIf e1 e2 e3) l = count_deref_expr e1 l + count_deref_expr e2 l + count_deref_expr e3 l)`;

val count_deref_def = Define `
(count_deref (IL1_Expr e) l = count_deref_expr e l) /\
(count_deref (IL1_SIf e1 e2 e3) l = count_deref_expr e1 l + count_deref e2 l + count_deref e3 l) /\
(count_deref (IL1_While e1 e2) l = count_deref_expr e1 l + count_deref e2 l) /\
(count_deref (IL1_Assign l1 e) l2 = count_deref_expr e l2) /\
(count_deref (IL1_Seq e1 e2) l = count_deref e1 l + count_deref e2 l)`;

val L1_TO_IL1_TOTAL_THM = store_thm("L1_TO_IL1_TOTAL_THM",
``!e n.?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)``,
Induct_on `e` THEN rw [l1_to_il1_pair_def]
THEN TRY (Cases_on `b` THEN EVAL_TAC THEN metis_tac []) THEN
TRY (`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
rw [] THEN `?sl e''' lc''.l1_to_il1_pair lc' e'' = (sl, e''', lc'')` by METIS_TAC [] THEN rw [])
THEN TRY (`?sl e' lc.l1_to_il1_pair n' e = (sl, e', lc)` by metis_tac [] THEN rw [] THEN FAIL_TAC "since nothing else will")
THEN
`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
`?sl e''' lc''.l1_to_il1_pair lc' e = (sl, e''', lc'')` by METIS_TAC []
THEN rw []);

val COMP_LOC_INCREASING_THM = store_thm("COMP_LOC_INCREASING_THM",
``!e n n' sl1 e1'.(l1_to_il1_pair n e = (sl1, e1', n')) ==> (n' >= n)``,
Induct_on `e` THEN rw []
THEN1 (Cases_on `b` THEN fs [l1_to_il1_pair_def] THEN EVAL_TAC)
THEN TRY (`?sl1 e1' lc2.l1_to_il1_pair n e = (sl1, e1', lc2)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl2 e2' lc3.l1_to_il1_pair lc2 e' = (sl2, e2', lc3)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl3 e3' lc4.l1_to_il1_pair lc3 e'' = (sl3, e3', lc4)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
fs [LET_DEF, l1_to_il1_pair_def] THEN
res_tac THEN
decide_tac)
THEN1 ((`?sl1 e1' n''.l1_to_il1_pair n' e = (sl1, e1', n'')` by metis_tac [L1_TO_IL1_TOTAL_THM]) THEN fs [l1_to_il1_pair_def, LET_DEF])
THEN1 (`?sl1 e1' lc2.l1_to_il1_pair n e = (sl1, e1', lc2)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl2 e2' lc3.l1_to_il1_pair lc2 e' = (sl2, e2', lc3)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl3 e3' lc4.l1_to_il1_pair lc3 e = (sl3, e3', lc4)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
fs [LET_DEF, l1_to_il1_pair_def] THEN
res_tac THEN
decide_tac));

val CONTAINS_CONVERT_THM = store_thm("CONTAINS_CONVERT_THM",
``!e n l.contains l (l1_to_il1 e n) <=> ?st ex n'.(l1_to_il1_pair n e = (st, ex, n')) /\ (contains l st \/ contains_expr l ex)``,
rw [EQ_IMP_THM] THEN1 (`?st ex n'.l1_to_il1_pair n e = (st, ex, n')` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN fs [l1_to_il1_def, LET_DEF, contains_def]) THEN rw [l1_to_il1_def, LET_DEF, contains_def]);

val COMPILER_LOC_CHANGE_THM = store_thm("COMPILER_LOC_CHANGE_THM",
``!st ex n n' e.(l1_to_il1_pair n e = (st, ex, n')) ==> (n <> n') ==> contains_a (Compiler n) (l1_to_il1 e n)``,
Induct_on `e` THEN rw []

THEN1 (Cases_on `b` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, contains_a_def])

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
THEN fs [contains_a_def])

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def]
THEN rw []
THEN imp_res_tac COMP_LOC_INCREASING_THM
THEN rw [contains_a_def]
THEN res_tac

THEN Cases_on `n = rl`
THEN Cases_on `rl = rl'`
THEN Cases_on `rl' = rl''`
THEN fs [contains_a_def]
THEN FAIL_TAC "expect to fail"));

val ALL_CO_LOCS_IN_RANGE_BA = store_thm("ALL_CO_LOCS_IN_RANGE_BA",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> contains (Compiler tn) (l1_to_il1 e n) ==> (tn >= n) /\ (tn < n')``,
Induct_on `e` THEN rw []

(* Base cases *)
THEN1 (Cases_on `b` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [])
THEN1 (Cases_on `b` THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [])
(* end base cases *)

(* Most cases *)
THEN TRY (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN res_tac THEN decide_tac)
THEN `?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def] THEN rw [] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN res_tac THEN decide_tac);

val ALL_CO_LOCS_IN_RANGE_FOR = store_thm("ALL_CO_LOCS_IN_RANGE_FOR",
``!e n st ex n'.(l1_to_il1_pair n e = (st, ex, n')) ==> !n''.(n'' >= n) /\ (n'' < n') ==> contains_a (Compiler n'') (l1_to_il1 e n)``,
Induct_on `e` THEN rw []

THEN1 (Cases_on `b` THEN fs [l1_to_il1_pair_def] THEN rw [] THEN decide_tac)

THEN TRY (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN rw [contains_a_def]
THEN res_tac
THEN Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl'` THEN rw []
THEN `n'' < rl'` by decide_tac
THEN res_tac
THEN fs [GREATER_EQ]
THEN FAIL_TAC "want to fail")

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN rw [contains_a_def]
THEN res_tac
THEN Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl''` THEN rw []
THEN `n'' < rl''` by decide_tac
THEN fs [GREATER_EQ]
THEN res_tac
THEN `rl'' >= rl'` by metis_tac [COMP_LOC_INCREASING_THM]
THEN fs [GREATER_EQ]
THEN rw []
THEN Cases_on `rl' <= n''` THEN fs [NOT_LESS_EQUAL])

THEN1 (`?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN rw [contains_a_def]
THEN res_tac
THEN fs [contains_a_def])

THEN1 (fs [l1_to_il1_pair_def] THEN rw [] THEN decide_tac)

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN rw [contains_a_def]
THEN res_tac
THEN Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS, GREATER_EQ])

THEN (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [LET_DEF, l1_to_il1_def, l1_to_il1_pair_def] THEN rw []
THEN rw [contains_a_def]
THEN fs [contains_a_def]
THEN res_tac
THEN Cases_on `n'' < rl` THEN fs [contains_a_def] THEN rw []
THEN fs [NOT_LESS]
THEN Cases_on `n'' = rl''` THEN rw []
THEN `n'' < n'` by decide_tac
THEN fs [GREATER_EQ]
THEN res_tac
THEN `n' >= rl'` by metis_tac [COMP_LOC_INCREASING_THM]
THEN fs [GREATER_EQ]
THEN rw []
THEN Cases_on `rl' <= n''` THEN fs [NOT_LESS_EQUAL]));

val CONTAINS_IMPLIES_COUNT_NZERO = store_thm("CONTAINS_IMPLIES_COUNT_NZERO",
``!e l.contains_a l e <=> (count_assign e l <> 0)``,
rw [EQ_IMP_THM] THEN Induct_on `e` THEN rw [contains_a_def, count_assign_def] THEN metis_tac []);

(* Couldn't find the appropriate thm in the lib *)
val SILLY_ARITH_THM = store_thm("SILLY_ARITH_THM",
``!a b.(a + 1 <= b) <=> (a < b)``, DECIDE_TAC);

val SILLY_ARITH_2_THM = store_thm("SILLY_ARITH_2_THM",
``!a b.(a + 1 <= b) ==> (a <= b)``, DECIDE_TAC);


val ALL_CO_LOCS_IN_RANGE = store_thm("ALL_CO_LOCS_IN_RANGE",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> (contains (Compiler tn) (l1_to_il1 e n) <=> (tn >= n) /\ (tn < n'))``,
metis_tac [EQ_IMP_THM, ALL_CO_LOCS_IN_RANGE_BA, ALL_CO_LOCS_IN_RANGE_FOR, CONTAINS_A_SUB]);


!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> if (tn >= n) /\ (tn < n') then (count_deref (l1_to_il1 e n) (Compiler tn) = 1) else (count_deref (l1_to_il1 e n) (Compiler tn) = 0)
Induct_on `e` THEN rw []

(* Base case *)
THEN TRY (Cases_on `b` THEN fs [count_assign_def, l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, ALL_CO_LOCS_IN_RANGE, NOT_LESS, NOT_LESS_EQUAL, GREATER_EQ] THEN rw [] THEN EVAL_TAC THEN decide_tac)

(* Operations *)
THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_deref_def, count_deref_expr_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_deref_def, count_deref_expr_def]
THEN1 (`(count_deref st'' (Compiler rl') = 0) /\ (count_deref_expr ex' (Compiler rl') = 0) /\ (count_deref st' (Compiler rl') = 0) /\ (count_deref_expr ex'' (Compiler rl') = 0)` by metis_tac [NOT_LESS_EQUAL, LESS_EQ_REFL] THEN rw [])
THEN Cases_on `rl <= tn`
THEN1
    (`count_deref st'' (Compiler tn) + count_deref_expr ex'' (Compiler tn) = 1` by (`tn < rl'` by decide_tac THEN metis_tac [])
    THEN rw [] THEN `~(tn < rl)` by metis_tac [NOT_LESS] THEN rw [] THEN `(count_deref st' (Compiler tn) = 0) /\ (count_deref_expr ex' (Compiler tn) = 0)` by metis_tac [] THEN decide_tac)
THEN1
    (`(count_deref st'' (Compiler tn) = 0) /\ (count_deref_expr ex'' (Compiler tn) = 0)` by metis_tac []
    THEN rw [] THEN `tn < rl` by metis_tac [NOT_LESS] THEN rw [] THEN `count_deref st' (Compiler tn) + count_deref_expr ex' (Compiler tn) = 1` by metis_tac [] THEN decide_tac))

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_deref_def, count_deref_expr_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_deref_def, count_deref_expr_def] THEN (metis_tac [NOT_LESS, NOT_LESS_EQ, SILLY_ARITH_2_THM, SILLY_ARITH_THM, LESS_LESS_EQ_TRANS, NOT_LESS_EQUAL, NOT_LESS, SILLY_ARITH_2_THM, LESS_TRANS]))

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_deref_def, count_deref_expr_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_deref_def, count_deref_expr_def]
THEN1 (`(count_deref st'' (Compiler rl') = 0) /\ (count_deref_expr ex' (Compiler rl') = 0) /\ (count_deref st' (Compiler rl') = 0) /\ (count_deref_expr ex'' (Compiler rl') = 0)` by metis_tac [NOT_LESS_EQUAL, LESS_EQ_REFL] THEN rw [])
THEN Cases_on `rl <= tn`
THEN1
    (`count_deref st'' (Compiler tn) + count_deref_expr ex'' (Compiler tn) = 1` by (`tn < rl'` by decide_tac THEN metis_tac [])
    THEN rw [] THEN `~(tn < rl)` by metis_tac [NOT_LESS] THEN rw [] THEN `(count_deref st' (Compiler tn) = 0) /\ (count_deref_expr ex' (Compiler tn) = 0)` by metis_tac [] THEN decide_tac)
THEN1
    (`(count_deref st'' (Compiler tn) = 0) /\ (count_deref_expr ex'' (Compiler tn) = 0)` by metis_tac []
    THEN rw [] THEN `tn < rl` by metis_tac [NOT_LESS] THEN rw [] THEN `count_deref st' (Compiler tn) + count_deref_expr ex' (Compiler tn) = 1` by metis_tac [] THEN decide_tac))

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_deref_def, count_deref_expr_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_deref_def, count_deref_expr_def] THEN (metis_tac [NOT_LESS, NOT_LESS_EQ, SILLY_ARITH_2_THM, SILLY_ARITH_THM, LESS_LESS_EQ_TRANS, NOT_LESS_EQUAL, NOT_LESS, SILLY_ARITH_2_THM, LESS_TRANS]))

(* IF *)
`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]


val assign_deref_case = (`?st ex rl.l1_to_il1_pair n' e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_assign_def] THEN (TRY decide_tac) THEN metis_tac []);

val op_1_case = (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_assign_def]
THEN1 ( `~(rl' < rl') /\ ~(rl' < rl)` by metis_tac [NOT_LESS, LESS_OR_EQ] THEN
`count_assign st'' (Compiler rl') = 0` by metis_tac [NOT_LESS, LESS_OR_EQ] THEN rw [] THEN metis_tac [])
THEN Cases_on `rl <= tn` THEN fs [] THEN rw []
THENL [(`tn < rl'` by decide_tac
THEN `count_assign st'' (Compiler tn) = 1` by metis_tac [LESS_SUC_IMP]),
(
`count_assign st'' (Compiler tn) = 0` by metis_tac []
)] THEN fs [NOT_LESS_EQUAL] THEN metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ]);

val op_2_case = (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN Cases_on `n = n'` THEN1 (rw [] THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac)
THEN metis_tac [CONTAINS_IMPLIES_COUNT_NZERO, CONTAINS_A_SUB, ALL_CO_LOCS_IN_RANGE]);

val EACH_CO_LOC_ASSIGNED_ONCE = store_thm("EACH_CO_LOC_ASSIGNED_ONCE",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> if (tn >= n) /\ (tn < n') then (count_assign (l1_to_il1 e n) (Compiler tn) = 1) else (count_assign (l1_to_il1 e n) (Compiler tn) = 0)``,
Induct_on `e` THEN rw []

THEN TRY (Cases_on `b` THEN fs [count_assign_def, l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, ALL_CO_LOCS_IN_RANGE, NOT_LESS, NOT_LESS_EQUAL, GREATER_EQ] THEN rw [] THEN EVAL_TAC THEN decide_tac)

THEN1 op_1_case
THEN1 op_2_case

THEN1 op_1_case
THEN1 op_2_case

(*If *)

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_assign_def]
THEN1 (`~(rl'' < rl'') /\ ~(rl'' < rl') /\ ~(rl'' < rl)` by metis_tac [NOT_LESS, LESS_OR_EQ, LESS_EQ_TRANS] THEN
`count_assign st'' (Compiler rl'') = 0` by metis_tac [] THEN `count_assign st' (Compiler rl'') = 0` by metis_tac [] THEN rw []
THEN metis_tac [])
THEN Cases_on `rl' <= tn` THEN Cases_on `rl <= tn` THEN fs [] THEN rw []

THENL [(`tn < rl''` by decide_tac
THEN `count_assign st''' (Compiler tn) = 1` by metis_tac [LESS_SUC_IMP] THEN `count_assign st' (Compiler tn) = 0` by metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ]),
decide_tac,
(`tn < rl''` by decide_tac THEN `count_assign st''' (Compiler tn) = 0` by metis_tac [LESS_SUC_IMP] THEN `count_assign st' (Compiler tn) = 0` by metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ]),
(`tn < rl''` by decide_tac THEN `count_assign st''' (Compiler tn) = 0` by metis_tac [LESS_SUC_IMP] THEN `count_assign st' (Compiler tn) = 1` by metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ])]
THEN fs [NOT_LESS_EQUAL] THEN metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ])

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e'' = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN Cases_on `n = n'` THEN1 (rw [] THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN decide_tac)
THEN metis_tac [CONTAINS_IMPLIES_COUNT_NZERO, CONTAINS_A_SUB, ALL_CO_LOCS_IN_RANGE])

(* Assign *)

THEN1 assign_deref_case
THEN1 assign_deref_case
THEN1 assign_deref_case
THEN1 assign_deref_case

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_assign_def]
THEN Cases_on `rl <= tn` THEN fs [] THEN rw []
THENL [(`tn < n'` by decide_tac
THEN `count_assign st'' (Compiler tn) = 1` by metis_tac [LESS_SUC_IMP]),
(
`count_assign st'' (Compiler tn) = 0` by metis_tac []
)] THEN fs [NOT_LESS_EQUAL] THEN metis_tac [NOT_LESS_EQUAL, GREATER_EQ, NOT_LESS, LESS_OR_EQ, GREATER_EQ])

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN Cases_on `n = n'` THEN1 (rw [] THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN rw []
THEN1 (fs [count_assign_def] THEN `tn < n` by imp_res_tac LESS_EQ THEN `n = rl` by decide_tac THEN rw [] THEN metis_tac [NOT_LESS, GREATER_EQ])
THEN1 (
`n <= tn` by metis_tac [NOT_LESS]
THEN `rl = n` by (fs [GREATER_EQ] THEN imp_res_tac LESS_EQUAL_ANTISYM)
THEN rw []
THEN fs [count_assign_def]
THEN metis_tac []))

THEN fs [count_assign_def, l1_to_il1_def, l1_to_il1_pair_def, LET_DEF] THEN rw [] THEN fs [count_assign_def]
THEN1 (
imp_res_tac COMP_LOC_INCREASING_THM
THEN `count_assign st' (Compiler tn) = 0` by metis_tac []
THEN rw []
THEN fs [GREATER_EQ, NOT_LESS_EQUAL]
THEN imp_res_tac LESS_EQ_TRANS
THEN `~(rl <= tn)` by (`rl > tn` by decide_tac THEN metis_tac [GREATER_EQ, LESS_EQ_TRANS, NOT_LESS])
THEN metis_tac [])
THEN1 (
imp_res_tac COMP_LOC_INCREASING_THM
THEN `count_assign st'' (Compiler tn) = 0` by metis_tac []
THEN rw []
THEN fs [GREATER_EQ, NOT_LESS]
THEN imp_res_tac LESS_EQ_TRANS
THEN `~(tn < rl)` by (`rl <= tn` by decide_tac THEN metis_tac [GREATER_EQ, LESS_EQ_TRANS, NOT_LESS])
THEN metis_tac []))

(* While *)
THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF, contains_def, contains_expr_def, count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN fs [GREATER_EQ] THEN rw [count_assign_def]

THEN Cases_on `rl' <= tn` THEN fs [] THEN rw []

THEN1 (`count_assign st''' (Compiler tn) = 1` by metis_tac []
THEN rw []

THEN `count_assign st'' (Compiler tn) = 0` by metis_tac [NOT_LESS]
THEN rw []
THEN metis_tac [NOT_LESS, LESS_EQ_TRANS])

THEN1 (`count_assign st''' (Compiler tn) = 0` by metis_tac []

THEN Cases_on `rl <= tn` THEN fs [] THEN rw []
THEN1 (`count_assign st'' (Compiler tn) = 1` by metis_tac [NOT_LESS_EQUAL]
THEN rw []
THEN metis_tac [NOT_LESS])
THEN1(
`count_assign st' (Compiler tn) = 1` by metis_tac [NOT_LESS_EQUAL]
THEN rw []
THEN metis_tac [])))

THEN1 (`?st ex rl.l1_to_il1_pair n e = (st, ex, rl)` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st' ex' rl'.l1_to_il1_pair rl e' = (st', ex', rl')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN `?st'' ex'' rl''.l1_to_il1_pair rl' e = (st'', ex'', rl'')` by metis_tac [L1_TO_IL1_TOTAL_THM]
THEN fs [l1_to_il1_def, l1_to_il1_pair_def, LET_DEF] THEN fs [count_assign_def, GREATER_EQ] THEN rw [count_assign_def] THEN imp_res_tac COMP_LOC_INCREASING_THM THEN imp_res_tac NOT_LESS_EQUAL THEN imp_res_tac NOT_LESS THEN fs [GREATER_EQ]
THENL[
metis_tac [],
`~(rl <= tn)` by (`tn < rl` by decide_tac THEN metis_tac [NOT_LESS_EQUAL]) THEN metis_tac [],
`~(rl' <= tn)` by (`tn < rl'` by decide_tac THEN metis_tac [NOT_LESS_EQUAL]) THEN metis_tac [],
`~(tn < rl)` by (`rl <= tn` by decide_tac THEN metis_tac [NOT_LESS]) THEN metis_tac [],
`~(tn < rl')` by (`rl' <= tn` by decide_tac THEN metis_tac [NOT_LESS]) THEN metis_tac [],
metis_tac []]));

val MAX_LOC_MIN_STORE_THM = store_thm("MAX_LOC_MIN_STORE_THM",
``!e s.minimal_store e s ==> !k.k ∈ FDOM s ==> k <= max_loc_l1 e``,
rw [minimal_store_def] THEN
`contains_l1 k e` by fs [] THEN
CCONTR_TAC THEN
fs [NOT_LESS_EQUAL, (fetch "l1" "UNUSED_UPPER_LOCS_THM")]);

val B_USELESS_LOC_EXPR_THM = store_thm("B_USELESS_LOC_EXPR_THM",
``!p r.bs_il1_expr p r ==> !k.~contains_expr k (FST p) ==> !v.bs_il1_expr (FST p, SND p |+ (k, v)) r``,
HO_MATCH_MP_TAC (fetch "il1" "bs_il1_expr_strongind") THEN rw []
THEN1 (Cases_on `r` THEN fs [Once (fetch "il1" "bs_il1_expr_cases")]) THEN TRY (
rw [Once (fetch "il1" "bs_il1_expr_cases")]
THEN fs [contains_expr_def] THEN metis_tac [])
THEN fs [contains_expr_def]
THEN rw [Once (fetch "il1" "bs_il1_expr_cases"), NOT_EQ_FAPPLY]);

val USELESS_LOC_EXPR_THM = store_thm("USELESS_LOC_EXPR_THM",
``!e s r.bs_il1_expr (e, s) r ==> !k.~contains_expr k e ==> !v.bs_il1_expr (e, s |+ (k, v)) r``,
METIS_TAC [B_USELESS_LOC_EXPR_THM, FST, SND]);


val B_USELESS_LOC_THM = store_thm("B_USELESS_LOC_THM",
``!p r s'.bs_il1 p r s' ==> !k.~contains k (FST p) ==> !v.bs_il1 (FST p, SND p |+ (k, v)) r (s' |+ (k, v))``,
HO_MATCH_MP_TAC (fetch "il1" "bs_il1_strongind") THEN rw []
THEN1 (fs [Once (fetch "il1" "bs_il1_cases"), contains_def] THEN METIS_TAC [USELESS_LOC_EXPR_THM])
THEN rw [Once (fetch "il1" "bs_il1_cases")] THEN fs [contains_def, FUPDATE_COMMUTES] THEN METIS_TAC [USELESS_LOC_EXPR_THM]);

val USELESS_LOC_THM = store_thm("USELESS_LOC_THM",
``!e s r s'.bs_il1 (e, s) r s' ==> !k.~contains k e ==> !v.bs_il1 (e, s |+ (k, v)) r (s' |+ (k, v))``,
METIS_TAC [FST, SND, B_USELESS_LOC_THM]);


val translate_store_equiv_def = Define `translate_store_equiv = !e1 e2 v1 v2 s s' s'' s1 s2 sc1 pe1 lc1 sc2 pe2 lc2.
(l1_to_il1_pair 0 e1 = (sc1, pe1, lc1)) ==>
(l1_to_il1_pair lc1 e2 = (sc2, pe2, lc2)) ==>
(big_step (e1, s) v1 s' /\
big_step (e2, s') v2 s'' /\
bs_il1 (sc1, MAP_KEYS User s) IL1_ESkip s1 /\
bs_il1 (sc2, MAP_KEYS User s') IL1_ESkip s2) ==> ?s2'.bs_il1 (sc2, s1) IL1_ESkip s2' /\ equiv s2 s2'`;

val translate_store_val_equiv_def = Define `translate_store_val_equiv =
!s1 s2 s'' v2 s' v1 s lc2 pe2 sc2 e2 lc1 pe1 sc1 e1.
(l1_to_il1_pair 0 e1 = (sc1, pe1, lc1)) ==>
(l1_to_il1_pair lc1 e2 = (sc2, pe2, lc2)) ==>
(big_step (e1, s) v1 s' /\
big_step (e2, s') v2 s'' /\
bs_il1 (IL1_Seq sc1 (IL1_Expr pe1), MAP_KEYS User s) (l1_il1_val v1) s1 /\
bs_il1 (IL1_Seq sc2 (IL1_Expr pe2), MAP_KEYS User s') (l1_il1_val v2) s2) ==>
    ?s2'.bs_il1 (IL1_Seq sc2 (IL1_Expr pe2), s1) (l1_il1_val v2) s2'`;

val IL1_EXPR_BACK_THM = store_thm("IL1_EXPR_BACK_THM",
``!e v s s'.bs_il1 (IL1_Expr e, s) v s' ==> bs_il1_expr (e, s) v /\ (s = s')``,
rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac []);

val IL1_SEQ_BACK_THM = store_thm("IL1_SEQ_BACK_THM",
``!e1 e2 v s s''.bs_il1 (IL1_Seq e1 e2, s) v s'' ==> ?s'.bs_il1 (e1, s) IL1_ESkip s' /\ bs_il1 (e2, s') v s''``,
rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac []);

val IL1_SEQ_ASSOC_THM = store_thm("IL1_SEQ_ASSOC_THM",
``!e1 e2 e3 s v s'.bs_il1 (IL1_Seq e1 (IL1_Seq e2 e3), s) v s' <=> bs_il1 (IL1_Seq (IL1_Seq e1 e2) e3, s) v s'``,
rw [EQ_IMP_THM]
THEN1 (fs [Once (fetch "il1" "bs_il1_cases")] THEN rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac [IL1_SEQ_BACK_THM])
THEN1 (rw [Once (fetch "il1" "bs_il1_cases")] THEN imp_res_tac IL1_SEQ_BACK_THM THEN imp_res_tac IL1_SEQ_BACK_THM THEN metis_tac [(fetch "il1" "bs_il1_cases")]));

val EXPR_PURE_THM = store_thm("EXPR_DOES_NOTHING_THM",
``!st es s s' v.bs_il1 (IL1_Seq st (IL1_Expr es), s) v s' ==> bs_il1 (st, s) IL1_ESkip s'``,
rw [] THEN
`bs_il1 (st, s) IL1_ESkip s' /\ bs_il1 (IL1_Expr es, s') v s'` by ALL_TAC THEN
IMP_RES_TAC IL1_SEQ_BACK_THM THEN
`s'' = s'` by fs [Once (fetch "il1" "bs_il1_cases")] THEN
metis_tac []);

val EXPR_PURE_2_THM = store_thm("EXPR_PURE_2_THM",
``!e s v s'.bs_il1 (IL1_Expr e, s) v s' ==> (s = s')``,
rw [Once (fetch "il1" "bs_il1_cases")]);

val _ = export_theory ();
