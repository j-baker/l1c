open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory il1Theory pred_setTheory pairTheory lcsymtacs prim_recTheory;

val _ = new_theory "l1_to_il1";

val IL1_EXPR_BACK_THM = store_thm("IL1_EXPR_BACK_THM",
``!e v s s'.bs_il1 (IL1_Expr e, s) v s' ==> bs_il1_expr (e, s) v /\ (s = s')``,
rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac []);

val IL1_SEQ_BACK_THM = store_thm("IL1_SEQ_BACK_THM",
``!e1 e2 v s s''.bs_il1 (IL1_Seq e1 e2, s) v s'' ==> ?s'.bs_il1 (e1, s) IL1_ESkip s' /\ bs_il1 (e2, s') v s''``,
rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac []);

val IL1_ASSIGN_BACK_THM = store_thm("IL1_ASSIGN_BACK_THM",
``!l e s s'.bs_il1 (IL1_Assign l e, s) IL1_ESkip s' ==> ?n.bs_il1_expr (e, s) (IL1_Integer n) /\ (s' = (s |+ (l, n)))``,
rw [Once (fetch "il1" "bs_il1_cases")] THEN metis_tac []);

val IL1_SIF_BACK_THM = store_thm("IL1_SIF_BACK_THM",
``!e1 e2 e3 s v s'.bs_il1 (IL1_SIf e1 e2 e3, s) v s' ==> (bs_il1_expr (e1, s) (IL1_Boolean T) /\ bs_il1 (e2, s) v s') \/ (bs_il1_expr (e1, s) (IL1_Boolean F) /\ bs_il1 (e3, s) v s')``,
rw [Once bs_il1_cases] THEN metis_tac []);

val IL1_WHILE_BACK_THM = store_thm("IL1_WHILE_BACK_THM",
``!e1 e2 s s''.bs_il1 (IL1_While e1 e2, s) IL1_ESkip s'' ==> (bs_il1_expr (e1, s) (IL1_Boolean F) /\ (s = s'')) \/ (bs_il1_expr (e1, s) (IL1_Boolean T) /\ ?s'.bs_il1 (e2, s) IL1_ESkip s' /\ bs_il1 (IL1_While e1 e2, s') IL1_ESkip s'')``,
rw [Once bs_il1_cases] THEN metis_tac []);

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
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq sl1 (IL1_While e1' (IL1_Seq sl2 sl1)), IL1_Value IL1_ESkip, lc3)) /\

    (l1_to_il1_pair lc (B_If e1 e2 e3) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in 
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2 in
        let (sl3, e3', lc4) = l1_to_il1_pair lc3 e3
        in
            (IL1_Seq
                (IL1_Seq sl1
                    (IL1_Assign (Compiler lc4) (IL1_EIf e1' (IL1_Value (IL1_Integer 1)) (IL1_Value (IL1_Integer 0)))))
                (IL1_SIf e1' sl2 sl3),
             IL1_EIf (IL1_Geq (IL1_Deref (Compiler lc4)) (IL1_Value (IL1_Integer 1))) e2' e3',
             lc4 + 1)) /\

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

val equiv_def = Define `equiv s1 s2 = !k.(User k ∈ FDOM s1 <=> User k ∈ FDOM s2) /\ (s1 ' (User k) = s2 ' (User k))`;

val EQUIV_REFL_THM = store_thm("EQUIV_REFL_THM",
``!x.equiv x x``,
fs [equiv_def]);

val EQUIV_TRANS_THM = store_thm("EQUIV_TRANS_THM",
``!x y z.equiv x y /\ equiv y z ==> equiv x z``,
rw [equiv_def]);

val EQUIV_APPEND_THM = store_thm("EQUIV_APPEND_THM",
``!e1 e2 k v.equiv e1 e2 ==> equiv (e1 |+ (k, v)) (e2 |+ (k, v))``,
rw [equiv_def] THEN metis_tac [FST, FUPDATE_SAME_APPLY]);

val MAP_APPEND_EQUIV_THM = store_thm("MAP_APPEND_EQUIV_THM",
``!s k v.(MAP_KEYS User s) |+ (User k, v) = (MAP_KEYS User (s |+ (k, v)))``,
rw [] THEN `INJ User (k INSERT FDOM s) UNIV` by rw [INJ_DEF]
THEN metis_tac [MAP_KEYS_FUPDATE])

val EQUIV_SYM_THM = store_thm("EQUIV_SYM_THM",
``!s s'.equiv s s' <=> equiv s' s``,
metis_tac [equiv_def]);

val WHILE_UNWIND_ONCE_THM = store_thm("WHILE_UNWIND_ONCE_THM",
``!e1 s e2 v s'.bs_il1_expr (e1, s) (IL1_Boolean T) ==> (bs_il1 (IL1_While e1 e2, s) IL1_ESkip s' <=> bs_il1 (IL1_Seq e2 (IL1_While e1 e2), s) IL1_ESkip s')``,
rw [EQ_IMP_THM] THEN1
(imp_res_tac IL1_WHILE_BACK_THM
THEN1 (imp_res_tac BS_IL1_EXPR_DETERMINACY THEN rw [])
THEN1 (rw [Once bs_il1_cases] THEN metis_tac []))
THEN1 (rw [Once bs_il1_cases] THEN imp_res_tac IL1_SEQ_BACK_THM THEN metis_tac [IL1_SEQ_BACK_THM])
);



val STORE_L1_IL1_INJ = store_thm("STORE_L1_IL1_INJ",
``!l s. l ∈ FDOM s ==> ((s ' l) = (MAP_KEYS User s) ' (User l))``,
rw [] THEN `FDOM (MAP_KEYS User s) = IMAGE User (FDOM s)` by rw [FDOM_DEF, MAP_KEYS_def, IMAGE_DEF]
THEN `INJ User (FDOM s) UNIV` by rw [INJ_DEF] THEN metis_tac [MAP_KEYS_def]);

val BS_VALUE_THM = store_thm("BS_VALUE_THM",
``!v v' s.bs_il1_expr (IL1_Value v, s) v' ==> (v = v') /\ !s'.bs_il1_expr (IL1_Value v, s') v'``,
Cases_on `v` THEN REPEAT (rw [Once bs_il1_expr_cases]));


val con_store_def = Define `con_store s = MAP_KEYS User s`;

val NOT_CONTAINS_MEANS_UNCHANGED_LEMMA = store_thm("NOT_CONTAINS_MEANS_UNCHANGED_LEMMA",
``!p v s'.bs_il1 p v s' ==> !l.~contains_a l (FST p) ==> (((SND p) ' l) = (s' ' l))``,
ho_match_mp_tac (fetch "il1" "bs_il1_strongind") THEN rw [FST, SND] THEN fs [contains_a_def] THEN metis_tac [FAPPLY_FUPDATE_THM]);

val NOT_CONTAINS_MEANS_UNCHANGED_THM = store_thm("NOT_CONTAINS_MEANS_UNCHANGED_THM",
``!e s v s'.bs_il1 (e, s) v s' ==> !l.~contains_a l e ==> (s ' l = s' ' l)``,
metis_tac [NOT_CONTAINS_MEANS_UNCHANGED_LEMMA, FST, SND]);

val CONTAINS_SIMPED_THM = store_thm("CONTAINS_SIMPED_THM",
``!n e st ex n' l.(l1_to_il1_pair n e = (st, ex, n')) ==> (contains_a l (l1_to_il1 e n) <=> contains_a l st)``,
rw [EQ_IMP_THM]
THEN1 (fs [l1_to_il1_def]
THEN `contains_a l (let (s, te, lc) = (st, ex, n') in IL1_Seq s (IL1_Expr te))` by metis_tac []
THEN fs [LET_DEF, contains_a_def])
THEN rw [l1_to_il1_def] THEN rw [contains_a_def]
);
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

val DOMS_SUBSET_THM_1 = store_thm("DOMS_SUBSET_THM",
``!p v s'.bs_il1 p v s' ==> FDOM (SND p) ⊆ FDOM s'``,
ho_match_mp_tac (fetch "il1" "bs_il1_strongind") THEN rw [FST, SND, SUBSET_DEF]);

val DOMS_SUBSET_THM = store_thm("DOMS_SUBSET_THM",
``!e s v s'.bs_il1 (e, s) v s' ==> FDOM s ⊆ FDOM s'``,
metis_tac [FST, SND, DOMS_SUBSET_THM_1]);

val bs_il1_cases = (fetch "il1" "bs_il1_cases");
val bs_il1_expr_cases = (fetch "il1" "bs_il1_expr_cases");

val NO_INTERMEDIATE_WRITES_SAME_VALUE = store_thm("NO_INTERMEDIATE_WRITES_SAME_VALUE",
``!p v.bs_il1_expr p v ==> !s' s'' l.l ∈ FDOM s'' ==> bs_il1 (IL1_Assign l (FST p), (SND p)) IL1_ESkip s' ==> ((s' ' l) = (s'' ' l)) ==> bs_il1_expr (IL1_Deref l, s'') v``,
Cases_on `p` THEN rw [FST, SND]
THEN fs [Once bs_il1_cases]
THEN rw [Once bs_il1_expr_cases]
THEN metis_tac [(fetch "il1" "BS_IL1_EXPR_DETERMINACY"), FAPPLY_FUPDATE]);

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

val SKIP_TO_SKIP_THM = store_thm("SKIP_TO_SKIP",
``!s.bs_il1_expr (IL1_Value IL1_ESkip, s) IL1_ESkip``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val SKIP_TO_SKIP_2_THM = store_thm("SKIP_TO_SKIP_2_THM",
``!s.bs_il1 (IL1_Expr (IL1_Value IL1_ESkip), s) IL1_ESkip s``,
rw [Once bs_il1_cases, Once bs_il1_expr_cases] THEN metis_tac []);

val ASSIGN_IMPLIES_SKIP_THM = store_thm("ASSIGN_IMPLIES_SKIP_THM",
``!e lc s st ex l lc'.(l1_to_il1_pair lc (B_Assign l e) = (st, ex, lc')) ==> (ex = IL1_Value (IL1_ESkip))``,
rw [l1_to_il1_pair_def]
THEN `?sl1 e1' lc2'.l1_to_il1_pair lc e = (sl1, e1', lc2')` by metis_tac [L1_TO_IL1_TOTAL_THM] 
THEN fs [LET_DEF]);

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
);

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
THEN fs [contains_a_def]));

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

val ALL_CO_LOCS_IN_RANGE = store_thm("ALL_CO_LOCS_IN_RANGE",
``!e n st ex n' tn.(l1_to_il1_pair n e = (st, ex, n')) ==> (contains (Compiler tn) (l1_to_il1 e n) <=> (tn >= n) /\ (tn < n'))``,
metis_tac [EQ_IMP_THM, ALL_CO_LOCS_IN_RANGE_BA, ALL_CO_LOCS_IN_RANGE_FOR, CONTAINS_A_SUB]);

val UNCHANGED_LOC_SIMP_THM = store_thm("UNCHANGED_LOC_SIMP_THM",
``!n e st ex n' tn.(l1_to_il1_pair n e = (st,ex,n')) ⇒
     (contains_a (Compiler tn) st ⇔ tn ≥ n ∧ tn < n')``,
rw [EQ_IMP_THM] THEN metis_tac [CONTAINS_SIMPED_THM, ALL_CO_LOCS_IN_RANGE_BA, (fetch "il1" "CONTAINS_A_SUB"), ALL_CO_LOCS_IN_RANGE_FOR]);

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
