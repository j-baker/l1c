open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory pred_setTheory pairTheory lcsymtacs;

val _ = new_theory "il1";

val _ = Hol_datatype `il1_loc = User of loc
                              | Compiler of loc`; 

val _ = Hol_datatype `il1_value = IL1_ESkip
                                | IL1_Integer of int
				| IL1_Boolean of bool`;

val _ = Hol_datatype `il1_expr = IL1_Value of il1_value
                               | IL1_Plus of il1_expr => il1_expr
                               | IL1_Geq of il1_expr => il1_expr
                               | IL1_Deref of il1_loc
                               | IL1_EIf of il1_expr => il1_expr => il1_expr`;

val _ = Hol_datatype `il1_stm = IL1_Expr of il1_expr
                              | IL1_Assign of il1_loc => il1_expr
                              | IL1_Seq of il1_stm => il1_stm
                              | IL1_SIf of il1_expr => il1_stm => il1_stm
                              | IL1_While of il1_expr => il1_stm`;

val contains_expr_def = Define `
    (contains_expr l (IL1_Value v) = F) /\
    (contains_expr l (IL1_Plus e1 e2) = contains_expr l e1 \/ contains_expr l e2) /\
    (contains_expr l (IL1_Geq e1 e2) = contains_expr l e1 \/ contains_expr l e2) /\
    (contains_expr l1 (IL1_Deref l2) = (l1 = l2)) /\
    (contains_expr l (IL1_EIf e1 e2 e3) = contains_expr l e1 \/ contains_expr l e2 \/ contains_expr l e3)`;

val contains_def = Define `
    (contains l (IL1_Expr e) = contains_expr l e) /\
    (contains l1 (IL1_Assign l2 e) = (l1 = l2) \/ contains_expr l1 e) /\
    (contains l (IL1_Seq e1 e2) = contains l e1 \/ contains l e2) /\
    (contains l (IL1_SIf e1 e2 e3) = contains_expr l e1 \/ contains l e2 \/ contains l e3) /\
    (contains l (IL1_While e1 e2) = contains_expr l e1 \/ contains l e2)`;

val contains_a_def = Define `
    (contains_a l (IL1_Expr _) = F) /\
    (contains_a l1 (IL1_Assign l2 e) = (l1 = l2)) /\
    (contains_a l (IL1_Seq e1 e2) = contains_a l e1 \/ contains_a l e2) /\
    (contains_a l (IL1_SIf _ e2 e3) = contains_a l e2 \/ contains_a l e3) /\
    (contains_a l (IL1_While _ e2) = contains_a l e2)`;


val (bs_il1_expr_rules, bs_il1_expr_induction, bs_il1_expr_ecases) = Hol_reln `
    (* Values *)
    (!v s.bs_il1_expr (IL1_Value v, s) v) /\

    (* Plus *)
    (!e1 e2 n1 n2 s.
        (bs_il1_expr (e1, s) (IL1_Integer n1) /\
         bs_il1_expr (e2, s) (IL1_Integer n2))
     ==> bs_il1_expr (IL1_Plus e1 e2, s) (IL1_Integer (n1 + n2))) /\

    (* Geq *)
    (!e1 e2 n1 n2 s.
        (bs_il1_expr (e1, s) (IL1_Integer n1) /\
         bs_il1_expr (e2, s) (IL1_Integer n2))
     ==> bs_il1_expr (IL1_Geq e1 e2, s) (IL1_Boolean (n1 >= n2))) /\

    (* Deref *)
    (!l s.
        l ∈ FDOM s
    ==> bs_il1_expr (IL1_Deref l, s) (IL1_Integer (s ' l))) /\

    (!l s.
        l ∉ FDOM s
    ==> bs_il1_expr (IL1_Deref l, s) (IL1_Integer 0)) /\

    (* EIf *)
    (!e1 e2 e3 s v.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_expr (e2, s) v)
     ==> bs_il1_expr (IL1_EIf e1 e2 e3, s) v) /\

    (!e1 e2 e3 s v.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1_expr (e3, s) v)
     ==> bs_il1_expr (IL1_EIf e1 e2 e3, s) v)`;

val bs_il1_expr_sinduction = derive_strong_induction(bs_il1_expr_rules, bs_il1_expr_induction);

val BS_IL1_EXPR_PLUS_BACK_THM = store_thm("BS_IL1_EXPR_PLUS_BACK_THM",
``!e1 e2 s v.bs_il1_expr (IL1_Plus e1 e2, s) v ==> ?n1 n2.bs_il1_expr (e1, s) (IL1_Integer n1) /\ bs_il1_expr (e2, s) (IL1_Integer n2) /\ (v = IL1_Integer (n1 + n2))``,
rw [Once bs_il1_expr_ecases] THEN metis_tac []);

val BS_IL1_EXPR_GEQ_BACK_THM = store_thm("BS_IL1_EXPR_GEQ_BACK_THM",
``!e1 e2 s v.bs_il1_expr (IL1_Geq e1 e2, s) v ==> ?n1 n2.bs_il1_expr (e1, s) (IL1_Integer n1) /\ bs_il1_expr (e2, s) (IL1_Integer n2) /\ (v = IL1_Boolean (n1 >= n2))``,
rw [Once bs_il1_expr_ecases] THEN metis_tac []);

val BS_IL1_EXPR_DEREF_BACK_THM = store_thm("BS_IL1_EXPR_DEREF_BACK_THM",
``!l s v.bs_il1_expr (IL1_Deref l, s) v ==> (l ∈ FDOM s /\ (v = IL1_Integer (s ' l))) \/ (l ∉ FDOM s /\ (v = IL1_Integer 0))``,
rw [Once bs_il1_expr_ecases] THEN metis_tac []);

val BS_IL1_EXPR_EIF_BACK_THM = store_thm("BS_IL1_EXPR_EIF_BACK_THM",
``!e1 e2 e3 s v.bs_il1_expr (IL1_EIf e1 e2 e3, s) v ==> (bs_il1_expr (e1, s) (IL1_Boolean T) /\ bs_il1_expr (e2, s) v) \/ (bs_il1_expr (e1, s) (IL1_Boolean F) /\ bs_il1_expr (e3, s) v)``,
rw [Once bs_il1_expr_ecases] THEN metis_tac []);

val BS_IL1_EXPR_DETERMINACY = store_thm("BS_IL1_EXPR_DETERMINACY",
``!p v1.bs_il1_expr p v1 ==> !v2.bs_il1_expr p v2 ==> (v1 = v2)``,
ho_match_mp_tac bs_il1_expr_sinduction THEN rw []
THEN1 (Cases_on `v1` THEN Cases_on `v2` THEN fs [Once bs_il1_expr_ecases])
THEN1 (imp_res_tac BS_IL1_EXPR_PLUS_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_GEQ_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_DEREF_BACK_THM THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_DEREF_BACK_THM THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw [])
THEN1 (imp_res_tac BS_IL1_EXPR_EIF_BACK_THM THEN res_tac THEN rw []));

val (bs_il1_rules, bs_il1_induction, bs_il1_ecases) = Hol_reln `
    (*  Expressions *)
    (!e v s.
        bs_il1_expr (e, s) v
    ==> bs_il1 (IL1_Expr e, s) v s) /\

    (* Assign *)
    (!l e s n.
        bs_il1_expr (e, s) (IL1_Integer n)
    ==> bs_il1 (IL1_Assign l e, s) IL1_ESkip (s |+ (l, n))) /\

    (* Seq *)
    (!e1 e2 v s s' s''.
        (bs_il1 (e1, s) IL1_ESkip s' /\
         bs_il1 (e2, s') v s'')
     ==> bs_il1 (IL1_Seq e1 e2, s) v s'') /\

    (* SIf *)
    (!e1 e2 e3 v s s'.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1 (e2, s) v s')
     ==> bs_il1 (IL1_SIf e1 e2 e3, s) v s') /\

    (!e1 e2 e3 v s s'.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1 (e3, s) v s')
     ==> bs_il1 (IL1_SIf e1 e2 e3, s) v s') /\

    (* While *)
    (!e1 e2 s s' s''.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1 (e2, s) IL1_ESkip s' /\
         bs_il1 (IL1_While e1 e2, s') IL1_ESkip s'')
     ==> bs_il1 (IL1_While e1 e2, s) IL1_ESkip s'') /\

    (!e1 e2 s.
        bs_il1_expr (e1, s) (IL1_Boolean F)
    ==> bs_il1 (IL1_While e1 e2, s) IL1_ESkip s)`;

val bs_il1_sinduction = derive_strong_induction(bs_il1_rules, bs_il1_induction);


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
THEN ((`?sl1 e1' n''.l1_to_il1_pair n' e = (sl1, e1', n'')` by metis_tac [L1_TO_IL1_TOTAL_THM]) THEN fs [l1_to_il1_pair_def, LET_DEF]));

Induct_on `e` THEN rw []
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

val MAX_LOC_MIN_STORE_THM = store_thm("MAX_LOC_MIN_STORE_THM",
``!e s.minimal_store e s ==> !k.k ∈ FDOM s ==> k <= max_loc_l1 e``,
rw [minimal_store_def] THEN
`contains_l1 k e` by fs [] THEN
CCONTR_TAC THEN
fs [NOT_LESS_EQUAL, (fetch "l1" "UNUSED_UPPER_LOCS_THM")]);

val B_USELESS_LOC_EXPR_THM = store_thm("B_USELESS_LOC_EXPR_THM",
``!p r.bs_il1_expr p r ==> !k.~contains_expr k (FST p) ==> !v.bs_il1_expr (FST p, SND p |+ (k, v)) r``,
HO_MATCH_MP_TAC bs_il1_expr_sinduction THEN rw []
THEN1 (Cases_on `r` THEN fs [Once bs_il1_expr_ecases]) THEN TRY (
rw [Once bs_il1_expr_ecases]
THEN fs [contains_expr_def] THEN metis_tac [])
THEN fs [contains_expr_def]
THEN rw [Once bs_il1_expr_ecases, NOT_EQ_FAPPLY]);

val USELESS_LOC_EXPR_THM = store_thm("USELESS_LOC_EXPR_THM",
``!e s r.bs_il1_expr (e, s) r ==> !k.~contains_expr k e ==> !v.bs_il1_expr (e, s |+ (k, v)) r``,
METIS_TAC [B_USELESS_LOC_EXPR_THM, FST, SND]);


val B_USELESS_LOC_THM = store_thm("B_USELESS_LOC_THM",
``!p r s'.bs_il1 p r s' ==> !k.~contains k (FST p) ==> !v.bs_il1 (FST p, SND p |+ (k, v)) r (s' |+ (k, v))``,
HO_MATCH_MP_TAC bs_il1_sinduction THEN rw []
THEN1 (fs [Once bs_il1_ecases, contains_def] THEN METIS_TAC [USELESS_LOC_EXPR_THM])
THEN rw [Once bs_il1_ecases] THEN fs [contains_def, FUPDATE_COMMUTES] THEN METIS_TAC [USELESS_LOC_EXPR_THM]);

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


val L1_TO_IL1_TOTAL_THM = store_thm("L1_TO_IL1_TOTAL_THM",
``!e n.?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)``,
Induct_on `e` THEN rw [l1_to_il1_pair_def]
THEN TRY (Cases_on `b` THEN EVAL_TAC THEN metis_tac []) THEN
TRY (`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
rw [] THEN `?sl e''' lc''.l1_to_il1_pair lc' e'' = (sl, e''', lc'')` by METIS_TAC [] THEN rw [])
THEN `?sl e' lc.l1_to_il1_pair n' e = (sl, e', lc)` by metis_tac [] THEN rw []);

val IL1_EXPR_BACK_THM = store_thm("IL1_EXPR_BACK_THM",
``!e v s s'.bs_il1 (IL1_Expr e, s) v s' ==> bs_il1_expr (e, s) v /\ (s = s')``,
rw [Once bs_il1_ecases] THEN metis_tac []);

val IL1_SEQ_BACK_THM = store_thm("IL1_SEQ_BACK_THM",
``!e1 e2 v s s''.bs_il1 (IL1_Seq e1 e2, s) v s'' ==> ?s'.bs_il1 (e1, s) IL1_ESkip s' /\ bs_il1 (e2, s') v s''``,
rw [Once bs_il1_ecases] THEN metis_tac []);

val IL1_SEQ_ASSOC_THM = store_thm("IL1_SEQ_ASSOC_THM",
``!e1 e2 e3 s v s'.bs_il1 (IL1_Seq e1 (IL1_Seq e2 e3), s) v s' <=> bs_il1 (IL1_Seq (IL1_Seq e1 e2) e3, s) v s'``,
rw [EQ_IMP_THM]
THEN1 (fs [Once bs_il1_ecases] THEN rw [Once bs_il1_ecases] THEN metis_tac [IL1_SEQ_BACK_THM])
THEN1 (rw [Once bs_il1_ecases] THEN imp_res_tac IL1_SEQ_BACK_THM THEN imp_res_tac IL1_SEQ_BACK_THM THEN metis_tac [bs_il1_ecases]));

val EXPR_PURE_THM = store_thm("EXPR_DOES_NOTHING_THM",
``!st es s s' v.bs_il1 (IL1_Seq st (IL1_Expr es), s) v s' ==> bs_il1 (st, s) IL1_ESkip s'``,
rw [] THEN
`bs_il1 (st, s) IL1_ESkip s' /\ bs_il1 (IL1_Expr es, s') v s'` by ALL_TAC THEN
IMP_RES_TAC IL1_SEQ_BACK_THM THEN
`s'' = s'` by fs [Once bs_il1_ecases] THEN
metis_tac []);

val EXPR_PURE_2_THM = store_thm("EXPR_PURE_2_THM",
``!e s v s'.bs_il1 (IL1_Expr e, s) v s' ==> (s = s')``,
rw [Once bs_il1_ecases]);

!p v s'.big_step p v s' ==> conv_ind ==> translate_store_equiv ==> translate_store_val_equiv ==> ?s1.(bs_il1 (l1_to_il1 (FST p) 0, MAP_KEYS User (SND p)) (l1_il1_val v) s1)
HO_MATCH_MP_TAC (fetch "l1" "big_step_strongind") THEN
rw [FST, SND, l1_il1_val_def] THEN
rw [l1_to_il1_def, l1_to_il1_pair_def, l1_il1_val_def]
THEN fs []

(* Value case *)
THEN1 (Cases_on `v` THEN
rw [l1_to_il1_pair_def, l1_il1_val_def] THEN
METIS_TAC [l1_to_il1_pair_def, l1_il1_val_def, bs_il1_ecases, bs_il1_expr_ecases])
(* End value case *)

(* Seq case *)
`?sl1 e1' lc2.l1_to_il1_pair 0 e1 = (sl1, e1', lc2)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
`?sl2 e2' lc3.l1_to_il1_pair lc2 e2 = (sl2, e2', lc3)` by metis_tac [L1_TO_IL1_TOTAL_THM] THEN
rw []
THEN `l1_to_il1 e1 0 = IL1_Seq sl1 (IL1_Expr e1')` by rw [l1_to_il1_def]
THEN `?s2.bs_il1 (l1_to_il1 e2 lc2, MAP_KEYS User s') (l1_il1_val v) s2` by (fs [conv_ind_def] THEN metis_tac [FST, SND])
THEN `l1_to_il1 e2 lc2 = IL1_Seq sl2 (IL1_Expr e2')` by rw [l1_to_il1_def]
THEN fs []
THEN `?s2'.bs_il1 (sl2, s1) IL1_ESkip s2' /\ equiv s2 s2'` by metis_tac [translate_store_equiv_def, EXPR_PURE_THM]
THEN rw [Once bs_il1_ecases]
THEN rw [Once bs_il1_ecases]
THEN `?s2'.bs_il1 (IL1_Seq sl2 (IL1_Expr e2'), s1) (l1_il1_val v) s2'` by metis_tac [l1_il1_val_def, translate_store_val_equiv_def]
THEN `?s'.bs_il1 (sl2, s1) IL1_ESkip s' /\ bs_il1 (IL1_Expr e2', s') (l1_il1_val v) s2''` by metis_tac [IL1_SEQ_BACK_THM]
THEN `s''' = s2''` by metis_tac [EXPR_PURE_2_THM]
THEN rw []
THEN metis_tac [EXPR_PURE_THM]
(* End seq case *)
val _ = export_theory ();
