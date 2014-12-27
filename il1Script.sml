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
            (IL1_Seq sl1 (IL1_SIf e1' sl2 sl3), IL1_EIf e1' e2' e3', lc4)) /\

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


val L1_TO_IL1_TOTAL_THM = store_thm("L1_TO_IL1_TOTAL_THM",
``!e n.?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)``,
Induct_on `e` THEN rw [l1_to_il1_pair_def]
THEN TRY (Cases_on `b` THEN EVAL_TAC THEN metis_tac []) THEN
TRY (`?sl e' lc.l1_to_il1_pair n e = (sl, e', lc)` by METIS_TAC [] THEN
`?sl e'' lc'.l1_to_il1_pair lc e' = (sl, e'', lc')` by METIS_TAC [] THEN
rw [] THEN `?sl e''' lc''.l1_to_il1_pair lc' e'' = (sl, e''', lc'')` by METIS_TAC [] THEN rw [])
THEN `?sl e' lc.l1_to_il1_pair n' e = (sl, e', lc)` by metis_tac [] THEN rw []);

!p v s'.big_step p v s' ==> ?s1.(bs_il1 (l1_to_il1 (pair_first p), MAP_KEYS User (pair_second p)) (l1_il1_val v) s1)
val IL1_SEQ_BACK_THM = store_thm("IL1_SEQ_BACK_THM",
``!e1 e2 v s s''.bs_il1 (IL1_Seq e1 e2, s) v s'' ==> ?s'.bs_il1 (e1, s) IL1_ESkip s' /\ bs_il1 (e2, s') v s''``,
rw [Once bs_il1_ecases] THEN metis_tac []);


HO_MATCH_MP_TAC (fetch "l1" "big_step_strongind")
THEN RW_TAC (srw_ss ()) [pair_first_def, pair_second_def, l1_il1_val_def]


val _ = export_theory ();
