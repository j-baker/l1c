open HolKernel boolLib bossLib wordsTheory wordsLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory;

val _ = new_theory "il1";

val _ = type_abbrev("loc", ``:num``);

val _ = type_abbrev("int", ``:word16``);

val _ = type_abbrev("state", ``:loc |-> int``);

val _ = type_abbrev("pred", ``:state -> bool``);

val _ = Hol_datatype `il1_value = IL1_ESkip
                                | IL1_Integer of int
				| IL1_Boolean of bool`;

val _ = Hol_datatype `il1_expr = IL1_Value of il1_value
                               | IL1_Plus of il1_expr => il1_expr
                               | IL1_Geq of il1_expr => il1_expr
                               | IL1_Deref of loc
                               | IL1_EIf of il1_expr => il1_expr => il1_expr`;

val _ = Hol_datatype `il1_stm = IL1_Expr of il1_expr
                              | IL1_Assign of loc => il1_expr
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

val max_loc_expr_def = Define `
    (max_loc_expr (IL1_Value v) = 0) /\
    (max_loc_expr (IL1_Plus e1 e2) = MAX (max_loc_expr e1) (max_loc_expr e2)) /\
    (max_loc_expr (IL1_Geq e1 e2) = MAX (max_loc_expr e1) (max_loc_expr e2)) /\
    (max_loc_expr (IL1_Deref l) = l) /\
    (max_loc_expr (IL1_EIf e1 e2 e3) = MAX (MAX (max_loc_expr e1) (max_loc_expr e2)) (max_loc_expr e3))`;

val max_loc_def = Define `
    (max_loc (IL1_Expr e) = max_loc_expr e) /\
    (max_loc (IL1_Assign l2 e) = MAX l2 (max_loc_expr e)) /\
    (max_loc (IL1_Seq e1 e2) = MAX (max_loc e1) (max_loc e2)) /\
    (max_loc (IL1_SIf e1 e2 e3) = MAX (MAX (max_loc_expr e1) (max_loc e2)) (max_loc e3)) /\
    (max_loc (IL1_While e1 e2) = MAX (max_loc_expr e1) (max_loc e2))`;


val UNUSED_UPPER_LOCS_EXPR_THM = store_thm(
    "UNUSED_UPPER_LOCS_EXPR_THM",
    ``!e n.max_loc_expr e < n ==> ~contains_expr n e``,
    Induct_on `e` THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss ()) [MAX_DEF]);

val UNUSED_UPPER_LOCS_THM = store_thm(
    "UNUSED_UPPER_LOCS_THM",
    ``!e n.max_loc e < n==> ~contains n e``,
    Induct_on `e` THEN EVAL_TAC
    THEN FULL_SIMP_TAC (srw_ss ()) [MAX_DEF, UNUSED_UPPER_LOCS_EXPR_THM]);

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

    (* EIf *)
    (!e1 e2 e3 s v.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_expr (e2, s) v)
     ==> bs_il1_expr (IL1_EIf e1 e2 e3, s) v) /\

    (!e1 e2 e3 s.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1_expr (e3, s) v)
     ==> bs_il1_expr (IL1_EIf e1 e2 e3, s) v)`;

val (bs_il1_rules, bs_il1_induction, bs_il1_ecases) = Hol_reln `
    (*  Expressions *)
    (!e v s.
        bs_il1_expr (e, s) v
    ==> bs_il1 (IL1_Expr e, s) v s) /\

    (* Assign *)
    (!l e s n.
       (l ∈ FDOM s /\
        bs_il1_expr (e, s) (IL1_Integer n))
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

val l1_to_il1_pair_def = Define `
    (l1_to_il1_pair lc (B_Value (B_N n)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Integer n), lc)) /\
    (l1_to_il1_pair lc (B_Value (B_B b)) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value (IL1_Boolean b), lc)) /\
    (l1_to_il1_pair lc (B_Value B_Skip) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Value IL1_ESkip, lc)) /\
    (l1_to_il1_pair lc (B_Deref l) = (IL1_Expr (IL1_Value IL1_ESkip), IL1_Deref l, lc)) /\

    (l1_to_il1_pair lc (B_Assign l e) =
        let (sl, e', lc2) = l1_to_il1_pair lc e
        in
            (IL1_Seq sl (IL1_Assign l e'), IL1_Value IL1_ESkip,lc2)) /\

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
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (lc3 + 1) e1')) sl2, IL1_Plus (IL1_Deref (lc3 + 1)) e2', lc3 + 1)) /\ 

    (l1_to_il1_pair lc (B_Geq e1 e2) =
        let (sl1, e1', lc2) = l1_to_il1_pair lc e1 in
        let (sl2, e2', lc3) = l1_to_il1_pair lc2 e2
        in
            (IL1_Seq (IL1_Seq sl1 (IL1_Assign (lc3 + 1) e1')) sl2, IL1_Geq (IL1_Deref (lc3 + 1)) e2', lc3 + 1))
`;

val l1_to_il1_def = Define `l1_to_il1 e = let (s, te, lc) = l1_to_il1_pair (max_loc_l1 e) e in IL1_Seq s (IL1_Expr te)`;


val _ = export_theory ();
