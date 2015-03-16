open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory bigstep_l1Theory pred_setTheory pairTheory lcsymtacs integerTheory ast_il1Theory;

val _ = new_theory "bigstep_il1";

val (bs_il1_expr_rules, bs_il1_expr_ind, bs_il1_expr_cases) = Hol_reln `
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

    (!e1 e2 e3 s v.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1_expr (e3, s) v)
     ==> bs_il1_expr (IL1_EIf e1 e2 e3, s) v)`;

val (bs_il1_rules, bs_il1_ind, bs_il1_cases) = Hol_reln `
    (*  Expressions *)
    (!e v s.
        bs_il1_expr (e, s) v
    ==> bs_il1 (IL1_Expr e, s) v s) /\

    (* Assign *)
    (!l e s n.
       (User l ∈ FDOM s /\
        bs_il1_expr (e, s) (IL1_Integer n))
    ==> bs_il1 (IL1_Assign (User l) e, s) IL1_ESkip (s |+ (User l, n))) /\

    (!l e s n.
        bs_il1_expr (e, s) (IL1_Integer n)
    ==> bs_il1 (IL1_Assign (Compiler l) e, s) IL1_ESkip (s |+ (Compiler l, n))) /\

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
       (bs_il1_expr (e1, s) (IL1_Boolean F))
    ==> bs_il1 (IL1_While e1 e2, s) IL1_ESkip s) /\

    (!e s v s'.
        bs_il1 (e, s) v s' ==> bs_il1 (IL1_Tick e, s) v s')
`;

val _ = export_theory ();
