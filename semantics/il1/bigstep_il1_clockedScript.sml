open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_il1Theory bigstep_il1Theory;


val _ = new_theory "bigstep_il1_clocked";


val (bs_il1_c_expr_rules, bs_il1_c_expr_ind, bs_il1_c_expr_cases) = Hol_reln `
    (!p.bs_il1_c_expr 0 p NONE) /\

    (* Values *)
    (!cl v s.bs_il1_c_expr (SUC cl) (IL1_Value v, s) (SOME (v, (SUC cl)))) /\

    (* Plus *)
    (!cl cl' cl'' e1 e2 n1 n2 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Integer n1, cl')) /\
         bs_il1_c_expr cl' (e2, s) (SOME (IL1_Integer n2, cl'')))
     ==> bs_il1_c_expr (SUC cl) (IL1_Plus e1 e2, s) (SOME (IL1_Integer (n1 + n2), cl''))) /\

    (!cl e1 e2 s.
         bs_il1_c_expr (SUC cl) (e1, s) NONE
     ==> bs_il1_c_expr (SUC cl) (IL1_Plus e1 e2, s) NONE) /\

    (!cl cl' e1 e2 n1 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Integer n1, cl')) /\
         bs_il1_c_expr cl' (e2, s) NONE)
     ==> bs_il1_c_expr (SUC cl) (IL1_Plus e1 e2, s) NONE) /\

    (* Geq *)
    (!cl cl' cl'' e1 e2 n1 n2 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Integer n1, cl')) /\
         bs_il1_c_expr cl' (e2, s) (SOME (IL1_Integer n2, cl'')))
     ==> bs_il1_c_expr (SUC cl) (IL1_Geq e1 e2, s) (SOME (IL1_Boolean (n1 >= n2), cl''))) /\

    (!cl e1 e2 s.
         bs_il1_c_expr (SUC cl) (e1, s) NONE
     ==> bs_il1_c_expr (SUC cl) (IL1_Geq e1 e2, s) NONE) /\

    (!cl cl' e1 e2 n1 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Integer n1, cl')) /\
         bs_il1_c_expr cl' (e2, s) NONE)
     ==> bs_il1_c_expr (SUC cl) (IL1_Geq e1 e2, s) NONE) /\

    (* Deref *)
    (!cl l s.
        l ∈ FDOM s
    ==> bs_il1_c_expr (SUC cl) (IL1_Deref l, s) (SOME (IL1_Integer (s ' l), (SUC cl)))) /\

    (* EIf *)
    (!cl cl' cl'' e1 e2 e3 s v.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c_expr cl' (e2, s) (SOME (v, cl'')))
     ==> bs_il1_c_expr (SUC cl) (IL1_EIf e1 e2 e3, s) (SOME (v, cl''))) /\

    (!cl cl' cl'' e1 e2 e3 s v.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean F, cl')) /\
         bs_il1_c_expr cl' (e3, s) (SOME (v, cl'')))
     ==> bs_il1_c_expr (SUC cl) (IL1_EIf e1 e2 e3, s) (SOME (v, cl''))) /\

    (!cl e1 e2 e3 s.
         bs_il1_c_expr (SUC cl) (e1, s) NONE
     ==> bs_il1_c_expr (SUC cl) (IL1_EIf e1 e2 e3, s) NONE) /\

    (!cl cl' e1 e2 e3 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c_expr cl' (e2, s) NONE)
     ==> bs_il1_c_expr (SUC cl) (IL1_EIf e1 e2 e3, s) NONE) /\

    (!cl cl' e1 e2 e3 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean F, cl')) /\
         bs_il1_c_expr cl' (e3, s) NONE)
     ==> bs_il1_c_expr (SUC cl) (IL1_EIf e1 e2 e3, s) NONE)`;

val (bs_il1_c_rules, bs_il1_c_ind, bs_il1_c_cases) = Hol_reln `
    (!p.bs_il1_c 0 p NONE) /\

    (*  Expressions *)
    (!cl cl' e v s.
        bs_il1_c_expr (SUC cl) (e, s) (SOME (v, cl'))
    ==> bs_il1_c (SUC cl) (IL1_Expr e, s) (SOME (v, s, cl'))) /\

    (!cl e s.
        bs_il1_c_expr (SUC cl) (e, s) NONE
    ==> bs_il1_c (SUC cl) (IL1_Expr e, s) NONE) /\

    (* Assign *)
    (!cl cl' l e s n.
       (User l ∈ FDOM s /\
        bs_il1_c_expr (SUC cl) (e, s) (SOME (IL1_Integer n, cl')))
    ==> bs_il1_c (SUC cl) (IL1_Assign (User l) e, s) (SOME (IL1_ESkip, s |+ (User l, n), cl'))) /\

    (!cl cl' l e s n.
        bs_il1_c_expr (SUC cl) (e, s) (SOME (IL1_Integer n, cl'))
    ==> bs_il1_c (SUC cl) (IL1_Assign (Compiler l) e, s) (SOME (IL1_ESkip, s |+ (Compiler l, n), cl'))) /\

    (!cl l e s.
       (User l ∈ FDOM s /\
        bs_il1_c_expr (SUC cl) (e, s) NONE)
    ==> bs_il1_c (SUC cl) (IL1_Assign (User l) e, s) NONE) /\

    (!cl l e s.
        bs_il1_c_expr (SUC cl) (e, s) NONE
    ==> bs_il1_c (SUC cl) (IL1_Assign (Compiler l) e, s) NONE) /\

    (* Seq *)
    (!cl cl' cl'' e1 e2 v s s' s''.
        (bs_il1_c (SUC cl) (e1, s) (SOME (IL1_ESkip, s', cl')) /\
         bs_il1_c cl' (e2, s') (SOME (v, s'', cl'')))
     ==> bs_il1_c (SUC cl) (IL1_Seq e1 e2, s) (SOME (v, s'', cl''))) /\

    (!cl e1 e2 s.
         bs_il1_c (SUC cl) (e1, s) NONE
     ==> bs_il1_c (SUC cl) (IL1_Seq e1 e2, s) NONE) /\

    (!cl cl' e1 e2 s s'.
        (bs_il1_c (SUC cl) (e1, s) (SOME (IL1_ESkip, s', cl')) /\
         bs_il1_c cl' (e2, s') NONE)
     ==> bs_il1_c (SUC cl) (IL1_Seq e1 e2, s) NONE) /\

    (* SIf *)
    (!cl cl' cl'' e1 e2 e3 v s s'.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c cl' (e2, s) (SOME (v, s', cl'')))
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) (SOME (v, s', cl''))) /\

    (!cl cl' cl'' e1 e2 e3 v s s'.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean F, cl')) /\
         bs_il1_c cl' (e3, s) (SOME (v, s', cl'')))
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) (SOME (v, s', cl''))) /\

    (!cl e1 e2 e3 s.
         bs_il1_c_expr (SUC cl) (e1, s) NONE
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) NONE) /\

    (!cl cl' e1 e2 e3 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean F, cl')) /\
         bs_il1_c cl' (e3, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) NONE) /\

    (!cl cl' e1 e2 e3 s.
        (bs_il1_c_expr (SUC cl) (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c cl' (e2, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) NONE) /\

    (* While *)
    (!cl cl' cl'' cl''' e1 e2 s s' s''.
        (bs_il1_c_expr cl (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c cl' (e2, s) (SOME (IL1_ESkip, s', cl'')) /\
         bs_il1_c cl'' (IL1_While e1 e2, s') (SOME (IL1_ESkip, s'', cl''')))
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) (SOME (IL1_ESkip, s'', cl'''))) /\

    (!cl cl' e1 e2 s.
       (bs_il1_c_expr cl (e1, s) (SOME (IL1_Boolean F, cl')))
    ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) (SOME (IL1_ESkip, s, cl'))) /\

    (!cl cl' e1 e2 s.
        (bs_il1_c_expr cl (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c cl' (e2, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) NONE) /\

    (!cl cl' cl'' e1 e2 s s'.
        (bs_il1_c_expr cl (e1, s) (SOME (IL1_Boolean T, cl')) /\
         bs_il1_c cl' (e2, s) (SOME (IL1_ESkip, s', cl'')) /\
         bs_il1_c cl'' (IL1_While e1 e2, s') NONE)
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) NONE) /\

    (!cl e1 e2 s.
       (bs_il1_c_expr cl (e1, s) NONE)
    ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) NONE)`;

val _ = export_theory ();
