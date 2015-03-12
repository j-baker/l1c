open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_il1Theory bigstep_il1Theory;

val _ = new_theory "bigstep_il1_clocked";

val (bs_il1_c_rules, bs_il1_c_ind, bs_il1_c_cases) = Hol_reln `
    (!p.bs_il1_c 0 p NONE) /\

    (*  Expressions *)
    (!cl e v s.
        bs_il1_expr (e, s) v
    ==> bs_il1_c (SUC cl) (IL1_Expr e, s) (SOME (v, s, cl))) /\

    (* Assign *)
    (!cl l e s n.
       (User l ∈ FDOM s /\
        bs_il1_expr (e, s) (IL1_Integer n))
    ==> bs_il1_c (SUC cl) (IL1_Assign (User l) e, s) (SOME (IL1_ESkip, s |+ (User l, n), cl))) /\

    (!cl l e s n.
        bs_il1_expr (e, s) (IL1_Integer n)
    ==> bs_il1_c (SUC cl) (IL1_Assign (Compiler l) e, s) (SOME (IL1_ESkip, s |+ (Compiler l, n), cl))) /\

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
    (!cl cl' e1 e2 e3 v s s'.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_c (SUC cl) (e2, s) (SOME (v, s', cl')))
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) (SOME (v, s', cl'))) /\

    (!cl cl' e1 e2 e3 v s s'.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1_c (SUC cl) (e3, s) (SOME (v, s', cl')))
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) (SOME (v, s', cl'))) /\

    (!cl e1 e2 e3 s.
        (bs_il1_expr (e1, s) (IL1_Boolean F) /\
         bs_il1_c (SUC cl) (e3, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) NONE) /\

    (!cl e1 e2 e3 s.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_c (SUC cl) (e2, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_SIf e1 e2 e3, s) NONE) /\

    (* While *)
    (!cl cl' cl'' e1 e2 s s' s''.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_c cl (e2, s) (SOME (IL1_ESkip, s', cl')) /\
         bs_il1_c cl' (IL1_While e1 e2, s') (SOME (IL1_ESkip, s'', cl'')))
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) (SOME (IL1_ESkip, s'', cl''))) /\

    (!cl e1 e2 s.
        bs_il1_expr (e1, s) (IL1_Boolean F)
    ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) (SOME (IL1_ESkip, s, SUC cl))) /\

    (!cl e1 e2 s.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_c cl (e2, s) NONE)
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) NONE) /\

    (!cl cl' e1 e2 s s'.
        (bs_il1_expr (e1, s) (IL1_Boolean T) /\
         bs_il1_c cl (e2, s) (SOME (IL1_ESkip, s', cl')) /\
         bs_il1_c cl' (IL1_While e1 e2, s') NONE)
     ==> bs_il1_c (SUC cl) (IL1_While e1 e2, s) NONE)`;

val _ = export_theory ();
