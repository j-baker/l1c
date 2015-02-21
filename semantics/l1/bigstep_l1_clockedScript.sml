open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory bigstep_l1Theory;


val _ = new_theory "bigstep_l1_clocked";

val (bs_l1_c_rules, bs_l1_c_ind, bs_l1_c_cases) = Hol_reln `
    (* Fail *)
    (!p.bs_l1_c 0 p NONE) /\

    (* Values *)
    (!cl v s.bs_l1_c (SUC cl) (L1_Value v, s) (SOME (v, s, cl))) /\

    (* Plus *)
    (!cl cl' cl'' e1 e2 n1 n2 s s' s''.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Int n1, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (L1_Int n2, s'', cl''))
     ==> bs_l1_c (SUC cl) (L1_Plus e1 e2, s) (SOME (L1_Int (n1 + n2), s'', cl'')))) /\

    (!cl cl' e1 e2 n1 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Int n1, s', cl')) /\
   bs_l1_c cl' (e2, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_Plus e1 e2, s) NONE) /\

    (!cl e1 e2 s.
         bs_l1_c (SUC cl) (e1, s) NONE
     ==> bs_l1_c (SUC cl) (L1_Plus e1 e2, s) NONE) /\

    (* Geq *)
    (!cl cl' cl'' e1 e2 n1 n2 s s' s''.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Int n1, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (L1_Int n2, s'', cl''))
     ==> bs_l1_c (SUC cl) (L1_Geq e1 e2, s) (SOME (L1_Bool (n1 >= n2), s'', cl'')))) /\

    (!cl cl' e1 e2 n1 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Int n1, s', cl')) /\
   bs_l1_c cl' (e2, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_Geq e1 e2, s) NONE) /\

    (!cl e1 e2 s.
         bs_l1_c (SUC cl) (e1, s) NONE
     ==> bs_l1_c (SUC cl) (L1_Geq e1 e2, s) NONE) /\

    (* Deref *)
    (!cl l s.
          l ∈ FDOM s
      ==> bs_l1_c (SUC cl) (L1_Deref l, s) (SOME (L1_Int (s ' l), s, cl))) /\

    (* Assign *)
    (!cl cl' l e s n s'.
        (l ∈ FDOM s /\
         bs_l1_c (SUC cl) (e, s) (SOME (L1_Int n, s', cl')))
     ==> bs_l1_c (SUC cl) (L1_Assign l e, s) (SOME (L1_Skip, s' |+ (l, n), cl'))) /\

    (!cl l e s.
        (l ∈ FDOM s /\
         bs_l1_c (SUC cl) (e, s) NONE)
     ==> bs_l1_c (SUC cl) (L1_Assign l e, s) NONE) /\

    (* Seq *)
    (!cl cl' cl'' e1 e2 v s s' s''.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Skip, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (v, s'', cl'')))
     ==> bs_l1_c (SUC cl) (L1_Seq e1 e2, s) (SOME (v, s'', cl''))) /\

    (!cl e1 e2 s.
         bs_l1_c (SUC cl) (e1, s) NONE
     ==> bs_l1_c (SUC cl) (L1_Seq e1 e2, s) NONE) /\

    (!cl cl' e1 e2 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Skip, s', cl')) /\
   bs_l1_c cl' (e2, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_Seq e1 e2, s) NONE) /\

    (* If *)
    (!cl cl' cl'' e1 e2 e3 s s' s'' v.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool T, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (v, s'', cl'')))
     ==> bs_l1_c (SUC cl) (L1_If e1 e2 e3, s) (SOME (v, s'', cl''))) /\
     
    (!cl cl' cl'' e1 e2 e3 s s' s'' v.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool F, s', cl')) /\
   bs_l1_c cl' (e3, s') (SOME (v, s'', cl'')))
     ==> bs_l1_c (SUC cl) (L1_If e1 e2 e3, s) (SOME (v, s'', cl''))) /\

    (!cl e1 e2 e3 s.
         bs_l1_c (SUC cl) (e1, s) NONE
     ==> bs_l1_c (SUC cl) (L1_If e1 e2 e3, s) NONE) /\

    (!cl cl' e1 e2 e3 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool T, s', cl')) /\
   bs_l1_c cl' (e2, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_If e1 e2 e3, s) NONE) /\
     
    (!cl cl' e1 e2 e3 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool F, s', cl')) /\
   bs_l1_c cl' (e3, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_If e1 e2 e3, s) NONE) /\

    (* While *)
    (!cl cl' cl'' cl''' e1 e2 s s' s'' s'''.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool T, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (L1_Skip, s'', cl'')) /\
   bs_l1_c cl'' (L1_While e1 e2, s'') (SOME (L1_Skip, s''', cl''')))
     ==> bs_l1_c (SUC cl) (L1_While e1 e2, s) (SOME (L1_Skip, s''', cl'''))) /\

    (!cl cl' e1 e2 s s'.
         bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool F, s', cl'))
     ==> bs_l1_c (SUC cl) (L1_While e1 e2, s) (SOME (L1_Skip, s', cl'))) /\

    (!cl e1 e2 s.
         bs_l1_c (SUC cl) (e1, s) NONE
     ==> bs_l1_c (SUC cl) (L1_While e1 e2, s) NONE) /\

    (!cl cl' e1 e2 s s'.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool T, s', cl')) /\
   bs_l1_c cl' (e2, s') NONE)
     ==> bs_l1_c (SUC cl) (L1_While e1 e2, s) NONE) /\

    (!cl cl' cl'' e1 e2 s s' s''.
        (bs_l1_c (SUC cl) (e1, s) (SOME (L1_Bool T, s', cl')) /\
   bs_l1_c cl' (e2, s') (SOME (L1_Skip, s'', cl'')) /\
   bs_l1_c cl'' (L1_While e1 e2, s'') NONE)
     ==> bs_l1_c (SUC cl) (L1_While e1 e2, s) NONE)
`;

val _ = export_theory ();
