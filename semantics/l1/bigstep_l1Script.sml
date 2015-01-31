open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory;

val _ = new_theory "bigstep_l1";

val (bs_l1_rules, bs_l1_induction, bs_l1_ecases) = Hol_reln `
    (* Values *)
    (!v s.bs_l1 (L1_Value v, s) v s) /\

    (* Plus *)
    (!e1 e2 n1 n2 s s' s''.
        (bs_l1 (e1, s) (L1_Int n1) s' /\
	 bs_l1 (e2, s') (L1_Int n2) s'')
     ==> bs_l1 (L1_Plus e1 e2, s) (L1_Int (n1 + n2)) s'') /\

    (* Geq *)
    (!e1 e2 n1 n2 s s' s''.
        (bs_l1 (e1, s) (L1_Int n1) s' /\
	 bs_l1 (e2, s') (L1_Int n2) s'')
     ==> bs_l1 (L1_Geq e1 e2, s) (L1_Bool (n1 >= n2)) s'') /\

    (* Deref *)
    (!l s.
          l ∈ FDOM s
      ==> bs_l1 (L1_Deref(l), s) (L1_Int (s ' l)) s) /\

    (* Assign *)
    (!l e s n s'.
        (l ∈ FDOM s /\
         bs_l1 (e, s) (L1_Int n) s')
     ==> bs_l1 (L1_Assign l e, s) (L1_Skip) (s' |+ (l, n))) /\

    (* Seq *)
    (!e1 e2 v s s' s''.
        (bs_l1 (e1, s) (L1_Skip) s' /\
	 bs_l1 (e2, s') v s'')
     ==> bs_l1 (L1_Seq e1 e2, s) v s'') /\

    (* If *)
    (!e1 e2 e3 s s' s'' v.
        (bs_l1 (e1, s) (L1_Bool T) s' /\
	 bs_l1 (e2, s') v s'')
     ==> bs_l1 (L1_If e1 e2 e3, s) v s'') /\
     
    (!e1 e2 e3 s s' s'' v.
        (bs_l1 (e1, s) (L1_Bool F) s' /\
	 bs_l1 (e3, s') v s'')
     ==> bs_l1 (L1_If e1 e2 e3, s) v s'') /\

    (* While *)
    (!e1 e2 s s' s'' s'''.
        (bs_l1 (e1, s) (L1_Bool T) s' /\
	 bs_l1 (e2, s') L1_Skip s'' /\
	 bs_l1 (L1_While e1 e2, s'') L1_Skip s''')
     ==> bs_l1 (L1_While e1 e2, s) L1_Skip s''') /\

    (!e1 e2 s s'.
         bs_l1 (e1, s) (L1_Bool F) s'
     ==> bs_l1 (L1_While e1 e2, s) L1_Skip s')`;

val _ = export_theory ();
