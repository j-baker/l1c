open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory

val _ = new_theory "smallstep_l1"

val (ss_l1_rules, ss_l1_induction, ss_l1_ecases) = Hol_reln `
    (* Plus *)
    (!n1 n2 s.ss_l1 (L1_Plus (L1_Value (L1_Int n1)) (L1_Value (L1_Int n2)), s) (L1_Value (L1_Int (n1 + n2)), s)) /\
    (!e1 e1' e2 s s'.
          ss_l1 (e1, s) (e1', s')
      ==> ss_l1 (L1_Plus e1 e2, s) (L1_Plus e1' e2, s')) /\
    (!n e2 e2' s s'.
          ss_l1 (e2, s) (e2', s')
      ==> ss_l1 (L1_Plus (L1_Value (L1_Int n)) e2, s) (L1_Plus (L1_Value (L1_Int n)) e2', s')) /\

    (* Geq *)
    (!n1 n2 s.ss_l1 (L1_Geq (L1_Value (L1_Int n1)) (L1_Value (L1_Int n2)), s) (L1_Value (L1_Bool (n1 >= n2)), s)) /\
    (!e1 e1' e2 s s'.
          ss_l1 (e1, s) (e1', s')
      ==> ss_l1 (L1_Geq e1 e2, s) (L1_Geq e1' e2, s')) /\
    (!n e2 e2' s s'.
          ss_l1 (e2, s) (e2', s')
      ==> ss_l1 (L1_Geq (L1_Value (L1_Int n)) e2, s) (L1_Geq (L1_Value (L1_Int n)) e2', s')) /\

    (* Deref *)
    (!l s.
          l ∈ FDOM s
      ==> ss_l1 (L1_Deref(l), s) (L1_Value (L1_Int (s ' l)), s)) /\

    (* Assign *)
    (!l n s.
          l ∈ FDOM s
      ==> ss_l1 (L1_Assign l (L1_Value (L1_Int n)), s) (L1_Value L1_Skip, s |+ (l, n))) /\
    (!l e e' s s'.
          ss_l1 (e, s) (e', s')
      ==> ss_l1 (L1_Assign l e, s) (L1_Assign l e', s')) /\

    (* Seq *)
    (!e2 s.ss_l1 (L1_Seq (L1_Value L1_Skip) e2, s) (e2, s)) /\
    (!e1 e1' e2 s s'.
          ss_l1 (e1, s) (e1', s')
      ==> ss_l1 (L1_Seq e1 e2, s) (L1_Seq e1' e2, s')) /\

    (* If *)
    (!e2 e3 s. ss_l1 (L1_If (L1_Value (L1_Bool T)) e2 e3, s) (e2, s)) /\
    (!e2 e3 s. ss_l1 (L1_If (L1_Value (L1_Bool F)) e2 e3, s) (e3, s)) /\
    (!e1 e1' e2 e3 s s'.
          ss_l1 (e1, s) (e1', s')
      ==> ss_l1 (L1_If e1 e2 e3, s) (L1_If e1' e2 e3, s')) /\

    (* While *)
    (!e1 e2 s. ss_l1 (L1_While e1 e2, s) (L1_If e1 (L1_Seq e2 (L1_While e1 e2)) (L1_Value L1_Skip), s))`

val _ = export_theory ()
