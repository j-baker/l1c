open HolKernel boolLib bossLib lcsymtacs ast_il1Theory bigstep_il1_clockedTheory bigstep_il1Theory;

val _ = new_theory "il1_back";

val BS_IL1_EXPR_VALUE_BACK_THM = store_thm("BS_IL1_EXPR_VALUE_BACK_THM",
``!v s v'.bs_il1_expr (IL1_Value v, s) v' ==> (v = v')``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val BS_IL1_EXPR_PLUS_BACK_THM = store_thm("BS_IL1_EXPR_PLUS_BACK_THM",
``!e1 e2 s v.bs_il1_expr (IL1_Plus e1 e2, s) v ==> ?n1 n2.bs_il1_expr (e1, s) (IL1_Integer n1) /\ bs_il1_expr (e2, s) (IL1_Integer n2) /\ (v = IL1_Integer (n1 + n2))``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val BS_IL1_EXPR_GEQ_BACK_THM = store_thm("BS_IL1_EXPR_GEQ_BACK_THM",
``!e1 e2 s v.bs_il1_expr (IL1_Geq e1 e2, s) v ==> ?n1 n2.bs_il1_expr (e1, s) (IL1_Integer n1) /\ bs_il1_expr (e2, s) (IL1_Integer n2) /\ (v = IL1_Boolean (n1 >= n2))``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val BS_IL1_EXPR_DEREF_BACK_THM = store_thm("BS_IL1_EXPR_DEREF_BACK_THM",
``!l s v.bs_il1_expr (IL1_Deref l, s) v ==> l ∈ FDOM s /\ (v = IL1_Integer (s ' l))``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val BS_IL1_EXPR_EIF_BACK_THM = store_thm("BS_IL1_EXPR_EIF_BACK_THM",
``!e1 e2 e3 s v.bs_il1_expr (IL1_EIf e1 e2 e3, s) v ==> (bs_il1_expr (e1, s) (IL1_Boolean T) /\ bs_il1_expr (e2, s) v) \/ (bs_il1_expr (e1, s) (IL1_Boolean F) /\ bs_il1_expr (e3, s) v)``,
rw [Once bs_il1_expr_cases] THEN metis_tac []);

val IL1_EXPR_BACK_THM = store_thm("IL1_EXPR_BACK_THM",
``!e v s s' c c'.bs_il1_c c (IL1_Expr e, s) (SOME (v, s', c')) ==> bs_il1_expr (e, s) v /\ (s = s') /\ (c = c')``,
rw [Once bs_il1_c_cases] THEN metis_tac []);

val IL1_SEQ_BACK_THM = store_thm("IL1_SEQ_BACK_THM",
``!e1 e2 v s s'' cl cl''.bs_il1_c cl (IL1_Seq e1 e2, s) (SOME (v, s'', cl'')) ==> ?cl' s'.bs_il1_c cl (e1, s) (SOME (IL1_ESkip, s', cl')) /\ bs_il1_c cl' (e2, s') (SOME (v, s'', cl''))``,
rw [Once bs_il1_c_cases] THEN metis_tac []);

val IL1_ASSIGN_BACK_THM = store_thm("IL1_ASSIGN_BACK_THM",
``!l e s s' v cl cl'.bs_il1_c cl (IL1_Assign l e, s) (SOME (v, s', cl')) ==> (cl = cl') /\ (v = IL1_ESkip) /\ ?n.bs_il1_expr (e, s) (IL1_Integer n) /\ (s' = (s |+ (l, n))) /\ (!l'.(l = User l') ==> l ∈ FDOM s)``,
rw [Once bs_il1_c_cases] THEN metis_tac []);

val IL1_SIF_BACK_THM = store_thm("IL1_SIF_BACK_THM",
``!e1 e2 e3 s v s' cl cl'.bs_il1_c cl (IL1_SIf e1 e2 e3, s) (SOME (v, s', cl')) ==> (bs_il1_expr (e1, s) (IL1_Boolean T) /\ bs_il1_c cl (e2, s) (SOME (v, s', cl'))) \/ (bs_il1_expr (e1, s) (IL1_Boolean F) /\ bs_il1_c cl (e3, s) (SOME (v, s', cl')))``,
rw [Once bs_il1_c_cases] THEN metis_tac []);

val IL1_WHILE_BACK_THM = store_thm("IL1_WHILE_BACK_THM",
``!e1 e2 s s'' v cl cl''.bs_il1_c cl (IL1_While e1 e2, s) (SOME (v, s'', cl'')) ==> (v = IL1_ESkip) /\ ((bs_il1_expr (e1, s) (IL1_Boolean F) /\ (s = s'')) \/ (bs_il1_expr (e1, s) (IL1_Boolean T) /\ ?s' c cl'.(cl = SUC c) /\ bs_il1_c c (e2, s) (SOME (IL1_ESkip, s', cl')) /\ bs_il1_c cl' (IL1_While e1 e2, s') (SOME (IL1_ESkip, s'', cl''))))``,
rw [Once bs_il1_c_cases] THEN metis_tac []);

val _ = export_theory ();
