open HolKernel boolLib bossLib Parse IndDefLib ast_il1Theory smallstep_il2Theory listTheory integerTheory lcsymtacs il2_compositionTheory relationTheory il1_to_il2_compilerTheory pairTheory bigstep_il1Theory bigstep_il1_clockedTheory smallstep_il2_clockedTheory;

val _ = new_theory "il1_il2_correctness";

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);
val rwa = rw_tac (srw_ss () ++ intSimps.INT_ARITH_ss);

val il1_il2_val_def = Define `
(il1_il2_val (IL1_Integer n) = n) /\
(il1_il2_val (IL1_ESkip) = skip_value) /\
(il1_il2_val (IL1_Boolean T) = true_value) /\
(il1_il2_val (IL1_Boolean F) = false_value)`;

val thmtest1 = prove(``∀P P' clk stk st clk' stk' st' clk'' stk'' st'' endpc.
     exec_clocked P (SOME (0,clk, stk,st)) (SOME (&LENGTH P,clk', stk',st')) ∧
     exec_clocked P' (SOME (0,clk', stk',st')) (SOME (&LENGTH P',clk'', stk'',st'')) /\ (&LENGTH P + &LENGTH P' = endpc) ⇒
     exec_clocked (P ++ P') (SOME (0,clk, stk,st)) (SOME (endpc,clk'', stk'',st''))``, metis_tac [EX_COM_THM]);

val thmtest2 = METIS_PROVE [EXECUTION_COMPOSE_THM]
``
∀P P' clk stk st i' clk' stk' st' x x'.
     exec_clocked P (SOME (0,clk,stk,st)) (SOME (i',clk',stk',st')) ∧ &LENGTH P ≤ i' ∧
     exec_clocked P' (SOME (i' − &LENGTH P,clk',stk',st')) x
   /\ (x' = incr_pc x (&LENGTH P))
⇒
     exec_clocked (P ++ P') (SOME (0,clk,stk,st)) x'
``;

val thmtest3 = METIS_PROVE [APPEND_TRACE_SAME_2_THM, incr_pc_def]
``
∀P P' pc clk stk st clk' pc' stk' st' pc1 pc2.
     exec_clocked P (SOME (pc, clk, stk, st)) (SOME (pc',clk',  stk', st')) /\ (pc1 = pc + &LENGTH P') /\ (pc2 = pc' + &LENGTH P') ⇒
       exec_clocked (P' ++ P) (SOME (pc1, clk, stk, st)) (SOME (pc2, clk', stk', st'))``;

val thmtest4 = METIS_PROVE [APPEND_TRACE_SAME_2_THM, incr_pc_def]
``
!P P' c c' cn cn'.exec_clocked P c c' /\ (cn' = (incr_pc c' (&LENGTH P'))) /\ (cn = (incr_pc c (&LENGTH P'))) ==> exec_clocked (P' ++ P) cn cn'
``;

val jz_thm = prove(``!x clk stk s.exec_clocked [IL2_Jz x] (SOME (0, clk, false_value::stk, s)) (SOME (1 + x, clk, stk, s))``,
rw [exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, false_value_def]);

fun btotal f x = f x handle HOL_ERR _ => false;

fun P id tm =
  btotal ((equal id) o fst o dest_var) tm orelse
  P id (snd(listSyntax.dest_cons tm));

fun tac P (g as (asl,w)) =
  let
    val ts = mk_set(List.concat (map (find_terms (btotal P)) (w::asl)))
    val ths = mapfilter (fn tm => map (C SPEC (ASSUME tm)) ts) asl
  in
    map_every assume_tac (List.concat ths)
  end g;

fun match_exists_tac tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val vs = map (fst o dest_var o variant (free_vars tm)) vs
    fun k (g as (_,w)) =
      let
        val (_,b) = strip_exists w
        val cs = strip_conj b val c = hd cs
        val (tms,_) = match_term c tm
        val xs = map #redex tms
        val ys = map #residue tms
        fun sorter ls = xs@(List.filter(not o Lib.C Lib.mem xs)ls)
      in
        CONV_TAC(RESORT_EXISTS_CONV sorter) >>
        map_every exists_tac ys
      end g
  in
    CONV_TAC(RENAME_VARS_CONV vs) >> k
  end g;

val length_thm = store_thm("length_thm",
``!l1 l2.&LENGTH l1 + &LENGTH l2 = &LENGTH (l1 ++ l2)``,
Induct_on `l1` THEN rwa [LENGTH, INT]);

val append_thm = prove(``!a b.a::b = [a] ++ b``, metis_tac [APPEND]);

val expr_correctness_lemma = prove(``!p v.bs_il1_expr p v ==> !clk stk.exec_clocked (il1e_to_il2 (FST p)) (SOME (0, clk, stk, (SND p))) (SOME (&LENGTH (il1e_to_il2 (FST p)), clk, (il1_il2_val v)::stk, (SND p)))``,
ho_match_mp_tac bs_il1_expr_strongind THEN rw [FST, SND, il1_il2_val_def] THEN rw [il1e_to_il2_def]

THEN1 (Cases_on `v` THEN rwa [exec_clocked_def, il1e_to_il2_def, Once RTC_CASES1, Once exec_clocked_one_cases, fetch_def, il1_il2_val_def] THEN (TRY (Cases_on `b`)) THEN rwa [il1e_to_il2_def, fetch_def, Once exec_clocked_instr_cases, Once exec_clocked_one_cases, il1_il2_val_def])


THEN1 (
tac (P "clk")
THEN tac (P "stk")
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN (TRY (Cases_on `n2 <= n1`)) THEN
rwa [exec_clocked_def, Once exec_clocked_one_cases, Once exec_clocked_instr_cases, Once RTC_CASES1, fetch_def, RTC_REFL, il1_il2_val_def, int_ge])

THEN1 (
tac (P "clk")
THEN tac (P "stk")
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN (TRY (Cases_on `n2 <= n1`)) THEN
rwa [exec_clocked_def, Once exec_clocked_one_cases, Once exec_clocked_instr_cases, Once RTC_CASES1, fetch_def, RTC_REFL, il1_il2_val_def, int_ge])

THEN1 rw [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL]

THEN1 (tac (P "clk") THEN tac (P "stk")
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN PURE_ONCE_REWRITE_TAC [append_thm]

THEN match_mp_tac thmtest2

THEN `exec_clocked [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] (SOME (0, clk, [true_value] ++ stk,s))
    (SOME (1,clk,stk,s))` by rw [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL, true_value_def]

THEN Q.LIST_EXISTS_TAC [`1`, `clk`, `stk`, `s`, `SOME (&((LENGTH (il1e_to_il2 e2) + (1 + LENGTH (il1e_to_il2 e3)))),
      clk,il1_il2_val v::stk,s)`]

THEN rwa [incr_pc_def]

THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN PURE_ONCE_REWRITE_TAC [append_thm]

THEN match_mp_tac thmtest2
THEN `exec_clocked [IL2_Jump (&LENGTH (il1e_to_il2 e3))]
    (SOME (0,clk,[il1_il2_val v] ++ stk,s)) (SOME (1 + &LENGTH (il1e_to_il2 e3),clk,[il1_il2_val v] ++ stk,s))` by rw [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL]

THEN first_assum (match_exists_tac o concl)

THEN Q.EXISTS_TAC `SOME (&(LENGTH (il1e_to_il2 e3)),clk,il1_il2_val v::stk,s)`

THEN rwa [incr_pc_def]

THEN rwa [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL])

THEN1 (rw [il1e_to_il2_def]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`clk`, `false_value::stk`, `s`] THEN rwa []
THEN PURE_ONCE_REWRITE_TAC [append_thm]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1e_to_il2 e2) + 1`, `clk`, `stk`, `s`, `SOME
     (&((LENGTH (il1e_to_il2 e2) + (1 + LENGTH (il1e_to_il2 e3)))),
      clk,il1_il2_val v::stk,s)`] THEN rwa [incr_pc_def]

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def])

THEN rwa [INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC]

THEN match_mp_tac thmtest3 THEN Q.LIST_EXISTS_TAC [`0`, `&LENGTH (il1e_to_il2 e3)`] THEN rwa [])
);

val EXPR_CORRECTNESS_THM = store_thm("EXPR_CORRECTNESS_THM",
``!e s v.bs_il1_expr (e, s) v ==>
     !clk stk.
       exec_clocked (il1e_to_il2 e) (SOME (0,clk, stk,s))
         (SOME (&LENGTH (il1e_to_il2 e),clk, il1_il2_val v::stk,s))``,
metis_tac [expr_correctness_lemma, FST, SND]);

val correctness_lemma = prove(``!c p r.bs_il1_c c p r ==> !stk.((r = NONE) /\ (exec_clocked (il1_to_il2 (FST p)) (SOME (0, c, stk, (SND p))) NONE)) \/ (?v s' c'.(r = SOME (v, s', c')) /\ (exec_clocked (il1_to_il2 (FST p)) (SOME (0, c, stk, SND p)) (SOME (&LENGTH (il1_to_il2 (FST p)), c', il1_il2_val v::stk, s'))))``,

ho_match_mp_tac bs_il1_c_strongind THEN rw [FST, SND, il1_il2_val_def]

THEN1 metis_tac [il1_to_il2_def, EXPR_CORRECTNESS_THM]

THEN1 (rw [il1_to_il2_def]

THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN tac (P "clk")
THEN tac (P "stk")

THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`c`, `il1_il2_val (IL1_Integer n)::stk`, `s`] THEN rwa []

THEN (rw [exec_clocked_def, Once RTC_CASES1, Once exec_clocked_instr_cases, il1_il2_val_def, fetch_def, Once exec_clocked_one_cases] THEN rw [Once exec_clocked_instr_cases, fetch_def, Once exec_clocked_one_cases]))

THEN1 (rw [il1_to_il2_def]

THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN tac (P "clk")
THEN tac (P "stk")

THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`c`, `il1_il2_val (IL1_Integer n)::stk`, `s`] THEN rwa []

THEN (rw [exec_clocked_def, Once RTC_CASES1, Once exec_clocked_instr_cases, il1_il2_val_def, fetch_def, Once exec_clocked_one_cases] THEN rw [Once exec_clocked_instr_cases, fetch_def, Once exec_clocked_one_cases]))

THEN1 (rw [il1_to_il2_def]
THEN tac (P "clk")
THEN tac (P "stk")
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`c'`, `skip_value::stk`, `s'`] THEN rwa []

THEN PURE_REWRITE_TAC [Once append_thm]

THEN match_mp_tac thmtest1
THEN rwa []
THEN `exec_clocked [IL2_Pop] (SOME (0, c', skip_value::stk, s')) (SOME (1, c', stk, s'))` by rw [exec_clocked_def, exec_clocked_instr_cases, LENGTH, Once RTC_CASES1, RTC_REFL, fetch_def, Once exec_clocked_one_cases]
THEN first_assum (match_exists_tac o concl) THEN rw [])

THEN1 (rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac APPEND_TRACE_SAME_THM THEN metis_tac [])

THEN1 (rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac DIV_THM THEN Q.LIST_EXISTS_TAC [`c'`, `skip_value::stk`, `s'`] THEN rw [] THEN PURE_REWRITE_TAC [Once append_thm] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac DIV_THM THEN Q.LIST_EXISTS_TAC [`c'`, `stk`, `s'`] THEN rw [] THEN (rw [exec_clocked_def, Once RTC_CASES1, Once exec_clocked_instr_cases, il1_il2_val_def, fetch_def, Once exec_clocked_one_cases] THEN rw [Once exec_clocked_instr_cases, fetch_def, Once exec_clocked_one_cases]))

THEN1 (rw [il1_to_il2_def]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN imp_res_tac EXPR_CORRECTNESS_THM THEN fs [il1_il2_val_def]

THEN Q.LIST_EXISTS_TAC [`c`, `true_value::stk`, `s`] THEN rwa []
THEN PURE_REWRITE_TAC [Once append_thm]
THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`c`, `stk`, `s`] THEN rwa []

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`cl'`, `il1_il2_val v::stk`, `s'`] THEN rwa []

THEN PURE_REWRITE_TAC [Once append_thm]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1_to_il2 e3)`, `cl'`, `il1_il2_val v::stk`, `s'`,`SOME (&LENGTH (il1_to_il2 e3), cl', il1_il2_val v::stk, s')`] THEN rwa [incr_pc_def] THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def]) THEN rw [exec_clocked_def, RTC_REFL])


THEN1 (rw [il1_to_il2_def]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN imp_res_tac EXPR_CORRECTNESS_THM THEN fs [il1_il2_val_def]

THEN Q.LIST_EXISTS_TAC [`c`, `false_value::stk`, `s`] THEN rwa []
THEN PURE_REWRITE_TAC [Once append_thm]
THEN match_mp_tac thmtest2

THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1_to_il2 e2) + 1`, `c`, `stk`, `s`, `SOME (&(LENGTH (il1_to_il2 e2) + 1 + LENGTH (il1_to_il2 e3)), cl', il1_il2_val v::stk, s')`] THEN rwa [incr_pc_def]

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def])

THEN match_mp_tac thmtest3 THEN Q.LIST_EXISTS_TAC [`0`, `&LENGTH (il1_to_il2 e3)`] THEN rwa [])



THEN1 (rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1e_to_il2 e1)`, `c`, `false_value::stk`, `s`, `NONE`] THEN rwa [il1_il2_val_def, incr_pc_def] THEN fs [il1_il2_val_def]

THEN PURE_REWRITE_TAC [Once append_thm]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1_to_il2 e2) + 1`, `c`, `stk`, `s`, `NONE`] THEN rwa [incr_pc_def] THEN fs [il1_il2_val_def]
THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN fs [INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC]

THEN match_mp_tac thmtest4 THEN Q.LIST_EXISTS_TAC [`SOME (0, c, stk, s)`, `NONE`] THEN rwa [incr_pc_def])


THEN1 (rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1e_to_il2 e1)`, `c`, `true_value::stk`, `s`, `NONE`] THEN rwa [il1_il2_val_def, incr_pc_def] THEN fs [il1_il2_val_def]

THEN PURE_REWRITE_TAC [Once append_thm]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1`, `c`, `stk`, `s`, `NONE`] THEN rwa [incr_pc_def] THEN fs [il1_il2_val_def]
THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac APPEND_TRACE_SAME_THM THEN metis_tac [])

THEN1 (rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1e_to_il2 e1)`, `c`, `true_value::stk`, `s`, `NONE`] THEN rwa [il1_il2_val_def, incr_pc_def] THEN fs [il1_il2_val_def]

THEN PURE_REWRITE_TAC [Once append_thm]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1`, `c`, `stk`, `s`, `NONE`] THEN rwa [incr_pc_def] THEN fs [il1_il2_val_def]
THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac APPEND_TRACE_SAME_THM THEN metis_tac [])

THEN1 (
rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest1 THEN imp_res_tac EXPR_CORRECTNESS_THM THEN fs [il1_il2_val_def] THEN Q.LIST_EXISTS_TAC [`c`, `false_value::stk`, `s`] THEN rwa [] THEN PURE_REWRITE_TAC [Once append_thm]

THEN match_mp_tac thmtest2
THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1_to_il2 e2) + 2`, `c`, `stk`, `s`, `SOME (&(LENGTH (il1_to_il2 e2) + 3), c, skip_value::stk, s)`] THEN rwa [incr_pc_def]

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def])

THEN match_mp_tac thmtest3 THEN Q.LIST_EXISTS_TAC [`0`, `1`] THEN rwa [] THEN rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def])



THEN1 (
`exec_clocked (il1_to_il2 (IL1_While e1 e2)) (SOME (0,c,stk,s))
  (SOME
     (0, c',stk,s'))` by (


rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2 THEN imp_res_tac EXPR_CORRECTNESS_THM THEN fs [il1_il2_val_def] THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1e_to_il2 e1)`, `c`, `true_value::stk`, `s`, `SOME (-&LENGTH(il1e_to_il2 e1), c', stk, s')`] THEN rwa [incr_pc_def] THEN PURE_REWRITE_TAC [Once append_thm]

THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1`, `c`, `stk`, `s`, `SOME (-(1 + &LENGTH (il1e_to_il2 e1)), c', stk, s')`] THEN rwa [incr_pc_def]

THEN1 (
rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN REWRITE_TAC [GSYM APPEND_ASSOC]

THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1_to_il2 e2)`, `c'`, `skip_value::stk`, `s'`, `SOME (-((&LENGTH (il1_to_il2 e2)) + (1 + (&LENGTH (il1e_to_il2 e1)))), c', stk, s')`] THEN rwa [incr_pc_def]

THEN PURE_REWRITE_TAC [Once append_thm] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2
THEN Q.LIST_EXISTS_TAC [`1`, `c'`, `stk`, `s'`, `SOME (-(1 + (&LENGTH (il1_to_il2 e2) + (1 + &LENGTH (il1e_to_il2 e1)))), c', stk, s')`] THEN rwa [incr_pc_def]

THEN (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def]))

THEN rw [exec_clocked_def]
THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE))))
THEN rw [GSYM exec_clocked_def]
THEN Q.EXISTS_TAC `(SOME (0,c',stk,s'))` THEN rw [])

THEN1 (
`exec_clocked (il1_to_il2 (IL1_While e1 e2)) (SOME (0,c,stk,s))
  (SOME
     (0, c',stk,s'))` by (


rw [il1_to_il2_def] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2 THEN imp_res_tac EXPR_CORRECTNESS_THM THEN fs [il1_il2_val_def] THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1e_to_il2 e1)`, `c`, `true_value::stk`, `s`, `SOME (-&LENGTH(il1e_to_il2 e1), c', stk, s')`] THEN rwa [incr_pc_def] THEN PURE_REWRITE_TAC [Once append_thm]

THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1`, `c`, `stk`, `s`, `SOME (-(1 + &LENGTH (il1e_to_il2 e1)), c', stk, s')`] THEN rwa [incr_pc_def]

THEN1 (
rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN REWRITE_TAC [GSYM APPEND_ASSOC]

THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`&LENGTH (il1_to_il2 e2)`, `c'`, `skip_value::stk`, `s'`, `SOME (-((&LENGTH (il1_to_il2 e2)) + (1 + (&LENGTH (il1e_to_il2 e1)))), c', stk, s')`] THEN rwa [incr_pc_def]

THEN PURE_REWRITE_TAC [Once append_thm] THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN match_mp_tac thmtest2
THEN Q.LIST_EXISTS_TAC [`1`, `c'`, `stk`, `s'`, `SOME (-(1 + (&LENGTH (il1_to_il2 e2) + (1 + &LENGTH (il1e_to_il2 e1)))), c', stk, s')`] THEN rwa [incr_pc_def]

THEN (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def]))

THEN rw [exec_clocked_def]
THEN match_mp_tac (GEN_ALL(CONJUNCT2 (SPEC_ALL (REWRITE_RULE [EQ_IMP_THM] RTC_CASES_RTC_TWICE))))
THEN rw [GSYM exec_clocked_def]
THEN Q.EXISTS_TAC `(SOME (0,c',stk,s'))` THEN rw []

THEN (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [il1_to_il2_def, exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])
)

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [il1_to_il2_def, exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def])

THEN1 (
Cases_on `r` THEN fs []
THEN1 (
rw [il1_to_il2_def]
THEN PURE_REWRITE_TAC [Once append_thm]

THEN match_mp_tac DIV_THM THEN Q.LIST_EXISTS_TAC [`c`, `stk`, `s`] THEN rw [] THEN (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [il1_to_il2_def, exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def]))

THEN Cases_on `x` THEN Cases_on `r` THEN rw [] THEN rw [il1_to_il2_def] THEN PURE_REWRITE_TAC [Once append_thm] THEN match_mp_tac thmtest1 THEN Q.LIST_EXISTS_TAC [`c`, `stk`, `s`] THEN rwa [] THEN (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [il1_to_il2_def, exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def, true_value_def]))
);

val CORRECTNESS_1_THM = store_thm("IL1_IL2_CORRECTNESS_1_THM",
``!c e s.bs_il1_c c (e, s) NONE ==>
    !stk.
       exec_clocked (il1_to_il2 e) (SOME (0, c, stk, s))
         NONE``,
rw [] THEN imp_res_tac correctness_lemma THEN fs []);

val CORRECTNESS_2_THM = store_thm("IL1_IL2_CORRECTNESS_2_THM",
``!c e s v s' c'.bs_il1_c c (e, s) (SOME (v, s', c')) ==>
    !stk.
      exec_clocked (il1_to_il2 e) (SOME (0, c, stk, s))
        (SOME (&LENGTH (il1_to_il2 e), c', (il1_il2_val v)::stk, s'))``,
rw [] THEN imp_res_tac correctness_lemma THEN fs [FST, SND]);

val _ = export_theory ();
