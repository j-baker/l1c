open HolKernel boolLib bossLib Parse IndDefLib ast_il1Theory smallstep_il2Theory listTheory integerTheory lcsymtacs il2_compositionTheory relationTheory il1_to_il2_compilerTheory pairTheory bigstep_il1Theory smallstep_il2_clockedTheory;

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
∀P P' clk stk st i' clk' stk' st' i'' clk'' stk'' st'' t.
     exec_clocked P (SOME (0,clk,stk,st)) (SOME (i',clk',stk',st')) ∧ &LENGTH P ≤ i' ∧
     exec_clocked P' (SOME (i' − &LENGTH P,clk',stk',st')) (SOME (i'',clk'',stk'',st''))
   /\ (t = &LENGTH P + i'')
⇒
     exec_clocked (P ++ P') (SOME (0,clk,stk,st)) (SOME (t,clk'',stk'',st''))
``;

val thmtest3 = METIS_PROVE [APPEND_TRACE_SAME_2_THM, incr_pc_def]
``
∀P P' pc clk stk st clk' pc' stk' st' pc1 pc2.
     exec_clocked P (SOME (pc, clk, stk, st)) (SOME (pc',clk',  stk', st')) /\ (pc1 = pc + &LENGTH P') /\ (pc2 = pc' + &LENGTH P') ⇒
       exec_clocked (P' ++ P) (SOME (pc1, clk, stk, st)) (SOME (pc2, clk', stk', st'))``;

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

THEN first_assum (match_exists_tac o concl)
THEN rwa []

THEN `&(1 + (LENGTH (il1e_to_il2 e2) + (1 + LENGTH (il1e_to_il2 e3)))) =
   1 + &((LENGTH (il1e_to_il2 e2) + (1 + LENGTH (il1e_to_il2 e3))))` by rwa []
THEN HINT_EXISTS_TAC
THEN fsa [] THEN rwa []

THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []
THEN PURE_ONCE_REWRITE_TAC [append_thm]

THEN match_mp_tac thmtest2
THEN `exec_clocked [IL2_Jump (&LENGTH (il1e_to_il2 e3))]
    (SOME (0,clk,[il1_il2_val v] ++ stk,s)) (SOME (1 + &LENGTH (il1e_to_il2 e3),clk,[il1_il2_val v] ++ stk,s))` by rw [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL]

THEN first_assum (match_exists_tac o concl)

THEN rwa []

THEN `&(1 + LENGTH (il1e_to_il2 e3)) = 1 + &LENGTH (il1e_to_il2 e3)` by rwa []

THEN HINT_EXISTS_TAC

THEN rwa [il1e_to_il2_def, exec_clocked_def, Once RTC_CASES1, exec_clocked_one_cases, fetch_def, exec_clocked_instr_cases, RTC_REFL])

THEN1 (rw [il1e_to_il2_def]
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN Q.LIST_EXISTS_TAC [`clk`, `false_value::stk`, `s`] THEN rwa []
THEN PURE_ONCE_REWRITE_TAC [append_thm]
THEN match_mp_tac thmtest2 THEN Q.LIST_EXISTS_TAC [`1 + &LENGTH (il1e_to_il2 e2) + 1`, `clk`, `stk`, `s`, `&(LENGTH (il1e_to_il2 e2) + (1 + LENGTH (il1e_to_il2 e3)))`] THEN rwa []

THEN1 (rw [exec_clocked_def] THEN match_mp_tac RTC_SUBSET THEN rwa [exec_clocked_one_cases, exec_clocked_instr_cases, fetch_def, false_value_def])

THEN rwa [INT_SUB_CALCULATE, INT_ADD_RINV, GSYM INT_ADD_ASSOC]

THEN match_mp_tac thmtest3 THEN Q.LIST_EXISTS_TAC [`0`, `&LENGTH (il1e_to_il2 e3)`] THEN rwa [])
);

val EXPR_CORRECTNESS_THM = store_thm("EXPR_CORRECTNESS_THM",
``!e s v.bs_il1_expr (e, s) v ==>
     !stk.
       exec (il1e_to_il2 e) (0,stk,s)
         (&LENGTH (il1e_to_il2 e),il1_il2_val v::stk,s)``,
metis_tac [expr_correctness_lemma, FST, SND]);

val correctness_lemma = prove(``!p v s'.bs_il1 p v s' ==> !stk.exec (il1_to_il2 (FST p)) (0, stk, (SND p)) (&LENGTH (il1_to_il2 (FST p)), (il1_il2_val v)::stk, s')``,
ho_match_mp_tac bs_il1_strongind THEN rw [FST, SND, il1_il2_val_def]

THEN1 metis_tac [il1_to_il2_def, EXPR_CORRECTNESS_THM]

THEN1 (rw [il1_to_il2_def]

THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN tac (P "stk")

THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []

THEN (rw [exec_def, Once RTC_CASES1, Once exec_instr_cases, il1_il2_val_def, fetch_def, Once exec_one_cases] THEN rw [Once exec_instr_cases, fetch_def, Once exec_one_cases]))

THEN1 (rw [il1_to_il2_def]

THEN imp_res_tac EXPR_CORRECTNESS_THM
THEN tac (P "stk")

THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN rwa []

THEN (rw [exec_def, Once RTC_CASES1, Once exec_instr_cases, il1_il2_val_def, fetch_def, Once exec_one_cases] THEN rw [Once exec_instr_cases, fetch_def, Once exec_one_cases]))

THEN1 (rw [il1_to_il2_def]

THEN tac (P "stk")
THEN REWRITE_TAC [GSYM APPEND_ASSOC]
THEN match_mp_tac thmtest1
THEN first_assum (match_exists_tac o concl)
THEN CONJ_TAC THEN1 rwa []
THEN CONJ_TAC

THEN1 (match_mp_tac thmtest1
THEN rwa []
THEN `exec [IL2_Pop] (0, skip_value::stk, s') (1, stk, s')` by rw [exec_def, exec_instr_cases, LENGTH, Once RTC_CASES1, RTC_REFL, fetch_def, Once exec_one_cases]
THEN first_assum (match_exists_tac o concl)
THEN rwa [])

THEN rwa [])

THEN1 (rw [il1_to_il2_def]
THEN `exec (il1e_to_il2 e1) (0, stk, s) (&LENGTH (il1e_to_il2 e1), true_value::stk, s)` by metis_tac [EXPR_CORRECTNESS_THM, il1_il2_val_def]
THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] (0, true_value::stk, s) (&LENGTH [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)], stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, true_value_def])

THEN `exec (il1_to_il2 e2) (0, stk, s) (&LENGTH (il1_to_il2 e2), (il1_il2_val v)::stk, s')` by rwa [length_thm]

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)])
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)]),stk,s)` by metis_tac [length_thm, EX_COM_THM]

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
          il1_to_il2 e2) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ (il1_to_il2 e2)),il1_il2_val v::stk,s')` by metis_tac [length_thm, EX_COM_THM]


THEN `exec [IL2_Jump (&LENGTH (il1_to_il2 e3))] (&LENGTH
            (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
             il1_to_il2 e2) - (&LENGTH
            (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
             il1_to_il2 e2)), il1_il2_val v::stk, s') (1 + &LENGTH (il1_to_il2 e3), il1_il2_val v::stk, s')` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, true_value_def])

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
          il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))])
         (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
              il1_to_il2 e2) + (1 + &LENGTH (il1_to_il2 e3)),
          il1_il2_val v::stk,s')` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

 
THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
          il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))] ++ il1_to_il2 e3)
         (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
              il1_to_il2 e2)+ (1 + &LENGTH (il1_to_il2 e3)),
          il1_il2_val v::stk,s')` by metis_tac [APPEND_TRACE_SAME_THM]

THEN fsa [length_thm, INT]

THEN `&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 1 +
     LENGTH (il1_to_il2 e3)) = &(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2)) +
          (1 + &LENGTH (il1_to_il2 e3))` by rwa []

THEN metis_tac [])

THEN1 (rw [il1_to_il2_def]

THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] (0,false_value::stk,s) (1 + &LENGTH (il1_to_il2 e2) + 1, stk, s)` by (rwa [exec_def]
THEN match_mp_tac RTC_SUBSET
THEN rwa [exec_one_cases, fetch_def, exec_instr_cases, false_value_def])



THEN `exec (il1e_to_il2 e1) (0, stk, s) (&LENGTH (il1e_to_il2 e1), false_value::stk, s)` by metis_tac [EXPR_CORRECTNESS_THM, il1_il2_val_def]
THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] (0, false_value::stk, s) (1 + &LENGTH (il1_to_il2 e2) + 1, stk, s)` by (rw [exec_def] THEN fs [RTC_SINGLE] THEN
 rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, false_value_def]
THEN
`(exec_one [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)])^* (1 + &LENGTH (il1_to_il2 e2) + 1, stk, s)
    (1 + &LENGTH (il1_to_il2 e2) + 1,stk,s)` by metis_tac [RTC_REFL]
THEN `1 + &(LENGTH (il1_to_il2 e2) + 1) = 1 + &LENGTH (il1_to_il2 e2) + 1` by rwa []
THEN rwa []
THEN metis_tac []
)


THEN `exec ([IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ il1_to_il2 e2) (0, false_value::stk, s) (1 + &LENGTH (il1_to_il2 e2) + 1, stk, s)` by metis_tac [APPEND_TRACE_SAME_THM]

THEN `exec (il1_to_il2 e3) (0, stk, s) (&LENGTH (il1_to_il2 e3), (il1_il2_val v)::stk, s')` by metis_tac []

THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] (&LENGTH (il1e_to_il2 e1) - &LENGTH (il1e_to_il2 e1),false_value::stk,s)
        (1 + &LENGTH (il1_to_il2 e2) + 1,stk,s)` by rwa []

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)])
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1_to_il2 e2) + 1),stk,
          s)` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ il1_to_il2 e2)
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1_to_il2 e2) + 1),stk,
          s)` by metis_tac [APPEND_TRACE_SAME_THM]

THEN `&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1_to_il2 e2) + 1) = (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))]))` by rwa []

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ il1_to_il2 e2)
         (0,stk,s)
         ((&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++ il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))])),stk,
          s)` by metis_tac []

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
          il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))]) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
              il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))]),
          stk,s)` by metis_tac [APPEND_TRACE_SAME_THM]


THEN ` exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
          il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))] ++ il1_to_il2 e3) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
              il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))]) + &LENGTH (il1_to_il2 e3),
          il1_il2_val v::stk,s')` by (imp_res_tac EX_COM_THM THEN rwa [])

THEN `&LENGTH
             (il1e_to_il2 e1 ++
              [IL2_Jz (&LENGTH (il1_to_il2 e2) + 1)] ++
              il1_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1_to_il2 e3))]) +
          &LENGTH (il1_to_il2 e3) = &(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 1 +
     LENGTH (il1_to_il2 e3))` by rwa [length_thm]

THEN metis_tac [])

THEN1 (`exec (il1_to_il2 (IL1_While e1 e2)) (0, stk, s) (0, stk, s')` by all_tac

THEN1 (rw [il1_to_il2_def]
THEN `exec (il1e_to_il2 e1) (0, stk, s) (&LENGTH (il1e_to_il2 e1), true_value::stk, s)` by metis_tac [EXPR_CORRECTNESS_THM, il1_il2_val_def]
THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] (0, true_value::stk, s) (&LENGTH [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)], stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, true_value_def])

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)])
        (0,stk,s)
        (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)]),stk,s)` by (imp_res_tac EX_COM_THM THEN fsa [length_thm])

THEN `exec (il1_to_il2 e2) (0, stk, s) (&LENGTH (il1_to_il2 e2), skip_value::stk, s')` by metis_tac []

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
          il1_to_il2 e2) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++
              [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++ (il1_to_il2 e2)),skip_value::stk,s')` by (imp_res_tac EX_COM_THM THEN fsa [length_thm])

THEN `exec  [IL2_Pop; IL2_Tick;
    IL2_Jump
      (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 3))]

(0, skip_value::stk, s') (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2)), stk, s')` by (rw [exec_def, Once RTC_CASES1, Once exec_instr_cases, il1_il2_val_def, fetch_def, Once exec_one_cases, RTC_REFL] THEN rw [exec_def, Once RTC_CASES1, Once exec_instr_cases, il1_il2_val_def, fetch_def, Once exec_one_cases, RTC_REFL] THEN rw [exec_def, Once RTC_CASES1, Once exec_instr_cases, il1_il2_val_def, fetch_def, Once exec_one_cases, RTC_REFL, INT] THEN `3 +
   (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 3)) = -&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2))` by fsa [INT] THEN metis_tac [RTC_REFL])

THEN ` exec
         [IL2_Pop; IL2_Tick;
          IL2_Jump
            (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                3))] (&LENGTH
               (il1e_to_il2 e1 ++
                [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
                il1_to_il2 e2) −
            &LENGTH
               (il1e_to_il2 e1 ++
                [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
                il1_to_il2 e2),skip_value::stk,s')
         (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2)),stk,
          s')` by rwa []

THEN `
         exec
           (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
            il1_to_il2 e2 ++ [IL2_Pop; IL2_Tick;
          IL2_Jump
            (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                3))]) (0,stk,s)
           (&LENGTH
               (il1e_to_il2 e1 ++
                [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
                il1_to_il2 e2) + -&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2)),stk,s')` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])


THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
          il1_to_il2 e2 ++
          [IL2_Pop; IL2_Tick;
           IL2_Jump
             (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                 3))] ++ [IL2_Push skip_value]) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++
              [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++ il1_to_il2 e2) +
          -&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2)),stk,
          s')` by metis_tac [APPEND_TRACE_SAME_THM]


THEN fsa [])

THEN metis_tac [exec_def, RTC_TRANSITIVE, transitive_def])

THEN1 (rw [il1_to_il2_def]
THEN `exec (il1e_to_il2 e1) (0, stk, s') (&LENGTH (il1e_to_il2 e1), false_value::stk, s')` by metis_tac [EXPR_CORRECTNESS_THM, il1_il2_val_def]
THEN `exec [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] (0, false_value::stk, s') (1 + (&(LENGTH (il1_to_il2 e2)) + 3), stk, s')` by  (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, false_value_def] THEN fsa [] THEN metis_tac [RTC_REFL])

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)]) (0, stk, s') (&LENGTH (il1e_to_il2 e1) + (1 + (&LENGTH (il1_to_il2 e2) + 3)), stk, s')` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])


THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
   il1_to_il2 e2 ++
   [IL2_Pop; IL2_Tick;
    IL2_Jump
	(-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 3))]) (0, stk, s') (&LENGTH (il1e_to_il2 e1) + (1 + (&LENGTH (il1_to_il2 e2) + 3)), stk, s')` by metis_tac [APPEND_TRACE_SAME_THM]

THEN `exec [IL2_Push skip_value] (0, stk, s') (&LENGTH [IL2_Push skip_value], skip_value::stk, s')` by  (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, false_value_def] THEN rwa [])

THEN `exec
        (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
         il1_to_il2 e2 ++
         [IL2_Pop; IL2_Tick;
          IL2_Jump
            (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                3))]) (0,stk,s')
        (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
         il1_to_il2 e2 ++
         [IL2_Pop; IL2_Tick;
          IL2_Jump
            (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                3))]), stk, s')` by (rwa [INT, length_thm] THEN `&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) + 3) = &LENGTH (il1e_to_il2 e1) + (1 + (&LENGTH (il1_to_il2 e2) + 3))` by rwa [] THEN fs [])

THEN ` exec
        (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
         il1_to_il2 e2 ++
         [IL2_Pop; IL2_Tick;
          IL2_Jump
            (-&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1_to_il2 e2) +
                3))] ++ [IL2_Push skip_value]) (0,stk,s')
        (&LENGTH
            (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1_to_il2 e2) + 3)] ++
             il1_to_il2 e2 ++
             [IL2_Pop; IL2_Tick;
              IL2_Jump
                (-&(LENGTH (il1e_to_il2 e1) + 1 +
                    LENGTH (il1_to_il2 e2) + 3))]) +
         &LENGTH [IL2_Push skip_value],skip_value::stk,s')` by imp_res_tac EX_COM_THM

THEN fsa [INT, length_thm]));

val CORRECTNESS_THM = store_thm("CORRECTNESS_THM",
``!e s v s'.bs_il1 (e, s) v s' ==>
    !stk.
       exec (il1_to_il2 e) (0, stk, s)
         (&LENGTH (il1_to_il2 e), il1_il2_val v::stk, s')``,
metis_tac [correctness_lemma, FST, SND]);

val _ = export_theory ();
