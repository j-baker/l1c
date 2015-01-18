open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory pred_setTheory pairTheory lcsymtacs il1Theory integerTheory il2Theory;

val _ = new_theory "il1_to_il2";

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);
val rwa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);

val il1e_to_il2_def = Define `
(il1e_to_il2 (IL1_Value (IL1_Integer n)) = [IL2_Push n]) /\
(il1e_to_il2 (IL1_Value IL1_ESkip) = [IL2_Push skip_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean T)) = [IL2_Push true_value]) /\
(il1e_to_il2 (IL1_Value (IL1_Boolean F)) = [IL2_Push false_value]) /\

(il1e_to_il2 (IL1_Plus e1 e2) = (il1e_to_il2 e2 ++ il1e_to_il2 e1 ++ [IL2_Plus])) /\

(il1e_to_il2 (IL1_Deref l) = [IL2_Load l]) /\

(il1e_to_il2 (IL1_EIf e1 e2 e3) =
                                    (il1e_to_il2 e1) ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ (il1e_to_il2 e2) ++ [IL2_Jump (&LENGTH  (il1e_to_il2 e3))] ++  (il1e_to_il2 e3)) /\
(il1e_to_il2 (IL1_Geq e1 e2) = (il1e_to_il2 e2) ++ (il1e_to_il2 e1) ++ [IL2_Geq])
`;

val il1_il2_val_def = Define `
(il1_il2_val (IL1_Integer n) = n) /\
(il1_il2_val (IL1_ESkip) = skip_value) /\
(il1_il2_val (IL1_Boolean T) = true_value) /\
(il1_il2_val (IL1_Boolean F) = false_value)`;

val length_thm = store_thm("length_thm",
``!l1 l2.&LENGTH l1 + &LENGTH l2 = &LENGTH (l1 ++ l2)``,
Induct_on `l1` THEN rwa [LENGTH, INT]);

val expr_correctness_lemma = prove(``!p v.bs_il1_expr p v ==> !stk.exec (il1e_to_il2 (FST p)) (0, stk, (SND p)) (&LENGTH (il1e_to_il2 (FST p)), (il1_il2_val v)::stk, (SND p))``,
ho_match_mp_tac bs_il1_expr_strongind THEN rw [FST, SND, il1_il2_val_def]

THEN1 (Cases_on `v` THEN rwa [exec_def, il1e_to_il2_def, Once RTC_CASES1, Once exec_one_cases, fetch_def, Once exec_instr_cases, Once exec_one_cases, il1_il2_val_def] THEN (TRY (metis_tac [RTC_REFL])) THEN Cases_on `b` THEN rwa [exec_def, il1e_to_il2_def, Once RTC_CASES1, Once exec_one_cases, fetch_def, Once exec_instr_cases, Once exec_one_cases, il1_il2_val_def])


THEN1 (
rw [il1e_to_il2_def]
THEN `exec (il1e_to_il2 e2) (0, stk, s) (&LENGTH (il1e_to_il2 e2), n2::stk, s)` by metis_tac []
THEN `exec (il1e_to_il2 e1) (&LENGTH (il1e_to_il2 e2) - &LENGTH (il1e_to_il2 e2), n2::stk, s) (&LENGTH (il1e_to_il2 e1), n1::n2::stk, s)` by rwa []

THEN `exec ((il1e_to_il2 e2) ++ (il1e_to_il2 e1)) (0, stk, s) (&LENGTH (il1e_to_il2 e2) + &LENGTH (il1e_to_il2 e1), n1::n2::stk, s)` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

THEN `exec [IL2_Plus] ((&LENGTH (il1e_to_il2 e2) + &LENGTH (il1e_to_il2 e1)) - &LENGTH ((il1e_to_il2 e2) ++ (il1e_to_il2 e1)), n1::n2::stk, s) (&LENGTH [IL2_Plus], (n1 + n2)::stk, s)` by rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm]

THEN imp_res_tac EXECUTION_COMPOSE_THM
THEN rwa [length_thm])

THEN1 (
rw [il1e_to_il2_def]
THEN `exec (il1e_to_il2 e2) (0, stk, s) (&LENGTH (il1e_to_il2 e2), n2::stk, s)` by metis_tac []
THEN `exec (il1e_to_il2 e1) (&LENGTH (il1e_to_il2 e2) - &LENGTH (il1e_to_il2 e2), n2::stk, s) (&LENGTH (il1e_to_il2 e1), n1::n2::stk, s)` by rwa []

THEN `exec ((il1e_to_il2 e2) ++ (il1e_to_il2 e1)) (0, stk, s) (&LENGTH (il1e_to_il2 e2) + &LENGTH (il1e_to_il2 e1), n1::n2::stk, s)` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

THEN Cases_on `n1 >= n2`
THENL [`exec [IL2_Geq] ((&LENGTH (il1e_to_il2 e2) + &LENGTH (il1e_to_il2 e1)) - &LENGTH ((il1e_to_il2 e2) ++ (il1e_to_il2 e1)), n1::n2::stk, s) (&LENGTH [IL2_Geq], true_value::stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm] THEN rwa []),
`exec [IL2_Geq] ((&LENGTH (il1e_to_il2 e2) + &LENGTH (il1e_to_il2 e1)) - &LENGTH ((il1e_to_il2 e2) ++ (il1e_to_il2 e1)), n1::n2::stk, s) (&LENGTH [IL2_Geq], false_value::stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm] THEN rwa [])]

THEN imp_res_tac EXECUTION_COMPOSE_THM
THEN rwa [length_thm, il1_il2_val_def])

THEN1 rw [il1e_to_il2_def, exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL]


THEN1 (rw [il1e_to_il2_def]
THEN `exec (il1e_to_il2 e1) (0, stk, s) (&LENGTH (il1e_to_il2 e1), true_value::stk, s)` by metis_tac []
THEN `exec [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] (0, true_value::stk, s) (&LENGTH [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)], stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, true_value_def])

THEN `exec (il1e_to_il2 e2) (0, stk, s) (&LENGTH (il1e_to_il2 e2), (il1_il2_val v)::stk, s)` by rwa [length_thm]

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)])
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)]),stk,s)` by metis_tac [length_thm, EX_COM_THM]

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
          il1e_to_il2 e2) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ (il1e_to_il2 e2)),il1_il2_val v::stk,s)` by metis_tac [length_thm, EX_COM_THM]


THEN `exec [IL2_Jump (&LENGTH (il1e_to_il2 e3))] (&LENGTH
            (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
             il1e_to_il2 e2) - (&LENGTH
            (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
             il1e_to_il2 e2)), il1_il2_val v::stk, s) (1 + &LENGTH (il1e_to_il2 e3), il1_il2_val v::stk, s)` by (rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, true_value_def])

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
          il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))])
         (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
              il1e_to_il2 e2) + (1 + &LENGTH (il1e_to_il2 e3)),
          il1_il2_val v::stk,s)` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

 
THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
          il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))] ++ il1e_to_il2 e3)
         (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
              il1e_to_il2 e2)+ (1 + &LENGTH (il1e_to_il2 e3)),
          il1_il2_val v::stk,s)` by metis_tac [APPEND_TRACE_SAME_THM]

THEN fsa [length_thm, INT]

THEN `&(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1e_to_il2 e2) + 1 +
     LENGTH (il1e_to_il2 e3)) = &(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1e_to_il2 e2)) +
          (1 + &LENGTH (il1e_to_il2 e3))` by rwa []

THEN metis_tac [])


THEN1 (rw [il1e_to_il2_def]

THEN `exec (il1e_to_il2 e1) (0, stk, s) (&LENGTH (il1e_to_il2 e1), false_value::stk, s)` by metis_tac []
THEN `exec [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] (0, false_value::stk, s) (1 + &LENGTH (il1e_to_il2 e2) + 1, stk, s)` by (rw [exec_def] THEN fs [RTC_SINGLE] THEN
 rw [exec_def, Once RTC_CASES1, exec_one_cases, fetch_def, exec_instr_cases, RTC_REFL, length_thm, false_value_def]
THEN
`(exec_one [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)])^* (1 + &LENGTH (il1e_to_il2 e2) + 1, stk, s)
    (1 + &LENGTH (il1e_to_il2 e2) + 1,stk,s)` by metis_tac [RTC_REFL]
THEN
HINT_EXISTS_TAC
THEN
rwa []

THEN metis_tac [])


THEN `exec ([IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ il1e_to_il2 e2) (0, false_value::stk, s) (1 + &LENGTH (il1e_to_il2 e2) + 1, stk, s)` by metis_tac [APPEND_TRACE_SAME_THM]

THEN `exec (il1e_to_il2 e3) (0, stk, s) (&LENGTH (il1e_to_il2 e3), (il1_il2_val v)::stk, s)` by metis_tac []

THEN `exec [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] (&LENGTH (il1e_to_il2 e1) - &LENGTH (il1e_to_il2 e1),false_value::stk,s)
        (1 + &LENGTH (il1e_to_il2 e2) + 1,stk,s)` by rwa []

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)])
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1e_to_il2 e2) + 1),stk,
          s)` by (imp_res_tac EXECUTION_COMPOSE_THM THEN rwa [])

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ il1e_to_il2 e2)
         (0,stk,s)
         (&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1e_to_il2 e2) + 1),stk,
          s)` by metis_tac [APPEND_TRACE_SAME_THM]

THEN `&LENGTH (il1e_to_il2 e1) + (1 + &LENGTH (il1e_to_il2 e2) + 1) = (&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))]))` by rwa []

THEN `exec (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ il1e_to_il2 e2)
         (0,stk,s)
         ((&LENGTH (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++ il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))])),stk,
          s)` by metis_tac []

THEN `exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
          il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))]) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
              il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))]),
          stk,s)` by metis_tac [APPEND_TRACE_SAME_THM]


THEN ` exec
         (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
          il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))] ++ il1e_to_il2 e3) (0,stk,s)
         (&LENGTH
             (il1e_to_il2 e1 ++ [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
              il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))]) + &LENGTH (il1e_to_il2 e3),
          il1_il2_val v::stk,s)` by (imp_res_tac EX_COM_THM THEN rwa [])

THEN `&LENGTH
             (il1e_to_il2 e1 ++
              [IL2_Jz (&LENGTH (il1e_to_il2 e2) + 1)] ++
              il1e_to_il2 e2 ++ [IL2_Jump (&LENGTH (il1e_to_il2 e3))]) +
          &LENGTH (il1e_to_il2 e3) = &(LENGTH (il1e_to_il2 e1) + 1 + LENGTH (il1e_to_il2 e2) + 1 +
     LENGTH (il1e_to_il2 e3))` by rwa [length_thm]

THEN metis_tac []));


val EXPR_CORRECTNESS_THM = store_thm("EXPR_CORRECTNESS_THM",
``!e s v.bs_il1_expr (e, s) v ⇒
     !stk.
       exec (il1e_to_il2 e) (0,stk,s)
         (&LENGTH (il1e_to_il2 e),il1_il2_val v::stk,s)``,
metis_tac [expr_correctness_lemma, FST, SND]);

val _ = export_theory ();
