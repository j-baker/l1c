open HolKernel boolLib bossLib ast_vsm0Theory relationTheory pairTheory listTheory finite_mapTheory lcsymtacs il3_store_propertiesTheory smallstep_il2Theory smallstep_vsm0Theory smallstep_il3Theory smallstep_il3_clockedTheory il2_il3_correctnessTheory integerTheory smallstep_vsm0_clockedTheory


val _ = new_theory "il3_to_vsm0_correctness"


val fb_cons_thm = prove(``!l v stk.l < LENGTH stk ==> ((stk ?? l) = (v::stk ?? l))``,
rw [fetch_rev_def] THEN
`l < LENGTH (REVERSE stk)` by metis_tac [LENGTH_REVERSE] THEN rw [fetch_append_thm])

val fb_append_thm = prove(``!l stk1 stk2.l < LENGTH stk2 ==> ((stk2 ?? l) = (stk1 ++ stk2 ?? l))``,
rw [fetch_rev_def] THEN `l < LENGTH (REVERSE stk2)` by metis_tac [LENGTH_REVERSE] THEN rw [REVERSE_APPEND, fetch_append_thm])


val (up_stack_rules, up_stack_ind, up_stack_cases) = Hol_reln `
(!l stk' v stk.(l < LENGTH stk') ==> up_stack (VSM_Store l) (v::stk) stk' (update_loc stk' l v)) /\
(!stk'.up_stack VSM_Nop _ stk' stk') /\
(!stk'.up_stack VSM_Tick _ stk' stk') /\
(!stk' n.up_stack (VSM_Push n) _ stk' stk') /\
(!stk' l.up_stack (VSM_Load l) _ stk' stk') /\
(!stk'.up_stack VSM_Pop _ stk' stk') /\
(!stk'.up_stack VSM_Plus _ stk' stk') /\
(!stk'.up_stack VSM_Geq _ stk' stk') /\
(!stk'.up_stack VSM_Halt _ stk' stk') /\
(!stk' off.up_stack (VSM_Jump off) _ stk' stk') /\
(!stk' off.up_stack (VSM_Jz off) _ stk' stk')
`

val (c_exec_il3_one_rules, c_exec_il3_one_ind, c_exec_il3_one_cases) = Hol_reln `
exec_il3_c_one P (SOME (pc, c, stk, st)) (SOME (pc', c', stk', st')) /\ (up_stack (P !! pc) stk stk' stk'') ==> c_exec_il3_one P (SOME (pc, c, stk, st)) (SOME (pc', c', stk'', st'))
`


val cexec_step_thm = prove(``
!P pc c stk st pc' c' stk' st' stkst stkst'.
    stack_contains_store st stkst /\
    up_stack (P !! pc) stk stkst stkst' /\
    exec_il3_c_one P (SOME (pc, c, stk, st)) (SOME (pc', c', stk', st'))
==> c_exec_il3_one P (SOME (pc, c, stk ++ stkst, st)) (SOME (pc', c', stk' ++ stkst', st')) /\ stack_contains_store st' stkst'``,

rw [c_exec_il3_one_cases]

THENL [Q.EXISTS_TAC `stk' ++ stkst`, all_tac] THEN rw [] THEN Cases_on `P !! pc` THEN fs [exec_il3_c_one_cases, exec_il3_c_instr_cases, up_stack_cases] THEN rw [] THEN fs [stack_contains_store_def] THEN rw [update_loc_def, LUPDATE_LENGTH, lupdate_append, LENGTH_REVERSE] THEN rw [] THEN1 decide_tac

THEN fs [fetch_rev_def, FETCH_EL, EL_LUPDATE, LENGTH_REVERSE, FAPPLY_FUPDATE_THM] THEN Cases_on `l = n` THEN rw [] THEN metis_tac [FETCH_EL, LENGTH_REVERSE])

val vsm_lemma = prove(``!P pc c stk st stkst x.
    stack_contains_store st stkst /\
    c_exec_il3_one P (SOME (pc, c, stk ++ stkst, st)) x
==> (!pc' c' stk' stkst' st'.(x = SOME (pc', c', stk' ++ stkst', st')) ==> vsm_exec_c_one P (SOME (pc, c, stk ++ stkst)) (SOME (pc', c', stk' ++ stkst'))) /\ ((x = NONE) ==> vsm_exec_c_one P (SOME (pc, c, stk ++ stkst)) NONE)``,
rw [c_exec_il3_one_cases] THEN fs [exec_il3_c_one_cases] THEN rw [vsm_exec_c_one_cases] THEN Cases_on `P !! pc` THEN fs [exec_il3_c_instr_cases, vsm_exec_c_instr_cases, up_stack_cases, stack_contains_store_def] THEN rw [] THEN fs [GSYM fb_append_thm, update_loc_def, fetch_rev_def])

val vsm_2_lemma = prove(``!P pc c stk st pc' c' stk' st' stkst stkst'.
stack_contains_store st stkst /\
up_stack (P !! pc) stk stkst stkst' /\
exec_il3_c_one P (SOME (pc, c, stk, st)) (SOME (pc', c', stk', st'))
==> vsm_exec_c_one P (SOME (pc, c, stk ++ stkst)) (SOME (pc', c', stk' ++ stkst')) /\
stack_contains_store st' stkst'``,
rw [] THEN imp_res_tac cexec_step_thm THEN metis_tac [vsm_lemma] )

val take_thm = prove(``!a b.TAKE (LENGTH a) (a ++ b) = a``, Induct_on `a` THEN rw [LENGTH, TAKE_def])
val drop_thm = prove(``!a b.DROP (LENGTH a) (a ++ b) = b``, Induct_on `a` THEN rw [LENGTH, DROP_def])

val exec_il3_imp_vsm_exec = prove(``!P c c'.exec_il3_c P c c' ==> !x n astk.(c = SOME x) /\ (FST (SND (SND x)) = TAKE n astk) /\ stack_contains_store (SND (SND (SND x))) (DROP n astk) /\ (!l.l ∈ FDOM (SND (SND (SND x))) <=> l < s_uloc P) ==> 
((c' = NONE) /\ vsm_exec_c P (SOME (FST x, FST (SND x), astk)) NONE) \/ (?x'.(c' = SOME x') /\ ?n' astk'.vsm_exec_c P (SOME (FST x, FST (SND x), astk)) (SOME (FST x', FST (SND x'), astk')) /\ (FST (SND (SND x')) = TAKE n' astk') /\ stack_contains_store (SND (SND (SND x'))) (DROP n' astk'))``,
STRIP_TAC THEN fs [exec_il3_c_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []
THEN1
(Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [FST, SND] THEN Q.LIST_EXISTS_TAC [`n`, `astk`] THEN rw [] THEN metis_tac [vsm_exec_c_def, RTC_REFL])

THEN Cases_on `c''` THEN1 (rw [] THEN Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [FST, SND] THEN Cases_on `c'` THEN1 (fs [exec_il3_c_one_cases, vsm_exec_c_def] THEN match_mp_tac RTC_SUBSET THEN Cases_on `P !! q` THEN fs [vsm_exec_c_one_cases, exec_il3_c_instr_cases, vsm_exec_c_instr_cases] THEN rw [])

THEN fs [] THEN Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND, vsm_exec_c_def] 
THEN rw [Once RTC_CASES1]

THEN `?stkst'. up_stack (P !! q) (TAKE n astk) (DROP n astk) stkst'` by (
Cases_on `P!!q` THEN rw [up_stack_cases]

THEN Cases_on `astk` THEN Cases_on `n` THEN fs [TAKE_def] THEN (TRY ((fs [exec_il3_c_one_cases, exec_il3_c_instr_cases]) THEN FAIL_TAC ""))

THEN fs [stack_contains_store_def] THEN fs [exec_il3_c_one_cases] THEN `?nq.q = &nq` by metis_tac [int_ge, NUM_POSINT_EXISTS] THEN rw [] THEN imp_res_tac int_monotonic_thm THEN metis_tac [suloc_thm])


THEN Q.EXISTS_TAC `SOME (q''', q'''', q''''' ++ stkst')` THEN rw []
THEN  metis_tac [TAKE_DROP, suloc_21_thm, exec_il3_c_def, RTC_SUBSET, take_thm, drop_thm, vsm_2_lemma])

THEN fs [] THEN Cases_on `x'` THEN Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r` THEN Cases_on `r''` THEN Cases_on `r'` THEN fs [FST, SND]

THEN Cases_on `c'` THEN1 (imp_res_tac RTC_CASES1 THEN rw [] THEN fs [exec_il3_c_one_cases]) THEN Cases_on `x` THEN Cases_on `r'` THEN Cases_on `r'''` THEN fs [FST, SND, vsm_exec_c_def]

THEN `(∀l. l ∈ FDOM r' ⇔ l < s_uloc P)` by metis_tac [suloc_21_thm, exec_il3_c_def, RTC_SUBSET] THEN fs []

THEN `?stkst'. up_stack (P !! q') (TAKE n astk) (DROP n astk) stkst'` by (
(Cases_on `P!!q'` THEN rw [up_stack_cases])

THEN Cases_on `astk` THEN Cases_on `n` THEN fs [TAKE_def] THEN (TRY ((fs [exec_il3_c_one_cases, exec_il3_c_instr_cases]) THEN FAIL_TAC ""))

THEN fs [stack_contains_store_def] THEN fs [exec_il3_c_one_cases] THEN `?nq.q' = &nq` by metis_tac [int_ge, NUM_POSINT_EXISTS] THEN rw [] THEN imp_res_tac int_monotonic_thm THEN metis_tac [suloc_thm])

THEN `stack_contains_store r' (DROP (LENGTH q'''''''') (q'''''''' ++ stkst'))` by (imp_res_tac vsm_2_lemma THEN metis_tac [drop_thm])
THEN `q'''''''' = TAKE (LENGTH q'''''''') (q'''''''' ++ stkst')` by metis_tac [take_thm] THEN res_tac THEN rw []

THEN Q.LIST_EXISTS_TAC [`n'''`, `astk'''`] THEN rw [] THEN rw [Once RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `SOME (q'''''', q''''''', q'''''''' ++ stkst')` THEN rw []

THEN metis_tac [vsm_2_lemma, TAKE_DROP])

val vsm_exec_correctness_1_thm = store_thm("vsm_exec_correctness_1_thm", ``!P pc c stk st.exec_il3_c P (SOME (pc, c, stk, st)) NONE /\ (!l.l ∈ FDOM st <=> l < s_uloc P) ==> vsm_exec_c P (SOME (pc, c, astack P st stk)) NONE``, rw [] THEN imp_res_tac exec_il3_imp_vsm_exec THEN fs [FST, SND, exec_il3_imp_vsm_exec, astack_produces_valid_store])

val vsm_exec_correctness_2_thm = store_thm("vsm_exec_correctness_2_thm", ``!P pc c stk st pc' c' stk' st'.exec_il3_c P (SOME (pc, c, stk, st)) (SOME (pc', c', stk', st')) /\ (!l.l ∈ FDOM st <=> l < s_uloc P) ==> ?n astk.vsm_exec_c P (SOME (pc, c, astack P st stk)) (SOME (pc', c', astk)) /\ (stk' = TAKE n astk)``, rw [] THEN imp_res_tac exec_il3_imp_vsm_exec THEN fs [FST, SND, exec_il3_imp_vsm_exec, astack_produces_valid_store] THEN metis_tac [FST, SND, exec_il3_imp_vsm_exec, astack_produces_valid_store])

val _ = export_theory ()
