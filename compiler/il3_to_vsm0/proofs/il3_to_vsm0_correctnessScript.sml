open HolKernel boolLib bossLib ast_vsm0Theory relationTheory pairTheory listTheory finite_mapTheory lcsymtacs il3_store_propertiesTheory smallstep_il2Theory smallstep_vsm0Theory smallstep_il3Theory il2_il3_correctnessTheory integerTheory;


val _ = new_theory "il3_to_vsm0_correctness";


val fb_cons_thm = prove(``!l v stk.l < LENGTH stk ==> ((stk ?? l) = (v::stk ?? l))``,
rw [fetch_rev_def] THEN
`l < LENGTH (REVERSE stk)` by metis_tac [LENGTH_REVERSE] THEN rw [fetch_append_thm]);

val fb_append_thm = prove(``!l stk1 stk2.l < LENGTH stk2 ==> ((stk2 ?? l) = (stk1 ++ stk2 ?? l))``,
rw [fetch_rev_def] THEN `l < LENGTH (REVERSE stk2)` by metis_tac [LENGTH_REVERSE] THEN rw [REVERSE_APPEND, fetch_append_thm]);


val (up_stack_rules, up_stack_ind, up_stack_cases) = Hol_reln `
(!l stk' v stk.(l < LENGTH stk') ==> up_stack (VSM_Store l) (v::stk) stk' (update_loc stk' l v)) /\
(!stk'.up_stack VSM_Nop _ stk' stk') /\
(!stk' n.up_stack (VSM_Push n) _ stk' stk') /\
(!stk' l.up_stack (VSM_Load l) _ stk' stk') /\
(!stk'.up_stack VSM_Pop _ stk' stk') /\
(!stk'.up_stack VSM_Plus _ stk' stk') /\
(!stk'.up_stack VSM_Geq _ stk' stk') /\
(!stk'.up_stack VSM_Halt _ stk' stk') /\
(!stk' off.up_stack (VSM_Jump off) _ stk' stk') /\
(!stk' off.up_stack (VSM_Jz off) _ stk' stk')
`;

val (c_exec_il3_one_rules, c_exec_il3_one_ind, c_exec_il3_one_cases) = Hol_reln `
exec_il3_one P (pc, stk, st) (pc', stk', st') /\ (up_stack (P !! pc) stk stk' stk'') ==> c_exec_il3_one P (pc, stk, st) (pc', stk'', st')
`;


val cexec_step_thm = prove(``
!P pc stk st pc' stk' st' stkst stkst'.
    stack_contains_store st stkst /\
    up_stack (P !! pc) stk stkst stkst' /\
    exec_il3_one P (pc, stk, st) (pc', stk', st')
==> c_exec_il3_one P (pc, stk ++ stkst, st) (pc', stk' ++ stkst', st') /\ stack_contains_store st' stkst'``,

rw [c_exec_il3_one_cases]

THEN1 (`  exec_il3_one P (pc,stk ++ stkst,st) (pc',stk' ++ stkst,st') ∧
  up_stack (P !! pc) (stk ++ stkst) (stk' ++ stkst) (stk' ++ stkst')` by (fs [exec_il3_one_cases]
THEN Cases_on `P !! pc` THEN fs [exec_il3_instr_cases, up_stack_cases] THEN rw []

THEN rw [update_loc_def]

THEN rw [lupdate_append]

THEN decide_tac)

THEN metis_tac [])


THEN Cases_on `P !! pc` THEN fs [exec_il3_one_cases, exec_il3_instr_cases, up_stack_cases] THEN rw []

THEN fs [stack_contains_store_def] THEN rw []

THEN (TRY (rw [update_loc_def, LUPDATE_LENGTH] THEN FAIL_TAC "fail"))

THEN rw [update_loc_def, fetch_rev_def]

THEN1 (`l < LENGTH (REVERSE stkst)` by metis_tac [LENGTH_REVERSE]
THEN rw [FETCH_EL]
THEN rw [EL_LUPDATE])

THEN res_tac
THEN `n < LENGTH (REVERSE stkst)` by metis_tac [LENGTH_REVERSE]
THEN `l < LENGTH (REVERSE stkst)` by metis_tac [LENGTH_REVERSE]

THEN fs [update_loc_def, fetch_rev_def, FETCH_EL]
THEN rw [EL_LUPDATE, FAPPLY_FUPDATE_THM]);

val vsm_lemma = prove(``!P pc stk st pc' stk' st' stkst stkst'.
    stack_contains_store st stkst /\
    c_exec_il3_one P (pc, stk ++ stkst, st) (pc', stk' ++ stkst', st') ==>
    vsm_exec_one P (pc, stk ++ stkst) (pc', stk' ++ stkst')``,

rw [c_exec_il3_one_cases] THEN fs [exec_il3_one_cases] THEN rw [vsm_exec_one_cases] THEN Cases_on `P !! pc` THEN fs [exec_il3_instr_cases, vsm_exec_instr_cases, up_stack_cases, stack_contains_store_def] THEN rw [] THEN fs [GSYM fb_append_thm, update_loc_def, fetch_rev_def]);

val vsm_2_lemma = prove(``!P pc stk st pc' stk' st' stkst stkst'.
stack_contains_store st stkst /\
up_stack (P !! pc) stk stkst stkst' /\
exec_il3_one P (pc, stk, st) (pc', stk', st')
==> vsm_exec_one P (pc, stk ++ stkst) (pc', stk' ++ stkst') /\
stack_contains_store st' stkst'``,
metis_tac [cexec_step_thm, vsm_lemma]);

val exec_il3_imp_vsm_exec = prove(``!P c c'.exec_il3 P c c' ==> !n astk.(FST (SND c) = TAKE n astk) /\ stack_contains_store (SND (SND c)) (DROP n astk) /\ (!l.l ∈ FDOM (SND (SND c)) <=> l < s_uloc P) ==> 
    ?n' astk'.vsm_exec P (FST c, astk) (FST c', astk') /\ (FST (SND c') = TAKE n' astk') /\ stack_contains_store (SND (SND c')) (DROP n' astk')``,
STRIP_TAC THEN fs [exec_il3_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN1 (Cases_on `c` THEN Cases_on `r` THEN fs [FST, SND] THEN rw [] THEN metis_tac [vsm_exec_def, RTC_REFL])

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND] THEN rw []



THEN rw [vsm_exec_def]

THEN `?stkst'. up_stack (P !! q) (TAKE n astk) (DROP n astk) stkst'` by (

Cases_on `P !! q` THEN rw [up_stack_cases]

THEN fs [stack_contains_store_def]


THEN `n' ∈ FDOM r'''` by (`?nq.(q = &nq)` by fs [exec_il3_one_cases, NUM_POSINT_EXISTS, int_ge, int_monotonic_thm] THEN rw []
THEN `nq < LENGTH P` by fs [int_monotonic_thm, exec_il3_one_cases]
THEN `n' < s_uloc P` by metis_tac [suloc_thm] THEN  metis_tac [])

THEN res_tac
THEN rw []

THEN Cases_on `TAKE n astk`

THEN1 fs [exec_il3_one_cases, exec_il3_instr_cases]

THEN metis_tac [])

THEN imp_res_tac vsm_2_lemma

THEN fs [TAKE_DROP]

THEN `stack_contains_store r (DROP (LENGTH q'''') (q'''' ++ stkst'))` by rw [drop_thm]
THEN `q'''' = TAKE (LENGTH q'''') (q'''' ++ stkst')` by rw [take_thm]

THEN res_tac THEN rw []

THEN rw [Once RTC_CASES1]

THEN fs [vsm_exec_def]

THEN `(∀l. l ∈ FDOM r ⇔ l < s_uloc P)` by (
match_mp_tac suloc_21_thm

THEN rw [exec_il3_def]
THEN metis_tac [RTC_SUBSET])

THEN fs [drop_thm, take_thm]
THEN rw []

THEN metis_tac []);

val vsm_exec_correctness_thm = store_thm("vsm_exec_correctness_thm", ``!P pc stk st pc' stk' st'.exec_il3 P (pc, stk, st) (pc', stk', st') /\
(!l.l ∈ FDOM st <=> l < s_uloc P)
==> 
?n astk.vsm_exec P (pc, astack P st stk) (pc', astk) /\ (stk' = TAKE n astk)``,

metis_tac [FST, SND, exec_il3_imp_vsm_exec, astack_produces_valid_store]);

val _ = export_theory ();
