open HolKernel bossLib boolLib Parse ast_il2Theory ast_vsm0Theory lcsymtacs pairTheory finite_mapTheory pred_setTheory integerTheory smallstep_il2Theory relationTheory listTheory smallstep_vsm0Theory arithmeticTheory;

val _ = new_theory "il2_to_il3_compiler";

val get_locations_def = Define `
(get_locations [] = []) /\
(get_locations ((IL2_Store l)::stms) = l::(get_locations stms)) /\
(get_locations ((IL2_Load l)::stms) = l::(get_locations stms)) /\
(get_locations (_::stms) = get_locations stms)`;

val locs_to_map_def = Define `
(locs_to_map [] = (FEMPTY,(0:num))) /\
(locs_to_map (l::ls) = let (map, next_loc) = locs_to_map ls
                        in (if l ∈ FDOM map then (map, next_loc) else (map |+ (l, next_loc), next_loc + 1)))`;

val locs_to_map_total_thm = prove(``!P.?m n.locs_to_map P = (m, n)``,
Induct_on `P` THEN  rw [locs_to_map_def] THEN rw []);

val make_loc_map_def = Define `make_loc_map il2_prog = (locs_to_map (get_locations il2_prog))`;

val dum_lt_thm = prove(``!x y. (&x < &y) ==> (x < y)``, rw [])

val every_store_inc_in_map = prove(``!i P.(?n.(n < LENGTH P) /\ (P !! &n = IL2_Store i)) ==> i ∈ FDOM (FST (make_loc_map P))``,
Induct_on `P`
THEN rw []

THEN rw [make_loc_map_def, get_locations_def]
THEN Cases_on `n`
THEN1 (fs [fetch_def] THEN rw [] THEN rw [get_locations_def] THEN rw [locs_to_map_def] THEN Cases_on `i ∈ FDOM map` THEN rw [])

THEN `P !! &n' = IL2_Store i` by (fs [fetch_def] THEN (`&SUC n' - 1 = &n'` by fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN fs [])
THEN `n' < LENGTH P` by decide_tac
THEN res_tac
THEN fs [make_loc_map_def]

THEN Cases_on `h` THEN rw [get_locations_def] THEN rw [locs_to_map_def] THEN Cases_on `i' ∈ FDOM map` THEN fs [FST]);

val ms_il2_def = Define `ms_il2 P s = (FDOM s = FDOM (FST (make_loc_map P)))`;

val ms_il2_trans = prove(``!P r''' i v.ms_il2 P r''' /\ ms_il2 P (r''' |+ (i, v)) ==> (FDOM r''' = FDOM (r''' |+ (i, v)))``,
metis_tac [ms_il2_def]);

val ms_const = prove(``!P c c'.exec P c c' ==> ms_il2 P (SND (SND c)) ==> ms_il2 P (SND (SND c'))``,
fs [exec_def] THEN STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT

THEN rw [ms_il2_def]

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND]

THEN fs [exec_one_cases] THEN Cases_on `P !! q` THEN fs [exec_instr_cases] THEN rw []

THEN `?nq.q = &nq` by metis_tac [int_ge, NUM_POSINT_EXISTS]
THEN rw []
THEN imp_res_tac dum_lt_thm
THEN imp_res_tac every_store_inc_in_map
THEN fs [FDOM_FUPDATE]

THEN `i INSERT FDOM (FST (make_loc_map P)) = FDOM (FST (make_loc_map P))` by (rw [INSERT_DEF, EXTENSION] THEN Cases_on `x = i` THEN rw [])

THEN rw []);

val ms_const_2 = prove(``!P pc stk st pc' stk' st'.exec_one P (pc, stk, st) (pc', stk', st') ==> ms_il2 P st ==> ms_il2 P st'``, metis_tac [ms_const, SND, exec_def, RTC_SUBSET]);

val map_range_thm = prove(``!P n.((SND (make_loc_map P)) = n) ==> !x.(x ∈ FDOM (FST (make_loc_map P))) ==> ((FST (make_loc_map P)) ' x < n)``,

Induct_on `P`

THEN rw [make_loc_map_def, locs_to_map_def, get_locations_def]

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm]
THEN Cases_on `h` THEN fs [get_locations_def] THEN fs [make_loc_map_def, locs_to_map_def, get_locations_def] THEN fs [LET_DEF] THEN Cases_on `i ∈ FDOM m` THEN fs [FST, SND] THEN (TRY decide_tac) THEN rw []
THEN rw [FAPPLY_FUPDATE_THM] THEN res_tac THEN decide_tac);

val map_fun_def = Define `map_fun m = \x.m ' x`;

val map_fun_exec = prove(``!m x.map_fun m x = m ' x``, REPEAT STRIP_TAC THEN EVAL_TAC);


val make_loc_map_inj = prove(``!P.INJ (map_fun (FST (make_loc_map P))) (FDOM (FST (make_loc_map P))) UNIV``,
rw [INJ_DEF, map_fun_def, make_loc_map_def]

THEN Induct_on `P`
THEN fs [locs_to_map_def, get_locations_def]

THEN rw []
THEN Cases_on `h` THEN fs [get_locations_def]

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [locs_to_map_def] THEN fs [LET_DEF]

THEN Cases_on `i ∈ FDOM m` THEN fs [FST] THEN rw []

THEN fs [FAPPLY_FUPDATE_THM] THEN rw []

THEN TRY (Cases_on `y = i` THEN fs [] THEN rw [])

THEN TRY (`m ' y < m ' y` by metis_tac [map_range_thm, FST, SND, make_loc_map_def] THEN decide_tac)

THEN TRY (Cases_on `x = i` THEN fs [] THEN rw [])

THEN TRY (`m ' x < m ' x` by metis_tac [map_range_thm, FST, SND, make_loc_map_def] THEN decide_tac));

val map_deref_thm = prove(``!P st x. (ms_il2 P st) /\ x ∈ FDOM st ⇒ (MAP_KEYS (map_fun (FST (make_loc_map P))) st ' ((map_fun (FST (make_loc_map P))) x) = st ' x)``,
rw [] THEN metis_tac [MAP_KEYS_def, make_loc_map_inj, INJ_SUBSET, ms_il2_def]);

val il2_to_il3m_def = Define `
(il2_to_il3m m IL2_Nop = VSM_Nop) /\
(il2_to_il3m m (IL2_Push x) = VSM_Push x) /\
(il2_to_il3m m (IL2_Store x) = VSM_Store (m ' x)) /\
(il2_to_il3m m (IL2_Load x) = VSM_Load (m ' x)) /\
(il2_to_il3m m IL2_Pop = VSM_Pop) /\
(il2_to_il3m m IL2_Plus = VSM_Plus) /\
(il2_to_il3m m IL2_Geq = VSM_Geq) /\
(il2_to_il3m m IL2_Halt = VSM_Halt) /\
(il2_to_il3m m (IL2_Jump n) = (VSM_Jump n)) /\
(il2_to_il3m m (IL2_Jz n) = VSM_Jz n)`;

val (exec_il3_instr_rules, exec_il3_instr_ind, exec_il3_instr_cases) = Hol_reln `
(!pc stk st.exec_il3_instr VSM_Nop (pc, stk, st) (pc+1, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Push n) (pc, stk, st) (pc+1, n::stk, st)) /\
(!l pc stk st.l ∈ FDOM st ==> exec_il3_instr (VSM_Load l) (pc, stk, st) (pc+1, (st ' l)::stk, st)) /\
(!l pc v stk st.exec_il3_instr (VSM_Store l) (pc, v::stk, st) (pc+1, stk, st |+ (l, v))) /\
(!pc v stk st.exec_il3_instr VSM_Pop (pc, v::stk, st) (pc+1, stk, st)) /\
(!pc v1 v2 stk st.exec_il3_instr VSM_Plus (pc, v1::v2::stk, st) (pc+1, (v1+v2)::stk, st)) /\
(!pc stk st.exec_il3_instr VSM_Halt (pc, stk, st) (pc, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Jump n) (pc, stk, st) (pc + 1 + n, stk, st)) /\
(!n pc stk st.exec_il3_instr (VSM_Jz n) (pc, 0::stk, st) (pc + 1 + n, stk, st)) /\
(!n pc t stk st.(t <> 0) ==> exec_il3_instr (VSM_Jz n) (pc, t::stk, st) (pc + 1, stk, st)) /\
(!v1 v2 pc stk st.(v1 >= v2) ==> exec_il3_instr (VSM_Geq) (pc, v1::v2::stk, st) (pc + 1, true_value::stk, st)) /\
(!v1 v2 pc stk st.(v1 < v2) ==> exec_il3_instr (VSM_Geq) (pc, v1::v2::stk, st) (pc + 1, false_value::stk, st))`;

val map_fetch_thm = prove(``!f xs n.(n < LENGTH xs) ==> ((MAP f xs) !! (&n) = f (xs !! (&n)))``,
Induct_on `xs`
THEN1 rw [LENGTH]

THEN rw []

THEN rw [fetch_def]

THEN Cases_on `n` THEN1 metis_tac []
THEN `n' < LENGTH xs` by DECIDE_TAC
THEN ` MAP f xs !! &n' = f (xs !! &n')` by metis_tac []
THEN rw [int_of_num]

THEN rw [INT_1]
THEN rw [int_sub]
THEN REWRITE_TAC [GSYM INT_ADD_ASSOC]
THEN REWRITE_TAC [Once INT_ADD_SYM]
THEN rw [INT_ADD_LINV]);

val (exec_il3_one_rules, exec_il3_one_ind, exec_il3_one_cases) = Hol_reln `
!instrs pc stk st pc' stk' st'.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_il3_instr (instrs !! pc) (pc, stk, st) (pc', stk', st')))
    ==> exec_il3_one instrs (pc, stk, st) (pc', stk', st')`;

val exec_il3_def = Define `exec_il3 P c c' = (exec_il3_one P)^* c c'`;

val il3_eql_il2 = prove(``!P c c'. exec P c c' ==> (ms_il2 P (SND (SND c))) ==> exec_il3 (MAP (il2_to_il3m (FST (make_loc_map P))) P) (FST c, FST (SND c), MAP_KEYS (map_fun (FST (make_loc_map P))) (SND (SND c))) (FST c', FST (SND c'), MAP_KEYS (map_fun (FST (make_loc_map P))) (SND (SND c')))``, 
STRIP_TAC
THEN fs [exec_def]
THEN ho_match_mp_tac RTC_STRONG_INDUCT
THEN rw []

THEN rw [exec_il3_def]

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND]

THEN rw [exec_il3_def]
THEN rw [Once RTC_CASES1]
THEN DISJ2_TAC
THEN `ms_il2 P r` by metis_tac [ms_const_2, SND, exec_def, RTC_SUBSET]
THEN fs [exec_il3_def]
THEN HINT_EXISTS_TAC
THEN rw []
THEN rw [exec_il3_one_cases] THEN fs [exec_one_cases]
THEN fs [int_ge]
THEN rw []

THEN Cases_on `P !! q` THEN fs [exec_instr_cases] THEN rw []

THEN (TRY (
`?nq.q = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [dum_lt_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]
THEN rw [exec_il3_instr_cases]
THEN FAIL_TAC "fail"
))

THEN (TRY (
`?nq.pc' = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [dum_lt_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]
THEN rw [exec_il3_instr_cases]
THEN FAIL_TAC "fail"
))

THEN (TRY (`?nq.q = &nq` by rw [NUM_POSINT_EXISTS, int_ge]
THEN rw []
THEN `nq < LENGTH P` by rw [dum_lt_thm]

THEN rw [map_fetch_thm]

THEN rw [il2_to_il3m_def]


THEN rw [exec_il3_instr_cases]

THEN `(FST (make_loc_map P) ' i) = map_fun (FST (make_loc_map P)) i` by metis_tac [map_fun_def]

THEN fs []
THEN imp_res_tac ms_il2_trans
THEN rw []

THEN TRY (match_mp_tac MAP_KEYS_FUPDATE
THEN fs [FDOM_FUPDATE]
THEN ` i INSERT FDOM r''' = FDOM r'''` by metis_tac []
THEN fs [])

THEN rw [MAP_KEYS_def]

THEN metis_tac [MAP_KEYS_FUPDATE, make_loc_map_inj, INJ_SUBSET, ms_il2_def, map_fun_def, ms_il2_trans, map_deref_thm, map_fun_def, MAP_KEYS_def, map_fun_def])))

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



val fetch_append_thm = store_thm("fetch_append_thm",
``!i xs ys.(&0 <= i) ==> ((xs ++ ys) !! i = (if i < &LENGTH xs then xs !! i else ys !! (i - &LENGTH xs)))``,
Induct_on `xs` THEN rw []

THEN1 metis_tac [int_le]

THEN1 (Cases_on `i = 0` THEN rw [APPEND, fetch_def]

THEN `xs ++ ys !! (i-1) = xs !! (i-1)` by (`0 <= (i-1)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN `i - 1 < &LENGTH xs` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN metis_tac []))

THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT_NOT_LT]

THEN `~(i-1 < &LENGTH xs)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) []
THEN `xs ++ ys !! (i-1) = ys !! (i-1) - &LENGTH xs` by (full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [])

THEN Cases_on `i = 0` THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [APPEND, fetch_def] THEN rw []
THEN full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT]
THEN `i - 1 - &LENGTH xs = i - (&LENGTH xs + 1)` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [INT, INT_SUB_LNEG, INT_ADD_COMM]
THEN rw []);


val FETCH_EL = prove(``!xs n.n < LENGTH xs ==> (xs !! &n = EL n xs)``,
Induct_on `n`

THEN1 (rw [fetch_def] THEN Cases_on `xs` THEN fs [LENGTH, fetch_def])
THEN rw [fetch_def]
THEN rw [EL] THEN Cases_on `xs` THEN fs [LENGTH] THEN res_tac THEN rw [fetch_def] THEN `&SUC n - 1 = &n` by (fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN rw []);

val fb_cons_thm = prove(``!l v stk.l < LENGTH stk ==> ((stk ?? l) = (v::stk ?? l))``,
rw [fetch_rev_def] THEN
`l < LENGTH (REVERSE stk)` by metis_tac [LENGTH_REVERSE] THEN rw [fetch_append_thm]);

val fb_append_thm = prove(``!l stk1 stk2.l < LENGTH stk2 ==> ((stk2 ?? l) = (stk1 ++ stk2 ?? l))``,
rw [fetch_rev_def] THEN `l < LENGTH (REVERSE stk2)` by metis_tac [LENGTH_REVERSE] THEN rw [REVERSE_APPEND, fetch_append_thm]);


val stack_contains_store_def = Define `
stack_contains_store st stk = !l.l ∈ FDOM st ==> (l < LENGTH stk) /\ (stk ?? l = st ' l)
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

val drop_thm = prove(``!xs ys.DROP (LENGTH xs) (xs ++ ys) = ys``,
Induct_on `xs` THEN rw []);

val take_thm = prove(``!xs ys.TAKE (LENGTH xs) (xs ++ ys) = xs``,
Induct_on `xs` THEN rw []);

val vsm_2_lemma = prove(``!P pc stk st pc' stk' st' stkst stkst'.
stack_contains_store st stkst /\
up_stack (P !! pc) stk stkst stkst' /\
exec_il3_one P (pc, stk, st) (pc', stk', st')
==> vsm_exec_one P (pc, stk ++ stkst) (pc', stk' ++ stkst') /\
stack_contains_store st' stkst'``,
metis_tac [cexec_step_thm, vsm_lemma]);


val s_uloc_def = Define `(s_uloc [] = 0) /\ (s_uloc (VSM_Load l::xs) = MAX (l + 1) (s_uloc xs)) /\ (s_uloc (VSM_Store l::xs) = MAX (l+1) (s_uloc xs)) /\ (s_uloc (_::xs) = s_uloc xs)`;

val suloc_thm = prove(``!P q n.(q < LENGTH P) /\ (P !! &q = VSM_Store n) ==> (n < s_uloc P)``,
Induct_on `q` THEN rw [] THEN rfs [FETCH_EL] THEN (Cases_on `P` THEN1 (fs [LENGTH]))
THEN1 (fs [] THEN rw [s_uloc_def])
THEN
Cases_on `h` THEN fs [EL, s_uloc_def] THEN rw [] THEN fs [] THEN rw [] THEN res_tac THEN fs [FETCH_EL]);

val suloc_2_thm = prove(``!P c c'.exec_il3 P c c' ==> (!l.l ∈ FDOM (SND (SND c)) <=> l < s_uloc P) ==> (!l.l ∈ FDOM (SND (SND c')) <=> l < s_uloc P)``,
STRIP_TAC THEN fs [exec_il3_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r`  THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND] THEN rw []

THEN fs [exec_il3_one_cases] THEN Cases_on `P !! q` THEN fs [exec_il3_instr_cases] THEN rw []
THEN `?nq.q = &nq` by metis_tac [NUM_POSINT_EXISTS, int_ge] THEN rw []
THEN imp_res_tac suloc_thm
THEN fs [dum_lt_thm] THEN rfs []
THEN `!l. (l = n) ==> (l < s_uloc P)` by metis_tac []
THEN `!l. l ∈ FDOM r' ⇔ l < s_uloc P` by metis_tac [EQ_IMP_THM]
THEN metis_tac []);

val suloc_21_thm = prove(``!P pc stk st pc' stk' st'.exec_il3 P (pc, stk, st) (pc', stk', st') /\ (!l.l ∈ FDOM st <=> l < s_uloc P) ==> (!l.l ∈ FDOM st' <=> l < s_uloc P)``,
rw []
THEN mp_tac suloc_2_thm
THEN rw []
THEN res_tac
THEN fs [SND]);

val astack_def = Define `astack P st stk = stk ++ (REVERSE (GENLIST (\l.st ' l) (s_uloc P)))`;

val astack_produces_valid_store = prove(``!P st stk.(!l.l ∈ FDOM st <=> l < s_uloc P) ==> ?n.(stk = TAKE n (astack P st stk)) /\ stack_contains_store st (DROP n (astack P st stk))``,

rw [astack_def]
THEN EXISTS_TAC ``(LENGTH stk)`` THEN
rw [take_thm, drop_thm, stack_contains_store_def, fetch_rev_def, FETCH_EL, LESS_EQ_IMP_LESS_SUC]);


val exec_il3_imp_vsm_exec = prove(``!P c c'.exec_il3 P c c' ==> !n astk.(FST (SND c) = TAKE n astk) /\ stack_contains_store (SND (SND c)) (DROP n astk) /\ (!l.l ∈ FDOM (SND (SND c)) <=> l < s_uloc P) ==> 
    ?n' astk'.vsm_exec P (FST c, astk) (FST c', astk') /\ (FST (SND c') = TAKE n' astk') /\ stack_contains_store (SND (SND c')) (DROP n' astk')``,
STRIP_TAC THEN fs [exec_il3_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []

THEN1 (Cases_on `c` THEN Cases_on `r` THEN fs [FST, SND] THEN rw [] THEN metis_tac [vsm_exec_def, RTC_REFL])

THEN Cases_on `c` THEN Cases_on `c'` THEN Cases_on `c''` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND] THEN rw []



THEN rw [vsm_exec_def]

THEN `?stkst'. up_stack (P !! q) (TAKE n astk) (DROP n astk) stkst'` by (

Cases_on `P !! q` THEN rw [up_stack_cases]

THEN fs [stack_contains_store_def]


THEN `n' ∈ FDOM r'''` by (`?nq.(q = &nq)` by fs [exec_il3_one_cases, NUM_POSINT_EXISTS, int_ge, dum_lt_thm] THEN rw []
THEN `nq < LENGTH P` by fs [dum_lt_thm, exec_il3_one_cases]
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


val vsm_exec_correctness_thm = prove(``!P pc stk st pc' stk' st'.exec_il3 P (pc, stk, st) (pc', stk', st') /\
(!l.l ∈ FDOM st <=> l < s_uloc P)
==> 
?n astk.vsm_exec P (pc, astack P st stk) (pc', astk) /\ (stk' = TAKE n astk)``,

metis_tac [FST, SND, exec_il3_imp_vsm_exec, astack_produces_valid_store]);

val il2_to_il3_def = Define `il2_to_il3 P = MAP (il2_to_il3m (FST (make_loc_map P))) P`;

val nice_il3_eql_il2 = prove(``!P pc stk st pc' stk' st'.exec P (pc, stk, st) (pc', stk', st') /\ ms_il2 P st ==>
exec_il3 (il2_to_il3 P) (pc, stk, MAP_KEYS (map_fun (FST (make_loc_map P))) st)
(pc', stk', MAP_KEYS (map_fun (FST (make_loc_map P))) st')``,
metis_tac [il3_eql_il2, FST, SND, il2_to_il3_def]);

val il2_vsm_correctness = store_thm("il2_vsm_correctness",``
!P pc stk st pc' stk' st'.
exec P (pc, stk, st) (pc', stk', st') /\ ms_il2 P st ==>

?n astk.vsm_exec (il2_to_il3 P) (pc, astack (il2_to_il3 P) (MAP_KEYS (map_fun (FST (make_loc_map P))) st) stk) (pc', astk) /\ (stk' = TAKE n astk)``,

rw []
THEN imp_res_tac nice_il3_eql_il2

THEN `ms_il2 P st ==> (!l.l ∈ FDOM (MAP_KEYS (map_fun (FST (make_loc_map P))) st) <=> (l < s_uloc (il2_to_il3 P)))` by cheat

THEN imp_res_tac vsm_exec_correctness_thm
THEN rfs []
THEN metis_tac []);

val _ = export_theory ();
