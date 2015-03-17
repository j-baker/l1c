open HolKernel boolLib bossLib lcsymtacs il2_to_il3_compilerTheory pred_setTheory finite_mapTheory listTheory pairTheory integerTheory smallstep_il2Theory relationTheory smallstep_il3Theory arithmeticTheory smallstep_vsm0Theory smallstep_il3_clockedTheory smallstep_il2_clockedTheory;

val _ = new_theory "il3_store_properties";

val locs_to_map_total_thm = store_thm("locs_to_map_total_thm", ``!P.?m n.locs_to_map P = (m, n)``,
Induct_on `P` THEN  rw [locs_to_map_def] THEN rw []);

val map_range_thm = prove(``!P n.((SND (make_loc_map P)) = n) ==> !x.(x ∈ FDOM (FST (make_loc_map P))) ==> ((FST (make_loc_map P)) ' x < n)``,
rw [EQ_IMP_THM]

THEN1 (Induct_on `P`

THEN rw [make_loc_map_def, locs_to_map_def, get_locations_def]

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm]
THEN Cases_on `h` THEN fs [get_locations_def] THEN fs [make_loc_map_def, locs_to_map_def, get_locations_def] THEN fs [LET_DEF] THEN Cases_on `i ∈ FDOM m` THEN fs [FST, SND] THEN (TRY decide_tac) THEN rw []
THEN rw [FAPPLY_FUPDATE_THM] THEN res_tac THEN decide_tac));

val map_range_2_thm = prove(``!P x.x < (SND (make_loc_map P)) ==> ?k.k ∈ FDOM (FST (make_loc_map P)) /\ ((FST (make_loc_map P)) ' k = x)``,


Induct_on `P` THEN rw [make_loc_map_def, locs_to_map_def, get_locations_def] THEN Cases_on `h` THEN fs [get_locations_def] THEN fs [locs_to_map_def, make_loc_map_def, get_locations_def]

THEN `?map next_loc.locs_to_map (get_locations P) = (map, next_loc)` by metis_tac [locs_to_map_total_thm]
THEN fs [LET_DEF] THEN rw [] THEN fs []

THEN Cases_on `k = i` THEN REWRITE_TAC [FAPPLY_FUPDATE_THM]

THEN (Cases_on `x = next_loc` THEN fs [] THEN1 metis_tac  [FAPPLY_FUPDATE_THM] THEN `x < next_loc` by decide_tac THEN res_tac THEN metis_tac [map_range_thm]));

val map_fun_def = Define `map_fun m = \x.m ' x`;

val map_fun_exec = prove(``!m x.map_fun m x = m ' x``, REPEAT STRIP_TAC THEN EVAL_TAC);


val make_loc_map_inj = store_thm("make_loc_map_inj", ``!P.INJ (map_fun (FST (make_loc_map P))) (FDOM (FST (make_loc_map P))) UNIV``,
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

val ms_il2_def = Define `ms_il2 P s = (FDOM s = FDOM (FST (make_loc_map P)))`;

val map_deref_thm = store_thm("map_deref_thm", ``!P st x. (ms_il2 P st) /\ x ∈ FDOM st ⇒ (MAP_KEYS (map_fun (FST (make_loc_map P))) st ' ((map_fun (FST (make_loc_map P))) x) = st ' x)``,
rw [] THEN metis_tac [MAP_KEYS_def, make_loc_map_inj, INJ_SUBSET, ms_il2_def]);

val int_monotonic_thm = store_thm("int_monotonic_thm",``!x y. (&x < &y) ==> (x < y)``, rw []);

val every_store_inc_in_map = prove(``!i P n.((n < LENGTH P) /\ ((P !! &n = IL2_Store i) \/ (P !! &n = IL2_Load i))) ==> i ∈ FDOM (FST (make_loc_map P))``,
Induct_on `P`
THEN rw []

THEN rw [make_loc_map_def, get_locations_def]

THEN Cases_on `h` THEN fs [get_locations_def]

THEN (TRY (Cases_on `n` THEN fs [fetch_def] THEN rw []

THEN fs [make_loc_map_def]

THEN `&SUC n' - 1 = &n'` by ((fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN rw [])
THEN fs []

THEN (TRY (metis_tac []))

THEN rw [locs_to_map_def]

THEN (TRY (Cases_on `i' ∈ FDOM map`)) THEN (TRY (Cases_on `i ∈ FDOM map`)) THEN fs [FST, SND] THEN rw [] THEN (TRY (metis_tac [])) THEN rw [get_locations_def, locs_to_map_def, FST, FAPPLY_FUPDATE_THM] THEN Cases_on `i ∈ FDOM map'` THEN rw [])));

val ms_il2_trans = store_thm("ms_il2_trans", ``!P r''' i v.ms_il2 P r''' /\ ms_il2 P (r''' |+ (i, v)) ==> (FDOM r''' = FDOM (r''' |+ (i, v)))``,
metis_tac [ms_il2_def]);

val ms_const = store_thm("ms_const", ``!P c c'.exec_clocked P c c' ==> !x y.(c = SOME x) /\ (c' = SOME y) ==> ms_il2 P (SND (SND (SND x))) ==> ms_il2 P (SND (SND (SND y)))``,
fs [exec_clocked_def] THEN STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT

THEN rw [ms_il2_def]

THEN Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [FST, SND] THEN Cases_on `y` THEN Cases_on `r'` THEN Cases_on `r''` THEN fs [FST, SND] THEN rw [] THEN Cases_on `c'` THEN1 (imp_res_tac RTC_CASES1 THEN fs [exec_clocked_one_cases]) THEN Cases_on `x` THEN Cases_on `r''` THEN Cases_on `r'''` THEN fs []

THEN fs [exec_clocked_one_cases] THEN Cases_on `P !! q` THEN fs [exec_clocked_instr_cases] THEN rw []

THEN `?nq.q = &nq` by metis_tac [int_ge, NUM_POSINT_EXISTS]
THEN rw []
THEN imp_res_tac int_monotonic_thm
THEN imp_res_tac every_store_inc_in_map
THEN fs [FDOM_FUPDATE]

THEN `i INSERT FDOM (FST (make_loc_map P)) = FDOM (FST (make_loc_map P))` by (rw [INSERT_DEF, EXTENSION] THEN Cases_on `x = i` THEN rw [])

THEN rw []);

val ms_const_2 = store_thm("ms_const_2", ``!P pc stk st pc' stk' st'.exec_one P (pc, stk, st) (pc', stk', st') ==> ms_il2 P st ==> ms_il2 P st'``, metis_tac [ms_const, SND, exec_def, RTC_SUBSET]);


val every_store_inc_in_map = prove(``!i P n.((n < LENGTH P) /\ ((P !! &n = IL2_Store i) \/ (P !! &n = IL2_Load i))) ==> i ∈ FDOM (FST (make_loc_map P))``,
Induct_on `P`
THEN rw []

THEN rw [make_loc_map_def, get_locations_def]

THEN Cases_on `h` THEN fs [get_locations_def]

THEN (TRY (Cases_on `n` THEN fs [fetch_def] THEN rw []

THEN fs [make_loc_map_def]

THEN `&SUC n' - 1 = &n'` by ((fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN rw [])
THEN fs []

THEN (TRY (metis_tac []))

THEN rw [locs_to_map_def]

THEN (TRY (Cases_on `i' ∈ FDOM map`)) THEN (TRY (Cases_on `i ∈ FDOM map`)) THEN fs [FST, SND] THEN rw [] THEN (TRY (metis_tac [])) THEN rw [get_locations_def, locs_to_map_def, FST, FAPPLY_FUPDATE_THM] THEN Cases_on `i ∈ FDOM map'` THEN rw [])));

val s_uloc_def = Define `(s_uloc [] = 0) /\ (s_uloc (VSM_Load l::xs) = MAX (l + 1) (s_uloc xs)) /\ (s_uloc (VSM_Store l::xs) = MAX (l+1) (s_uloc xs)) /\ (s_uloc (_::xs) = s_uloc xs)`;

val FETCH_EL = store_thm("FETCH_EL", ``!xs n.n < LENGTH xs ==> (xs !! &n = EL n xs)``,
Induct_on `n`

THEN1 (rw [fetch_def] THEN Cases_on `xs` THEN fs [LENGTH, fetch_def])
THEN rw [fetch_def]
THEN rw [EL] THEN Cases_on `xs` THEN fs [LENGTH] THEN res_tac THEN rw [fetch_def] THEN `&SUC n - 1 = &n` by (fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN rw []);

val suloc_thm = store_thm("suloc_thm", ``!P q n.(q < LENGTH P) /\ (P !! &q = VSM_Store n) ==> (n < s_uloc P)``,
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
THEN fs [int_monotonic_thm] THEN rfs []
THEN `!l. (l = n) ==> (l < s_uloc P)` by metis_tac []
THEN `!l. l ∈ FDOM r' ⇔ l < s_uloc P` by metis_tac [EQ_IMP_THM]
THEN metis_tac []);

val suloc_21_thm = store_thm("suloc_21_thm", ``!P pc stk st pc' stk' st'.exec_il3 P (pc, stk, st) (pc', stk', st') /\ (!l.l ∈ FDOM st <=> l < s_uloc P) ==> (!l.l ∈ FDOM st' <=> l < s_uloc P)``,
rw []
THEN mp_tac suloc_2_thm
THEN rw []
THEN res_tac
THEN fs [SND]);

val stack_contains_store_def = Define `
stack_contains_store st stk = !l.l ∈ FDOM st ==> (l < LENGTH stk) /\ (stk ?? l = st ' l)
`;

val drop_thm = store_thm("drop_thm", ``!xs ys.DROP (LENGTH xs) (xs ++ ys) = ys``,
Induct_on `xs` THEN rw []);

val take_thm = store_thm("take_thm", ``!xs ys.TAKE (LENGTH xs) (xs ++ ys) = xs``,
Induct_on `xs` THEN rw []);


val astack_def = Define `astack P st stk = stk ++ (REVERSE (GENLIST (\l.st ' l) (s_uloc P)))`;

val astack_produces_valid_store = store_thm("astack_produces_valid_store", ``!P st stk.(!l.l ∈ FDOM st <=> l < s_uloc P) ==> ?n.(stk = TAKE n (astack P st stk)) /\ stack_contains_store st (DROP n (astack P st stk))``,

rw [astack_def]
THEN EXISTS_TAC ``(LENGTH stk)`` THEN
rw [take_thm, drop_thm, stack_contains_store_def, fetch_rev_def, FETCH_EL, LESS_EQ_IMP_LESS_SUC]);


val load_in_prog_imp_in_map = prove(``!P i'.MEM (IL2_Load i') P ==> i' ∈ FDOM (FST (make_loc_map P)) ``,
Induct_on `P` THEN rw [] THEN fs [MEM, FST, make_loc_map_def, locs_to_map_def, get_locations_def]
THEN (TRY (res_tac THEN Cases_on `h` THEN fs [fetch_def, make_loc_map_def, il2_to_il3_def, s_uloc_def, locs_to_map_def, get_locations_def, il2_to_il3m_def, FCARD_FEMPTY]))

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [LET_DEF]
THEN Cases_on `i' ∈ FDOM m` THEN fs [] THEN rw []);

val store_in_prog_imp_in_map = prove(``!P i'.MEM (IL2_Store i') P ==> i' ∈ FDOM (FST (make_loc_map P)) ``,
Induct_on `P` THEN rw [] THEN fs [MEM, FST, make_loc_map_def, locs_to_map_def, get_locations_def]
THEN (TRY (res_tac THEN Cases_on `h` THEN fs [fetch_def, make_loc_map_def, il2_to_il3_def, s_uloc_def, locs_to_map_def, get_locations_def, il2_to_il3m_def, FCARD_FEMPTY]))

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [LET_DEF]
THEN Cases_on `i' ∈ FDOM m` THEN fs [] THEN rw []);


val snd_arg_fcard = prove(``!P.SND (make_loc_map P) = FCARD (FST (make_loc_map P))``,

fs [make_loc_map_def] THEN Induct_on `P` THEN rw [get_locations_def, locs_to_map_def, FST, FCARD_FEMPTY] THEN Cases_on `h` THEN  fs [fetch_def, make_loc_map_def, il2_to_il3_def, s_uloc_def, locs_to_map_def, get_locations_def, il2_to_il3m_def] THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [LET_DEF]
THEN Cases_on `i ∈ FDOM m` THEN fs [FCARD_FUPDATE] THEN decide_tac);

val s_uloc_fcard = prove(``!P.s_uloc (il2_to_il3 P) = FCARD (FST (make_loc_map P))``,

Induct_on `P` THEN rw [get_locations_def, locs_to_map_def, FST, FCARD_FEMPTY, s_uloc_def, make_loc_map_def, il2_to_il3_def]

THEN Cases_on `h` THEN fs [fetch_def, make_loc_map_def, il2_to_il3_def, s_uloc_def, locs_to_map_def, get_locations_def, il2_to_il3m_def, FCARD_FEMPTY]

THEN `?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [LET_DEF]

THEN Cases_on `i ∈ FDOM m` THEN fs [FCARD_FUPDATE, FCARD_FEMPTY]

THEN (TRY (`m ' i < FCARD m` by metis_tac [snd_arg_fcard, map_range_thm, FST, SND, make_loc_map_def]

THEN `m ' i + 1 <= FCARD m` by decide_tac THEN rw [MAX_DEF] THEN decide_tac))

THEN `MAP (il2_to_il3m (m |+ (i, n))) P = MAP (il2_to_il3m m) P` by (

rw [MAP_EQ_f]

THEN Cases_on `e` THEN  fs [il2_to_il3m_def, get_locations_def, s_uloc_def] THEN 


`?m n.locs_to_map (get_locations P) = (m, n)` by metis_tac [locs_to_map_total_thm] THEN fs [LET_DEF]

THEN fs [locs_to_map_def, get_locations_def] THEN fs [LET_DEF]

THEN Cases_on `i' ∈ FDOM m'` THEN fs [] THEN rw [] THEN1 metis_tac [FAPPLY_FUPDATE_THM]

THEN fs [FDOM_FUPDATE]

THEN metis_tac [store_in_prog_imp_in_map, load_in_prog_imp_in_map, FST, make_loc_map_def, FAPPLY_FUPDATE_THM])

THEN rw []

THEN rw [MAX_DEF]

THEN `FCARD m = n` by metis_tac [snd_arg_fcard, FST, make_loc_map_def, SND, MAX_DEF] THEN decide_tac);

val least_unused_loc_is_next_to_use = prove(``!P.SND (make_loc_map P) = s_uloc (il2_to_il3 P)``, metis_tac [s_uloc_fcard, snd_arg_fcard]);

val min_store_imp_all_locs_in_range = store_thm("min_store_imp_all_locs_in_range", ``!P st.ms_il2 P st ==> (!l.l ∈ FDOM (MAP_KEYS (map_fun (FST (make_loc_map P))) st) <=> (l < s_uloc (il2_to_il3 P)))``,

rw [ms_il2_def]

THEN rw [MAP_KEYS_def, make_loc_map_inj]

THEN `s_uloc (il2_to_il3 P) = (SND (make_loc_map P))` by metis_tac [least_unused_loc_is_next_to_use]

THEN metis_tac [locs_to_map_total_thm, map_fun_def, map_range_thm, make_loc_map_def,EQ_IMP_THM, map_range_2_thm, FST, SND, make_loc_map_def]);

val _ = export_theory ();
