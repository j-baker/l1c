 open HolKernel bossLib Parse boolLib listTheory lcsymtacs ast_vsm0Theory ast_il2Theory finite_mapTheory smallstep_il2Theory relationTheory smallstep_vsm0Theory pairTheory;

val _ = new_theory "il2_to_vsm0_compiler";

val get_locations_def = Define `
(get_locations [] = []) /\
(get_locations ((IL2_Store l)::stms) = l::(get_locations stms)) /\
(get_locations ((IL2_Load l)::stms) = l::(get_locations stms)) /\
(get_locations (_::stms) = get_locations stms)`;

val locs_to_map_def = Define `
(locs_to_map [] = (FEMPTY,(0:num))) /\
(locs_to_map (l::ls) = let (map, next_loc) = locs_to_map ls
                        in (if l ∈ FDOM map then (map, next_loc) else (map |+ (l, next_loc), next_loc + 1)))`;

val make_loc_map_def = Define `make_loc_map il2_prog = (locs_to_map (get_locations il2_prog))`;

val il2_to_vsm0m_def = Define `
(il2_to_vsm0m m IL2_Nop = VSM_Nop) /\
(il2_to_vsm0m m (IL2_Push x) = VSM_Push x) /\
(il2_to_vsm0m m (IL2_Store x) = VSM_Store (m ' x)) /\
(il2_to_vsm0m m (IL2_Load x) = VSM_Load (m ' x)) /\
(il2_to_vsm0m m IL2_Pop = VSM_Pop) /\
(il2_to_vsm0m m IL2_Plus = VSM_Plus) /\
(il2_to_vsm0m m IL2_Geq = VSM_Geq) /\
(il2_to_vsm0m m IL2_Halt = VSM_Halt) /\
(il2_to_vsm0m m (IL2_Jump n) = (VSM_Jump n)) /\
(il2_to_vsm0m m (IL2_Jz n) = VSM_Jz n)`;

val repeatn_def = Define `(repeatn 0 _ = []) /\ (repeatn (SUC n) x = x::(repeatn n x))`;

val num_locs_def = Define `num_locs prog = SND (locs_to_map (get_locations prog))`;

val il2_to_vsm0_def = Define `il2_to_vsm0 prog = let (map,  num_locs) = (locs_to_map (get_locations prog)) in
((repeatn num_locs (VSM_Push 0)) ++ (MAP (il2_to_vsm0m map) prog))`;

val update_stack_def = Define `
(update_stack m stk (IL2_Store l) v = update_loc stk (m ' l) v) /\
(update_stack _ stk _ _ = stk)`;



val badinstr_def = Define `
(badinstr (IL2_Store l) [] = T) /\
(badinstr IL2_Pop [] = T) /\
(badinstr IL2_Plus [] = T) /\
(badinstr IL2_Plus [x] = T) /\
(badinstr IL2_Geq [] = T) /\
(badinstr IL2_Geq [x] = T) /\
(badinstr (IL2_Jz n) [] = T) /\
(badinstr _ _ = F)`;

val badin_no_step = prove(``!inst stk.badinstr inst stk ==> !st pc pc' stk' st'.~exec_instr inst (pc, stk, st) (pc', stk', st')``,
rw [] THEN Cases_on `inst` THEN Cases_on `stk` THEN fs [badinstr_def] THEN rw [] THEN rw [Once exec_instr_cases] THEN Cases_on `t` THEN fs [badinstr_def] THEN rw []);

val exec_no_badinstr = prove(``
!P stk st stk''' st'''.
exec P (0, stk, st) (&LENGTH P, stk''', st''') ==>
    !pc' stk' st' pc'' stk'' st''.
        ((exec_one P)^* (0, stk, st) (pc', stk', st') /\
         (exec_one P (pc', stk', st') (pc'', stk'', st'')) /\
         (exec_one P)^* (pc'', stk'', st'') (&LENGTH P, stk''', st'''))
      ==> ~badinstr (P !! pc') stk'``,
rw [] THEN
CCONTR_TAC THEN
fs [Once exec_one_cases, badin_no_step]);

val exec_one_append = prove(``
!P pc stk st pc' stk' st st'.
exec_one P (pc, stk, st) (pc', stk', st') ==> !app.exec_one P (pc, stk ++ app, st) (pc', stk' ++ app, st')``,

rw [] THEN
rw [Once exec_one_cases] THEN fs [Once exec_one_cases]
THEN Cases_on `P !! pc'` THEN rw [Once exec_instr_cases] THEN fs [Once exec_instr_cases]);

val exec_append_stack = prove(``
!P stk st stk''' st'''.
exec P (0, stk, st) (&LENGTH P, stk''', st''') ==>
    !pc' stk' st' pc'' stk'' st''.
        ((exec_one P)^* (0, stk, st) (pc', stk', st') /\
         (exec_one P (pc', stk', st') (pc'', stk'', st'')) /\
         (exec_one P)^* (pc'', stk'', st'') (&LENGTH P, stk''', st'''))
      ==> !x.(exec_one P) (pc', stk'++x, st') (pc'', stk''++x, st'')``,
rw [] THEN
rw [Once exec_one_cases] THEN fs [Once exec_one_cases]
THEN Cases_on `P !! pc'` THEN rw [Once exec_instr_cases] THEN fs [Once exec_instr_cases]);


val (new_exec_one_rules, new_exec_one_ind, new_exec_one_cases) = Hol_reln `!P pc pc' stk stk' st st' app app'.(exec_one P (pc, stk, st) (pc', stk', st')) ==> (new_exec_one P (pc, stk ++ app, st) (pc', stk' ++ app', st'))`;

val NEWEXEC_SUB = store_thm("NEWEXEC_SUB",
``!P p p'.exec P p p' ==> (new_exec_one P)^* p p'``,
fs [exec_def]
THEN STRIP_TAC

THEN ho_match_mp_tac exec_strongind

THEN rw []

THEN Cases_on `p`
THEN Cases_on `r`
THEN Cases_on `p''`
THEN Cases_on `r`
THEN Cases_on `p'`
THEN Cases_on `r`

THEN `new_exec_one P (q, q', r') (q'''', q''''', r''')` by (rw [Once new_exec_one_cases]
THEN `(q' = q' ++ []) ∧ (q''''' = q''''' ++ []) ∧
  exec_one P (q,q',r') (q'''',q''''',r''')` by metis_tac [APPEND_NIL]
THEN metis_tac [])

THEN rw [Once RTC_CASES1]
THEN DISJ2_TAC

THEN metis_tac []);

!P p p'.(new_exec_one P)^* p p' ==> ?stk stk' app app'.((FST (SND p)) = stk ++ app) /\ ((FST (SND p')) = stk' ++ app') /\ (exec_one P)^* p p'
STRIP_TAC

ho_match_mp_tac RTC_STRONG_INDUCT
rw []

THEN Cases_on `p` THEN rw [FST, SND] THEN Cases_on `r` THEN fs [FST, SND]

metis_tac [APPEND_NIL]

Cases_on `p'` THEN Cases_on `p''` THEN Cases_on `r` THEN Cases_on `r''` THEN fs [FST, SND]
THEN rw []

fs [Once new_exec_one_cases]
rw []




` (stk'' ++ app'' = stk'' ++ app'') ∧
  (stk' ++ app' = stk' ++ app') ∧
  (exec_one P)^* (q,stk'' ++ app'',r') (q''',stk' ++ app',r)` by all_tac

rw []

rw [Once RTC_CASES1]
DISJ2_TAC

`exec_one P (q, stk'' ++ app'', r') (q'', stk''' ++ app'', r''')` by metis_tac [exec_one_append]

HINT_EXISTS_TAC
rw []


fs [new_exec_one_cases]

rw []

`exec_one P (pc, stk ++ app, st) (pc', stk' ++ app, st')` by metis_tac [exec_one_append]

HINT_EXISTS_TAC

rw []

imp_res_tac exec_one_append

val exec_append_stack = prove(``
!P stk st stk''' st'''.
exec P (0, stk, st) (&LENGTH P, stk''', st''') ==>
    !pc' stk' st' pc'' stk'' st''.
        ((exec_one P)^* (0, stk, st) (pc', stk', st') /\
         (exec_one P (pc', stk', st') (pc'', stk'', st'')) /\
         (exec_one P)^* (pc'', stk'', st'') (&LENGTH P, stk''', st'''))
      ==> !a b c d y.
        ((exec_one P)^* (0, stk++x, st) (pc', stk'++x, st') /\
         (exec_one P (pc', stk'++x, st') (pc'', stk''++y, st'')) /\
         (exec_one P)^* (pc'', stk''++y, st'') (&LENGTH P, stk''', st'''))

(exec_one P) (pc', stk'++x, st') (pc'', stk''++x, st'




``,
rw [] THEN
rw [Once exec_one_cases] THEN fs [Once exec_one_cases]
THEN Cases_on `P !! pc'` THEN rw [Once exec_instr_cases] THEN fs [Once exec_instr_cases]);





CCONTR_TAC THEN
fs [Once exec_one_cases, badin_no_step]);

val _ = export_theory ();
