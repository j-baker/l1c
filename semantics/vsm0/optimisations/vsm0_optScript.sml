open HolKernel bossLib boolLib lcsymtacs listTheory ast_vsm0Theory relationTheory smallstep_vsm0_clockedTheory integerTheory arithmeticTheory smallstep_il2Theory pred_setTheory

val _ = new_theory "vsm0_opt"

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)
val rwa = rw_tac (srw_ss () ++ intSimps.INT_ARITH_ss)

val MAPi_def = Define `(MAPi P [] = []) /\ (MAPi P (x::xs) = (P 0 x)::MAPi (P o SUC) xs)`

val EL_MAPi_thm = prove(``!P l n.n < LENGTH l ==> (EL n (MAPi P l) = P n (EL n l))``, Induct_on `l` THEN rw [] THEN rw [MAPi_def] THEN Cases_on `n` THEN rw [EL] THEN fs [])


val rw_for_def = Define `(rw_for len pc (VSM_Jump n) = if len < &pc + n + 1 then (VSM_Jump (n - 1)) else VSM_Jump n)
/\ (rw_for len pc (VSM_Jz n) = if len < &pc + n + 1 then (VSM_Jz (n - 1)) else VSM_Jump n)
/\ (rw_for len pc x = x)
`

val rw_ba_def = Define `(rw_ba pc (VSM_Jump n) = if &pc + n + 1 < 0 then (VSM_Jump (n + 1)) else VSM_Jump n)
/\ (rw_ba pc (VSM_Jz n) = if &pc + n + 1 < 0 then (VSM_Jz (n + 1)) else VSM_Jump n)
/\ (rw_ba pc x = x)
`

val el_append_thm = prove(``!x l1 l2.(LENGTH l1 < x) ==> (EL x (l1 ++ l2) = EL (x - LENGTH l1) l2)``,
Induct_on `l1` THEN rw [] THEN Cases_on `x` THEN fs [])

val EL_APPEND_THM = prove(``
!L1 L2 n.(n < LENGTH (L1 ++ L2)) ==>
(EL n (L1 ++ L2) = if n < LENGTH L1 then EL n L1 else EL (n - LENGTH L1) L2)
``,
Induct_on `L1` THEN fs []
THEN Induct_on `n` THEN fs [] THEN rw [] THEN `n < LENGTH L1 + LENGTH L2` by decide_tac THEN metis_tac [])

val drop_el = prove(``
!P n d.(n + d < LENGTH P) ==> (EL n (DROP d P) = EL (n + d) P)
``,
Induct_on `P` THEN fs [] THEN rw []

THEN Cases_on `d` THEN fs [] THEN rw [] THEN `n + SUC n' = SUC (n + n')` by decide_tac THEN fs [])

val take_el = prove(``
!P n t.(n < t) /\ (t < LENGTH P) ==> (EL n (TAKE t P) = EL n P)
``,
Induct_on `P` THEN fs [] THEN rw [] THEN Cases_on `t` THEN fs [] THEN rw [] THEN Cases_on `n` THEN fs [])

val mapi_length_thm = prove(``!l P.LENGTH l = LENGTH (MAPi P l)``,
Induct_on `l` THEN rw [MAPi_def])

val nop_elim_def = Define `
nop_elim P l = if (EL l P <> VSM_Nop)  \/ (LENGTH P <= l) then P else
(MAPi (rw_for &l) (TAKE l P)) ++ (MAPi rw_ba (DROP (SUC l) P))`

val nop_elim_length = prove(``
!P l.(LENGTH (nop_elim P l) = LENGTH P) \/ (SUC (LENGTH (nop_elim P l)) = LENGTH P)
``,
fs [nop_elim_def] THEN rw [] THEN fs [GSYM mapi_length_thm] THEN DISJ2_TAC

THEN fs [NOT_LEQ]
THEN `l <= LENGTH P` by decide_tac
THEN imp_res_tac LENGTH_TAKE
THEN rw []
THEN decide_tac)

val make_pair_def = Define `
(make_pair l pc clk stk = (SOME (pc, clk, stk), SOME (if &l < pc then (pc - 1) else pc, clk, stk)))
`

val bisim_set_def = Define `
bisim_set P l = if (EL l P = VSM_Nop) /\ (l < LENGTH P) then {x | ?pc clk stk.(make_pair l pc clk stk = x) \/ (x = (NONE, NONE))} else {(x, x) | T}`

val bisim_set_fun = prove(``!P l x y z.(x, y) ∈ bisim_set P l /\ (x, z) ∈ bisim_set P l ==> (y = z)``,
fs [bisim_set_def] THEN rw [] THEN fs [make_pair_def] THEN rw [] THEN fsa [])


val nj_def = Define `(nj x m (VSM_Jump n) = (&x <> (&m+n+1))) /\ (nj x m (VSM_Jz n) = (&x <> (&m+n+1))) /\ (nj _ _ _ = T)`

val no_jumps_def = Define `no_jumps l P = EVERYi (nj l) P`

val elim_pushpop_def = Define `
elim_pushpop P l = if (SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (case EL l P of VSM_Push x => T | _ => F) /\ (EL (SUC l) P = VSM_Pop) then LUPDATE VSM_Nop l (LUPDATE VSM_Nop (SUC l) P) else P
`

val el_pp_bs_set_def = Define `
el_pp_bs_set P l = if (l < LENGTH P) then {(x, x) | (?pc clk stk.(x = SOME (pc, clk, stk)) /\ (pc <> &(SUC l))) \/ (x = NONE)} ∪ 
{(x, y) | ?clk stk e.(x = SOME (&(SUC l), clk, e::stk)) /\ (y = SOME (&(SUC l), clk, stk))}

else {(x, x) | T}`

val epbs_compute_def = Define `
(epbs_compute P l (NONE, NONE) = T) /\
(epbs_compute P l (SOME(pc1, clk1, stk1), SOME(pc2, clk2, stk2)) = if l < LENGTH P then
(if pc1 <> &SUC l then SOME(pc1, clk1, stk1) = SOME(pc2, clk2, stk2) else
(case stk1 of [] => F 
	   | (h::t) => SOME(pc1, clk1, stk1) = SOME(pc2, clk2, h::stk2)))
else SOME(pc1, clk1, stk1) = SOME(pc2, clk2, stk2)) /\
(epbs_compute _ _ _ = F)`

val compute_equiv = prove(``!P l.epbs_compute P l = el_pp_bs_set P l``,

rw [epbs_compute_def, el_pp_bs_set_def, EXTENSION, SPECIFICATION, EQ_IMP_THM]

THEN1 (Cases_on `x` THEN Cases_on `q` THEN Cases_on `r` THEN fs [epbs_compute_def] THEN Cases_on `x` THEN Cases_on `x'`
THEN Cases_on `r` THEN Cases_on `r'` THEN fs [epbs_compute_def] THEN rfs [] THEN Cases_on `q <> &SUC l` THEN fs [] THEN Cases_on `r''` THEN fs [] THEN rw [])

THEN (TRY (EVAL_TAC THEN fs [] THEN Cases_on `x` THEN Cases_on `q` THEN Cases_on `r` THEN fs [epbs_compute_def] THEN Cases_on `x` THEN Cases_on `x'` THEN Cases_on `r` THEN Cases_on `r'` THEN fs [epbs_compute_def] THEN rfs []))

THEN Cases_on `x'` THEN fs [epbs_compute_def] THEN Cases_on `x` THEN Cases_on `r` THEN fs [epbs_compute_def])

val everyi_thm = prove(``
!L P l.(l < LENGTH L) /\ EVERYi P L ==> P l (EL l L)``,

Induct_on `l` THEN fs [] THEN rw [] THEN1 (Cases_on `L` THEN fs [EVERYi_DEF])
THEN `l < LENGTH L` by decide_tac THEN fs [] THEN Cases_on `L` THEN fs [] THEN fs [EVERYi_DEF] THEN `(P o SUC) l (EL l t)` by metis_tac [] THEN fs [])


val epbs_function = prove(``!P l x y z.(x, y) ∈ el_pp_bs_set P l /\ (x, z) ∈ el_pp_bs_set P l ==> (y = z)``,
fs [el_pp_bs_set_def] THEN rw [])

val FETCH_EL = store_thm("FETCH_EL", ``!xs n.n < LENGTH xs ==> (xs !! &n = EL n xs)``,
Induct_on `n`
THEN1 (rw [fetch_def] THEN Cases_on `xs` THEN fs [LENGTH, fetch_def])
THEN rw [fetch_def]
THEN rw [EL] THEN Cases_on `xs` THEN fs [LENGTH] THEN res_tac THEN rw [fetch_def] THEN `&SUC n - 1 = &n` by (fs [INT, int_sub] THEN rw [Once (GSYM INT_ADD_ASSOC)]) THEN rw [])


val plus_sound_thm = prove(``
!P l.
(SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (?x.EL l P = VSM_Push x) /\ (EL (SUC l) P = VSM_Pop) ==>
!c c'.vsm_exec_c P c c' ==> !d d''.(c, d) ∈ (el_pp_bs_set P l) ==> (c', d'') ∈ (el_pp_bs_set P l)
==> vsm_exec_c (elim_pushpop P l) d d''
``,
(NTAC 3 STRIP_TAC) THEN fs [vsm_exec_c_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []
THEN1 metis_tac [RTC_REFL, epbs_function]
THEN fs [vsm_exec_c_one_cases, int_ge] THEN rw [] THEN `?ipc.pc = &ipc` by rwa [NUM_POSINT_EXISTS] THEN fs [] THEN rw []
THEN fs [el_pp_bs_set_def] THEN rw [] THEN (REVERSE (Cases_on `l < LENGTH P`))
THEN1(rw [Once RTC_CASES1] THEN DISJ2_TAC THEN fs [elim_pushpop_def] THEN `~(SUC l < LENGTH P)` by decide_tac THEN fs [] THEN rw [vsm_exec_c_one_cases, int_ge] THEN metis_tac [])
THEN imp_res_tac FETCH_EL THEN fs[] THEN rw []
THEN (TRY (fs [vsm_exec_c_one_cases] THEN FAIL_TAC ""))


THEN ((Cases_on `c'` THEN1 (imp_res_tac RTC_CASES1 THEN fs [vsm_exec_c_one_cases] THEN rw [] THEN fs [vsm_exec_c_instr_cases] THEN rw [] THEN rw [Once RTC_CASES1] THEN Q.EXISTS_TAC `NONE` THEN rw [] THEN fs [elim_pushpop_def, int_ge, vsm_exec_c_one_cases] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rw [EL_LUPDATE] THEN fs [vsm_exec_c_instr_cases])) THEN Cases_on `x'` THEN Cases_on `r` THEN fs []

THEN rfs [] THEN fs []

THEN Cases_on `q <> &SUC l` THEN fs [] THEN rw [] THEN fs [] THEN rw []

THEN1 (rw [Once RTC_CASES1] THEN (TRY (DISJ2_TAC)) THEN Q.EXISTS_TAC `SOME (q, q', r')` THEN fs [vsm_exec_c_one_cases, int_ge] THEN fs [elim_pushpop_def] THEN rw [] THEN Cases_on `ipc = l` THEN fs [] THEN rw [] THEN1 (fs[vsm_exec_c_instr_cases, EL_LUPDATE] THEN rw [] THEN fsa [] THEN rfs [] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rw [EL_LUPDATE]) THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN fs [] THEN fs [EL_LUPDATE, vsm_exec_c_instr_cases])



THEN Cases_on `ipc = l` THEN fs [] THEN rw [] THEN1 (rfs [] THEN fs [vsm_exec_c_instr_cases] THEN rw [] THEN fsa [] THEN fs [elim_pushpop_def] THEN rfs [] THEN rw [Once RTC_CASES1] THEN (TRY (DISJ2_TAC)) THEN Q.EXISTS_TAC `SOME (&SUC ipc, clk, stk)` THEN rw [] THEN rw [vsm_exec_c_one_cases, int_ge] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rw [] THEN rwa [EL_LUPDATE, vsm_exec_c_instr_cases] THEN (Cases_on `(clk = clk') /\ (stk = stk')` THEN `&SUC ipc = &ipc + 1` by rwa [] THEN rwa [RTC_REFL] THEN (imp_res_tac RTC_CASES1 THEN (TRY(fsa [] THEN rw [] THEN FAIL_TAC "")))

THEN fs [vsm_exec_c_one_cases] THEN rw [] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rfs [])
)

THEN fs [vsm_exec_c_instr_cases] THEN `&ipc + 1 = &SUC ipc` by rwa [] THEN fs [] THEN rw [] THEN fs [no_jumps_def] THEN
imp_res_tac everyi_thm THEN rfs [nj_def] THEN fsa []))

val pushpop_safe_1 = prove(``!P clk stk l.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (elim_pushpop P l) (SOME (0, clk, stk)) NONE``,
rw []
THEN Cases_on `(SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (case EL l P of VSM_Push x => T | _ => F) /\ (EL (SUC l) P = VSM_Pop)` THEN fs []
THEN1 (Cases_on `EL l P` THEN fs [] THEN imp_res_tac plus_sound_thm THEN fs [el_pp_bs_set_def] THEN `l < LENGTH P` by decide_tac THEN fs []) THEN rw [elim_pushpop_def])

val pushpop_safe_2 = prove(``!P clk stk l clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (elim_pushpop P l) (SOME (0, clk, stk)) (SOME (&LENGTH (elim_pushpop P l), clk', stk'))``,
rw []
THEN Cases_on `(SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (case EL l P of VSM_Push x => T | _ => F) /\ (EL (SUC l) P = VSM_Pop)` THEN fs []
THEN1 (Cases_on `EL l P` THEN fs [] THEN imp_res_tac plus_sound_thm THEN fs [el_pp_bs_set_def] THEN `l < LENGTH P` by decide_tac THEN fs [] THEN Cases_on `LENGTH P <> SUC l` THEN fs [] THEN fs [elim_pushpop_def] THEN rfs []) THEN rw [elim_pushpop_def])

val c_pp_def = Define `(c_pp P 0 = elim_pushpop P 0) /\ (c_pp P (SUC n) = elim_pushpop (c_pp P n) (SUC n))`

val c_pp_1_thm = prove(``
!P clk stk n.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (c_pp P n) (SOME (0, clk, stk)) NONE
``,
Induct_on `n` THEN rw [] THEN metis_tac [pushpop_safe_1, c_pp_def])

val c_pp_2_thm = prove(``
!P clk stk n clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (c_pp P n) (SOME (0, clk, stk)) (SOME (&LENGTH (c_pp P n), clk', stk'))
``,
Induct_on `n` THEN rw [] THEN metis_tac [pushpop_safe_2, c_pp_def])

val comp_pp_def = Define `comp_pp P = c_pp P (LENGTH P)`

val comp_pp_1_thm = store_thm("comp_pp_1_thm", ``
!P clk stk.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (comp_pp P) (SOME (0, clk, stk)) NONE
``, metis_tac [comp_pp_def, c_pp_1_thm])

val comp_pp_2_thm = store_thm("comp_pp_2_thm", ``
!P clk stk clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (comp_pp P) (SOME (0, clk, stk)) (SOME (&LENGTH (comp_pp P), clk', stk'))
``, metis_tac [comp_pp_def, c_pp_2_thm])


val cast_sub = prove(``!l n.(l <= n) ==> (&(n-l) = &n - &l)``,
Induct_on `n` THEN rw []
THEN Cases_on `l = SUC n`
THEN rwa []

THEN `SUC n - l = SUC (n-l)` by decide_tac
THEN rw [INT]
THEN `l <= n` by decide_tac
THEN res_tac
THEN rwa [])

val halt_thm = prove(``!P c c'.vsm_exec_c P c c' ==> !ipc clk stk.(c = SOME (&ipc, clk, stk)) /\ (EL ipc P = VSM_Halt) ==> (c' = SOME (&ipc, clk, stk))``,
STRIP_TAC THEN fs [vsm_exec_c_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN fs [vsm_exec_c_one_cases] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL, vsm_exec_c_instr_cases])

val nice_halt_thm = prove(``!ipc P clk stk c'.(EL ipc P = VSM_Halt) /\ (vsm_exec_c_one P)^* (SOME (&ipc, clk, stk)) c' ==> (c' = SOME (&ipc, clk, stk))``, metis_tac [halt_thm, vsm_exec_c_def])

val length_nop_elim = prove(``
!l P n.(SUC n < LENGTH P) ==> (n < LENGTH (nop_elim P l))
``,
rw [] THEN rw [nop_elim_def] THEN fs [GSYM mapi_length_thm, NOT_LESS_EQUAL] THEN (TRY decide_tac) THEN `l <= LENGTH P` by decide_tac THEN fs [LENGTH_TAKE] THEN decide_tac)

val nop_elim_fetch = prove(``
!P l n.(SUC n < LENGTH P) /\ (l < LENGTH P) ==> (nop_elim P l !! &n = EL n (nop_elim P l))
``,
rw [] THEN `n < LENGTH P` by decide_tac THEN rw [nop_elim_def, FETCH_EL]
THEN match_mp_tac FETCH_EL THEN rw [GSYM mapi_length_thm, LENGTH_TAKE] THEN `l <= LENGTH P` by decide_tac THEN fs [LENGTH_TAKE] THEN decide_tac)

val remove_nop_sound = prove(``
!P l c c'.vsm_exec_c P c c' ==> !d d''.(c, d) ∈ (bisim_set P l) ==> (c', d'') ∈ (bisim_set P l) ==> vsm_exec_c (nop_elim P l) d d''
``,
(NTAC 2 STRIP_TAC) THEN fs [vsm_exec_c_def] THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw []
THEN1 metis_tac [RTC_REFL, bisim_set_fun]

THEN fsa [vsm_exec_c_one_cases, int_ge] THEN rw []

THEN rfs [bisim_set_fun]

THEN Cases_on `EL l P <> VSM_Nop` THEN1 (fs [nop_elim_def, bisim_set_def] THEN rw [Once RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `c'` THEN rwa [vsm_exec_c_one_cases]) THEN fs []

THEN fs [bisim_set_def] THEN Cases_on `~(l < LENGTH P)` THEN1 (fs [] THEN fs [nop_elim_def, NOT_LESS] THEN rw [Once RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `c'` THEN rwa [vsm_exec_c_one_cases])

THEN fs [] THEN rw []

THEN Cases_on `c'` THEN1 (Cases_on `P !! pc` THEN fs [vsm_exec_c_instr_cases] THEN `c'' = NONE` by (imp_res_tac RTC_CASES1 THEN fs [vsm_exec_c_one_cases]) THEN rw [] THEN fs [make_pair_def])


THEN (TRY (fs [vsm_exec_c_instr_cases] THEN rw [] THEN fs [make_pair_def] THEN rw []
THEN match_mp_tac RTC_SUBSET THEN fsa [vsm_exec_c_one_cases, int_ge] THEN rw []

THEN1 (`(pc − 1 < &LENGTH (nop_elim P l)) = (pc < &SUC (LENGTH (nop_elim P l)))` by rwa [GSYM INT] THEN rw [] THEN
`?x.pc = &x` by rwa [NUM_POSINT_EXISTS] THEN rw [] THEN fs [] THEN Cases_on `x` THEN fs []
THEN metis_tac [length_nop_elim])

THEN1 (Cases_on `pc` THEN fs [] THEN Cases_on `n` THEN fs [] THEN rw [] THEN fsa [GSYM INT] THEN `&SUC n' - 1 = &n'` by rwa [] THEN rw []

THEN rw [nop_elim_fetch] THEN `n' < LENGTH (nop_elim P l)` by metis_tac [length_nop_elim] THEN fs [nop_elim_def] THEN rw [] THEN1 decide_tac THEN fs [] THEN rw [] THEN rfs [] THEN fs [EL_APPEND_THM] THEN `l <= LENGTH P` by decide_tac THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN `~(n' < l)` by decide_tac THEN fs [] THEN `(n' - l) < LENGTH (DROP (SUC l) P)` by (`SUC l <= LENGTH P` by decide_tac THEN rw [LENGTH_DROP] THEN decide_tac)
 THEN rw [EL_MAPi_thm]

THEN `(n' - l) + (SUC l) < LENGTH P` by decide_tac

THEN rw [drop_el]

THEN `n' - l + SUC l = SUC n'` by decide_tac THEN rw []

THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rw [] THEN rw [rw_ba_def, vsm_exec_c_instr_cases])

THEN1 (`?x.pc = &x` by metis_tac [NUM_POSINT_EXISTS] THEN fs [] THEN rw [] THEN fs [NOT_LESS] THEN rw [] THEN fs [nop_elim_def] THEN `l <= LENGTH P` by decide_tac THEN rw [GSYM mapi_length_thm, LENGTH_TAKE] THEN Cases_on `x = l` THEN imp_res_tac FETCH_EL THEN fs [] THEN decide_tac)

THEN (`?n'.pc = &n'` by rw [NUM_POSINT_EXISTS] THEN fs [] THEN rw [] THEN fsa [GSYM INT] THEN `&SUC n' - 1 = &n'` by rwa [] THEN rw []

THEN rw [nop_elim_fetch] THEN `n' < l` by (Cases_on `n' = l` THEN imp_res_tac FETCH_EL THEN fs [NOT_LESS] THEN rw [] THEN decide_tac)
THEN `SUC n' < LENGTH P` by decide_tac
THEN  `n' < LENGTH (nop_elim P l)` by metis_tac [length_nop_elim] THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN fs [nop_elim_def] THEN rw [] THEN1 rw [vsm_exec_c_instr_cases] THEN fs [] THEN rw [] THEN rfs [] THEN fs [EL_APPEND_THM] THEN `l <= LENGTH P` by decide_tac THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN `(n' < l)` by decide_tac THEN fs [] THEN rw [EL_MAPi_thm, take_el, rw_for_def, vsm_exec_c_instr_cases]
THEN FAIL_TAC "")))

THEN (TRY (Cases_on `x` THEN Cases_on `r`

THEN Cases_on `d` THEN1 fs [RTC_REFL, make_pair_def] THEN Cases_on `x` THEN Cases_on `r` THEN rw []

THEN (TRY (Cases_on `c''` THEN1 fs [make_pair_def] THEN Cases_on `x` THEN Cases_on `r`
THEN Cases_on `d''` THEN1 fs [make_pair_def] THEN Cases_on `x` THEN Cases_on `r`

THEN `(pc'' = q'''') /\ (clk'' = q''''') /\ (stk'' = r''')` by fs [make_pair_def] THEN rw []
THEN `(q''''''' = clk'') /\ (r''' = r'''')` by fs [make_pair_def] THEN rw []))

THEN (TRY (`(clk = q''') /\ (stk = r'')` by (fs [make_pair_def] THEN rw [] THEN FAIL_TAC "")))
THEN `(pc' = pc) /\ (clk' = clk) /\ (stk' = stk)` by fs [make_pair_def] THEN rw []

THEN Cases_on `pc = &l`

         THEN1( `EL l P = P !! &l` by (imp_res_tac FETCH_EL THEN fs [FETCH_EL]) THEN rw [] THEN fs [vsm_exec_c_instr_cases] THEN rw []
 THEN fs [make_pair_def] THEN rw []
          THEN `&l + 1 - 1 = &l` by rwa []
          THEN fs [])
THEN rw [Once RTC_CASES1] THEN (TRY DISJ2_TAC)
THEN `?ipc.pc = &ipc` by rwa [NUM_POSINT_EXISTS] THEN rw [] THEN fs [] THEN rw []
THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN rw [] THEN rfs [FETCH_EL] THEN rw []

THEN Cases_on `(!x.EL ipc P <> VSM_Jump x) /\ (!x.EL ipc P <> VSM_Jz x) /\ (EL ipc P <> VSM_Halt)`

THEN1 (fs []
THEN `q = &ipc + 1` by fs [vsm_exec_c_instr_cases] THEN rw []
THEN Q.EXISTS_TAC `SOME (q'' + 1, q', r')` THEN rw []
THEN1 (
fs [make_pair_def] THEN rw [] THEN fsa [] THEN rw []
THEN rwa [vsm_exec_c_one_cases, int_ge]
THEN1 (rw [INT_SUB_LE] THEN decide_tac)
THEN1 (rwa [INT_LT_SUB_RADD, GSYM INT] THEN Cases_on `LENGTH (nop_elim P l) = LENGTH P` THEN1 decide_tac THEN `SUC (LENGTH (nop_elim P l)) = LENGTH P` by metis_tac [nop_elim_length] THEN decide_tac)
THEN1 (rw [nop_elim_def] THEN1 decide_tac
THEN Cases_on `ipc` THEN1 decide_tac
THEN `&SUC n - 1 = &n` by rwa [] THEN fs []
THEN fsa [] THEN `n < LENGTH P` by decide_tac THEN

`LENGTH P = SUC (LENGTH (MAPi (rw_for &l) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P)))` by (`l <= LENGTH P` by decide_tac THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac)

THEN `n < (LENGTH (MAPi (rw_for (&l)) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P)))` by decide_tac
THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL]
THEN `l <= LENGTH P` by decide_tac
THEN rw [EL_APPEND_THM] THEN fs [EL_APPEND_THM, GSYM mapi_length_thm, LENGTH_TAKE, NOT_LESS_EQUAL, NOT_LESS] THEN rw []
THEN rfs [LENGTH_TAKE] THEN1 decide_tac THEN fs [GSYM INT] THEN `l < SUC (SUC n)` by decide_tac THEN fs []

THEN `SUC l < LENGTH P` by decide_tac
THEN `LENGTH (DROP (SUC l) P) = LENGTH P - (SUC l)` by fs [LENGTH_DROP]
THEN `n - l < LENGTH (DROP (SUC l) P)` by decide_tac
THEN fs [EL_MAPi_thm]

THEN fs []

THEN rw [] THEN FULL_SIMP_TAC (srw_ss () ++ ARITH_ss) [] THEN rw []

THEN `(n-l) + (SUC l) < LENGTH P` by decide_tac

THEN fs [drop_el]
THEN `n - l + SUC l = SUC n` by decide_tac THEN fs [] THEN Cases_on `(EL (SUC n) P)` THEN fs [rw_ba_def] THEN fsa [vsm_exec_c_instr_cases])
THEN1 (rwa [INT_LT_SUB_RADD, GSYM INT] THEN Cases_on `LENGTH (nop_elim P l) = LENGTH P` THEN1 decide_tac THEN `SUC (LENGTH (nop_elim P l)) = LENGTH P` by metis_tac [nop_elim_length] THEN decide_tac)
THEN1 (
fs [NOT_LESS, GSYM INT]
THEN rw [nop_elim_def] THEN1 decide_tac
THEN `ipc < l` by decide_tac
THEN `~(l < SUC ipc)` by decide_tac THEN fs []
THEN fs [NOT_LESS_EQUAL, NOT_LESS]
THEN `LENGTH P = SUC (LENGTH (MAPi (rw_for (&l)) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P)))` by (`l <= LENGTH P` by decide_tac THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac)

THEN `ipc < (LENGTH (MAPi (rw_for (&l)) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P)))` by decide_tac

THEN imp_res_tac FETCH_EL THEN fs [FETCH_EL] THEN `l <= LENGTH P` by decide_tac

THEN rw [EL_APPEND_THM] THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN rfs [LENGTH_TAKE] THEN rw []
THEN `l < LENGTH P` by decide_tac THEN fs [EL_MAPi_thm, take_el] THEN Cases_on `EL ipc P` THEN fs [rw_for_def] THEN fsa [vsm_exec_c_instr_cases]))
THEN fs [make_pair_def] THEN rw [] THEN fsa [GSYM INT] THEN (TRY (`l < SUC ipc` by decide_tac)) THEN (TRY (`~(l < SUC ipc)` by decide_tac)) THEN fs [] THEN `&SUC ipc - 1 = &ipc` by rwa [] THEN fs [])

THEN (REVERSE (rw [] THEN fs []))

THEN1 (rw [] THEN fs [vsm_exec_c_instr_cases] THEN rw [] THEN `(SOME (&ipc,clk,r')) = (SOME (pc'',clk'',r'''))` by (imp_res_tac nice_halt_thm THEN fs [] THEN rw []) THEN rw [] THEN fs [] THEN rw [] THEN Q.EXISTS_TAC `SOME (q'', clk, r')` THEN fs [RTC_REFL] THEN
fs [make_pair_def] THEN rw []
THEN rw [nop_elim_def] THEN fs [] THEN1 decide_tac THEN fs [NOT_LESS_EQUAL] THEN rw []
THEN `l <= LENGTH P` by decide_tac
THEN1 (
Cases_on `ipc` THEN rwa []
THEN `&SUC n - 1 = &n` by rwa [] THEN rw [] THEN rwa [vsm_exec_c_one_cases, int_ge, INT_SUB_LE, INT_SUB_LT, GSYM INT, GSYM mapi_length_thm, LENGTH_TAKE] THEN fs []
THEN (TRY (decide_tac)) THEN rw []

THEN `SUC (LENGTH (MAPi (rw_for &l) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P))) = LENGTH P` by (rw [GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac)

THEN `n < LENGTH
           (MAPi (rw_for &l) (TAKE l P) ++
            MAPi rw_ba (DROP (SUC l) P))` by decide_tac

THEN rw [FETCH_EL]

THEN fs [EL_APPEND_THM] THEN rw [] THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN rfs [] THEN1 decide_tac
THEN `n - l < LENGTH (DROP (SUC l) P)` by (rw [GSYM mapi_length_thm, LENGTH_DROP] THEN decide_tac)

THEN fs [drop_el, EL_MAPi_thm] THEN `(n-l) + (SUC l) < LENGTH P` by decide_tac THEN rw [drop_el] THEN `n - l + SUC l = SUC n` by decide_tac THEN rw [] THEN rw [rw_ba_def, vsm_exec_c_instr_cases])

THEN rwa [vsm_exec_c_one_cases, int_ge, INT_SUB_LE, INT_SUB_LT, GSYM INT, GSYM mapi_length_thm, LENGTH_TAKE] THEN fs [] THEN1 decide_tac

THEN `SUC (LENGTH (MAPi (rw_for &l) (TAKE l P) ++
   MAPi rw_ba (DROP (SUC l) P))) = LENGTH P` by (rw [GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac)

THEN `ipc < LENGTH
           (MAPi (rw_for &l) (TAKE l P) ++
            MAPi rw_ba (DROP (SUC l) P))` by decide_tac

THEN (REVERSE (rw [FETCH_EL, EL_APPEND_THM] THEN fs [GSYM mapi_length_thm, LENGTH_TAKE] THEN rfs [])) THEN1 decide_tac

THEN rw [EL_MAPi_thm, take_el, rw_for_def, vsm_exec_c_instr_cases])
THEN1 cheat

THEN rw [] THEN fs [vsm_exec_c_instr_cases] THEN rw [] THEN fs [make_pair_def] THEN rw []
THEN fs [] THEN HINT_EXISTS_TAC THEN fsa [] THEN rw [GSYM INT] THEN 

rwa [vsm_exec_c_one_cases, int_ge, INT_SUB_LE, INT_SUB_LT, GSYM INT, GSYM mapi_length_thm, LENGTH_TAKE] THEN fs [] THEN (TRY  decide_tac)
THEN (TRY (Cases_on `ipc` THEN rwa [] THEN rw [INT_SUB_LE] THEN `&SUC n - 1 = &n` by rwa [] THEN rw [] THEN fs []
THEN (TRY (`LENGTH P <= SUC (LENGTH (nop_elim P l))` by (`l <= LENGTH P` by decide_tac THEN rw [nop_elim_def, GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac) THEN decide_tac)) THEN rw []


THEN ((`n < LENGTH (nop_elim P l)`  by metis_tac [length_nop_elim] )
THEN fs [nop_elim_fetch, nop_elim_def] THEN rw [] THEN1 decide_tac THEN res_tac THEN rfs [] THEN fs [] THEN

rw [EL_APPEND_THM] THEN `l <= LENGTH P` by decide_tac THEN `(n - l) + (SUC l) < LENGTH P` by decide_tac
THEN fs [GSYM mapi_length_thm, LENGTH_TAKE, take_el, drop_el, EL_MAPi_thm] THEN1 decide_tac

THEN `(n - l) < LENGTH (DROP (SUC l) P)` by (rw [LENGTH_DROP] THEN decide_tac)

THEN rw [EL_MAPi_thm] THEN rw [drop_el] THEN `n - l + SUC l = SUC n` by decide_tac THEN rw [] THEN rwa [rw_ba_def, vsm_exec_c_instr_cases]
THEN `l <= n` by decide_tac
THEN fs [cast_sub] THEN fs [INT_NOT_LT] THEN fsa [] THEN rw [])))


THEN (TRY (fs [GSYM INT] THEN `ipc < l` by decide_tac

THEN `SUC ipc < LENGTH P` by decide_tac

THEN rwa [] THEN rw [INT_SUB_LE] THEN rw [] THEN fs []
THEN (TRY (`LENGTH P <= SUC (LENGTH (nop_elim P l))` by (`l <= LENGTH P` by decide_tac THEN rw [nop_elim_def, GSYM mapi_length_thm, LENGTH_TAKE] THEN decide_tac) THEN decide_tac)) THEN rw []


THEN (`ipc < LENGTH (nop_elim P l)`  by metis_tac [length_nop_elim] )
THEN fs [nop_elim_fetch, nop_elim_def] THEN rw [] THEN1 decide_tac THEN res_tac THEN rfs [] THEN fs [] THEN

rw [EL_APPEND_THM] THEN `l <= LENGTH P` by decide_tac
THEN fs [GSYM mapi_length_thm, LENGTH_TAKE, take_el, drop_el, EL_MAPi_thm] THEN fs [rw_for_def] THEN rw [vsm_exec_c_instr_cases] THEN fsa [])))))

val nopr_safe_1 = prove(``!P clk stk l.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (nop_elim P l) (SOME (0, clk, stk)) NONE``,
rw [nop_elim_def] THEN fs []

THEN ` (SOME (0,clk,stk),SOME (0, clk, stk)) ∈ bisim_set P l ⇒
          (NONE,NONE) ∈ bisim_set P l ⇒ vsm_exec_c (nop_elim P l) (SOME (0, clk, stk)) NONE` by (imp_res_tac remove_nop_sound THEN rw [bisim_set_def]) THEN fs [bisim_set_def, NOT_LESS_EQUAL] THEN rfs [make_pair_def] THEN fs [GSYM NOT_LESS_EQUAL, nop_elim_def] THEN metis_tac [])

val nopr_safe_2 = prove(``!P clk stk l clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (nop_elim P l) (SOME (0, clk, stk)) (SOME (&LENGTH (nop_elim P l), clk', stk'))``,
rw [] THEN Cases_on `(EL l P <> VSM_Nop)  \/ (LENGTH P <= l)` THEN fs [] THEN imp_res_tac remove_nop_sound THEN fs [bisim_set_def] THEN rfs []

THEN fs [SPECIFICATION] THEN (TRY (`nop_elim P l = P` by all_tac THEN fs [nop_elim_def] THEN rw [] THEN FAIL_TAC ""))

THEN `make_pair l (&LENGTH P) clk' stk' = (SOME (&LENGTH P, clk', stk'), SOME (&LENGTH (nop_elim P l), clk', stk')) ` by (

fs [make_pair_def, NOT_LESS_EQUAL] THEN fs [nop_elim_def, GSYM NOT_LESS_EQUAL, GSYM mapi_length_thm] THEN `l <= LENGTH P` by decide_tac THEN fs [LENGTH_TAKE] THEN rwa [] THEN Cases_on `LENGTH P` THEN fs [] THEN `&SUC n - 1 = &n` by fsa [] THEN rw [] THEN decide_tac)

THEN `make_pair l 0 clk stk = (SOME (0, clk, stk), SOME (0, clk, stk))` by fs [make_pair_def]

THEN fs [NOT_LESS_EQUAL]

THEN `
     vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ⇒
       (SOME (0, clk, stk), SOME (0, clk, stk)) ∈ bisim_set P l ⇒
       (SOME (&LENGTH P, clk', stk'), SOME (&LENGTH (nop_elim P l), clk', stk')) ∈ bisim_set P l ⇒
       vsm_exec_c (nop_elim P l) (SOME (0, clk, stk)) (SOME (&LENGTH (nop_elim P l), clk', stk'))` by metis_tac [remove_nop_sound]

THEN rfs [] THEN fs [bisim_set_def, make_pair_def] THEN rfs [])

val nop_elim_length2 = prove(``
!P l.(LENGTH P = LENGTH (nop_elim P l)) ==> (P = nop_elim P l)``,
rw []
THEN fs [nop_elim_def] THEN rw [] THEN fs [] THEN fs [GSYM mapi_length_thm, NOT_LESS_EQUAL] THEN `l <= LENGTH P` by decide_tac THEN fs [LENGTH_TAKE] THEN `SUC(LENGTH P) = l + (LENGTH P - SUC l)` by decide_tac THEN `SUC (LENGTH P) = LENGTH P` by decide_tac THEN `!x.SUC x <> x` by (rw [] THEN decide_tac) THEN fs [])


val ffp_def = tDefine "ffp" `ffp P l = let newP = nop_elim P l
                                in if P = newP then P else ffp newP l`
(WF_REL_TAC `measure (\(P, l).LENGTH P)` THEN rw []
THEN `(LENGTH P = LENGTH (nop_elim P l)) \/ (SUC (LENGTH (nop_elim P l)) = LENGTH P)` by metis_tac [nop_elim_length]
THEN1 metis_tac [nop_elim_length2]
THEN decide_tac)


val ffp_fp = prove(``!P l.ffp P l = ffp (nop_elim P l) l``,
recInduct (fetch "-" "ffp_ind") THEN rw [] THEN rw [Once ffp_def] THEN rw [] THEN rw [Once ffp_def] THEN rw [LET_DEF])

val ffp_safe_1 = prove(``!P l clk stk.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (ffp P l) (SOME (0, clk, stk)) NONE``,
recInduct (fetch "-" "ffp_ind") THEN rw [] THEN rw [Once ffp_def] THEN rw [] THEN fs [] THEN metis_tac [nopr_safe_1])

val ffp_safe_2 = prove(``!P l clk stk clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (ffp P l) (SOME (0, clk, stk)) (SOME (&LENGTH (ffp P l), clk', stk'))``,
recInduct (fetch "-" "ffp_ind") THEN rw [] THEN rw [] THEN fs [] THEN 
Cases_on `P <> nop_elim P l` THEN fs []
THEN1 metis_tac [ffp_fp, nopr_safe_2]
THEN rw [Once ffp_def] THEN rw [Once ffp_def, LET_DEF])

val c_nopr_def = Define `(c_nopr P 0 = ffp P 0) /\ (c_nopr P (SUC n) = ffp (c_nopr P n) (SUC n))`

val c_nopr_1_thm = prove(``
!P clk stk n.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (c_nopr P n) (SOME (0, clk, stk)) NONE
``,
Induct_on `n` THEN rw [] THEN metis_tac [ffp_safe_1, c_nopr_def])

val c_nopr_2_thm = prove(``
!P clk stk n clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (c_nopr P n) (SOME (0, clk, stk)) (SOME (&LENGTH (c_nopr P n), clk', stk'))
``,
Induct_on `n` THEN rw [] THEN metis_tac [ffp_safe_2, c_nopr_def])

val comp_nopr_def = Define `comp_nopr P = c_nopr P (LENGTH P)`

val comp_nopr_1_thm = store_thm("comp_nopr_1_thm", ``
!P clk stk.vsm_exec_c P (SOME (0, clk, stk)) NONE ==> vsm_exec_c (comp_nopr P) (SOME (0, clk, stk)) NONE
``, metis_tac [comp_nopr_def, c_nopr_1_thm])

val comp_nopr_2_thm = store_thm("comp_nopr_2_thm", ``
!P clk stk clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (comp_nopr P) (SOME (0, clk, stk)) (SOME (&LENGTH (comp_nopr P), clk', stk'))
``, metis_tac [comp_nopr_def, c_nopr_2_thm])

val _ = export_theory ()
