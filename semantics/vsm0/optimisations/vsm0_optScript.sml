open HolKernel bossLib boolLib lcsymtacs listTheory ast_vsm0Theory relationTheory smallstep_vsm0_clockedTheory integerTheory arithmeticTheory smallstep_il2Theory

val _ = new_theory "vsm0_opt"

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss)
val rwa = rw_tac (srw_ss () ++ intSimps.INT_ARITH_ss)

val MAPi_def = Define `(MAPi P [] = []) /\ (MAPi P (x::xs) = (P 0 x)::MAPi (P o SUC) xs)`

val EL_MAPi_thm = prove(``!P l n.n < LENGTH l ==> (EL n (MAPi P l) = P n (EL n l))``, Induct_on `l` THEN rw [] THEN rw [MAPi_def] THEN Cases_on `n` THEN rw [EL] THEN fs [])


val rw_for_def = Define `(rw_for len pc (VSM_Jump n) = if len <= &pc + n + 1 then (VSM_Jump (n - 2)) else VSM_Jump n)
/\ (rw_for len pc (VSM_Jz n) = if len <= &pc + n + 1 then (VSM_Jz (n - 2)) else VSM_Jump n)
/\ (rw_for len pc x = x)
`

val rw_ba_def = Define `(rw_ba pc (VSM_Jump n) = if &pc + n + 1 < 0 then (VSM_Jump (n + 2)) else VSM_Jump n)
/\ (rw_ba pc (VSM_Jz n) = if &pc + n + 1 < 0 then (VSM_Jz (n + 2)) else VSM_Jump n)
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
(MAPi (rw_for &LENGTH P) (TAKE l P)) ++ (MAPi rw_ba (DROP (SUC l) P))`

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
bisim_set P l = if (EL l P = VSM_Nop) /\ (l < LENGTH P) then {x | ?pc clk stk.(make_pair l pc clk stk = x)} else {(x, x) | T}`

val bisim_set_fun = prove(``!P l x y z.(x, y) ∈ bisim_set P l /\ (x, z) ∈ bisim_set P l ==> (y = z)``,
fs [bisim_set_def] THEN rw [] THEN fs [make_pair_def] THEN rw [] THEN fsa [])


val nj_def = Define `(nj x m (VSM_Jump n) = (&x <> (&m+n+1))) /\ (nj x m (VSM_Jz n) = (&x <> (&m+n+1))) /\ (nj _ _ _ = T)`

val no_jumps_def = Define `no_jumps l P = EVERYi (nj l) P`

val elim_pushpop_def = Define `
elim_pushpop P l = if (SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (?x.EL l P = VSM_Push x) /\ (EL (SUC l) P = VSM_Pop) then LUPDATE VSM_Nop l (LUPDATE VSM_Nop (SUC l) P) else P
`

val el_pp_bs_set_def = Define `
el_pp_bs_set P l = if (l < LENGTH P) then {(x, x) | (?pc clk stk.(x = SOME (pc, clk, stk)) /\ (pc <> &(SUC l))) \/ (x = NONE)} ∪ 
{(x, y) | ?clk stk e.(x = SOME (&(SUC l), clk, e::stk)) /\ (y = SOME (&(SUC l), clk, stk))}

else {(x, x) | T}`

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
THEN Cases_on `(SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (?x.EL l P = VSM_Push x) /\ (EL (SUC l) P = VSM_Pop)` THEN fs []
THEN1 (imp_res_tac plus_sound_thm THEN fs [el_pp_bs_set_def] THEN `l < LENGTH P` by decide_tac THEN fs []) THEN rw [elim_pushpop_def])

val pushpop_safe_2 = prove(``!P clk stk l clk' stk'.vsm_exec_c P (SOME (0, clk, stk)) (SOME (&LENGTH P, clk', stk')) ==> vsm_exec_c (elim_pushpop P l) (SOME (0, clk, stk)) (SOME (&LENGTH (elim_pushpop P l), clk', stk'))``,
rw []
THEN Cases_on `(SUC l < LENGTH P) /\ (no_jumps (SUC l) P) /\ (?x.EL l P = VSM_Push x) /\ (EL (SUC l) P = VSM_Pop)` THEN fs []
THEN1 (imp_res_tac plus_sound_thm THEN fs [el_pp_bs_set_def] THEN `l < LENGTH P` by decide_tac THEN fs [] THEN Cases_on `LENGTH P <> SUC l` THEN fs [] THEN fs [elim_pushpop_def] THEN rfs []) THEN rw [elim_pushpop_def])

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

val _ = export_theory ()
