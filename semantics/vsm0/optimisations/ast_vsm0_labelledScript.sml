open HolKernel bossLib Parse integerTheory smallstep_vsm0Theory relationTheory pairTheory arithmeticTheory

val _ = new_theory "ast_vsm0_labelled"

val _ = Datatype `vsm_l_op = VSML_Nop
| VSML_Tick
| VSML_Push int
| VSML_Load num
| VSML_Store num
| VSML_Pop
| VSML_Plus
| VSML_Geq`;

val _ = type_abbrev("vsm_bb", ``:(vsm_l_op list)``)

val _ = Datatype `vsm_l_jmp = Jump num
                            | Jz num
                            | None`;   

val _ = type_abbrev("vsm_l_prog", ``:((vsm_l_jmp # vsm_bb) list)``);

val (bb_ei_rules, bb_ei_ind, bb_ei_cases) = Hol_reln `
(!stk.bb_ei VSML_Nop stk stk) /\
(!stk.bb_ei VSML_Nop stk stk) /\
(!n stk.bb_ei (VSML_Push n) stk (n::stk)) /\
(!l stk.bb_ei (VSML_Load l) stk ((stk ?? l)::stk)) /\
(!l v stk.bb_ei (VSML_Store l) stk (update_loc stk l v)) /\
(!v stk.bb_ei VSML_Pop (v::stk) stk) /\
(!v1 v2 stk.bb_ei VSML_Plus (v1::v2::stk) ((v1+v2)::stk)) /\
(!v1 v2 stk.(v1 >= v2) ==> bb_ei VSML_Geq (v1::v2::stk) (true_value::stk)) /\
(!v1 v2 stk.(v1 < v2) ==> bb_ei VSML_Geq (v1::v2::stk) (false_value::stk))`;

val (ebbo_rules, ebbo_ind, ebbo_cases) = Hol_reln `
!b bb stk stk'.
(bb_ei b stk stk') ==> ebbo (b::bb, stk) (bb, stk')`;

val (ebb_rules, ebb_ind, ebb_cases) = Hol_reln `
!bb stk stk'.ebbo^* (bb, stk) ([], stk') ==> ebb bb stk stk'`;


val (ep_rules, ep_ind, ep_cases) = Hol_reln `
(!bbp prog stk stk' nbbp bb.
(bbp < LENGTH prog) /\
(EL bbp prog = (Jump nbbp, bb)) /\
(ebb bb stk stk') ==> ep prog (bbp, stk) (nbbp, stk')) /\
(!bbp prog stk stk' nbbp bb.
(bbp < LENGTH prog) /\
(EL bbp prog = (Jz nbbp, bb)) /\
(ebb bb stk (0::stk')) ==> ep prog (bbp, stk) (nbbp, stk')) /\
(!bbp prog stk stk' nbbp bb x.
(x <> 0) /\
(bbp < LENGTH prog) /\
(EL bbp prog = (Jz nbbp, bb)) /\
(ebb bb stk (x::stk')) ==> ep prog (bbp, stk) (bbp + 1, stk')) /\
(!bbp prog stk stk' bb.
(bbp < LENGTH prog) /\
(EL bbp prog = (None, bb)) /\
(ebb bb stk stk') ==> ep prog (bbp, stk) (bbp + 1, stk'))`;


val sp_def = Define `(sp [] = []) /\ (sp (VSML_Push x :: VSML_Pop :: bb) = sp bb) /\ (sp (b::bb) = b::sp bb)`;


val sound_thm = prove(``!bb stk stk'.ebb bb stk stk' ==> ebb (sp bb) stk stk'``,

Induct_on `bb` THEN rw [ebb_cases, sp_def] THEN Induct_on `bb` THEN rw [ebb_cases, sp_def] THEN1 (Cases_on `h` THEN fs [sp_def])

THEN Cases_on `h` THEN Cases_on `h'` THEN fs [sp_def] THEN rw []

THEN (TRY (imp_res_tac RTC_CASES1 THEN imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [] THEN fs [bb_ei_cases] THEN rw [] THEN rw [Once RTC_CASES1] THEN rw [ebbo_cases, bb_ei_cases] THEN FAIL_TAC "fail"))

THEN1 (imp_res_tac RTC_CASES1 THEN imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [] THEN fs [bb_ei_cases] THEN rw [] THEN res_tac THEN rw [] THEN imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [] THEN fs[bb_ei_cases] THEN rw [])

THEN imp_res_tac RTC_CASES1 THEN imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [] THEN fs [bb_ei_cases] THEN rw []  THEN res_tac THEN fs [] THEN rw []

THEN rw [Once RTC_CASES1] THEN rw [ebbo_cases, bb_ei_cases] THEN metis_tac []);


val bb_det = prove(``!bb stk stk'.ebb bb stk stk' ==> !stk''.ebb bb stk stk'' ==> (stk' = stk'')
``,

Induct_on `bb` THEN rw [ebb_cases] THEN1 (imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [])

THEN fs [ebb_cases] THEN Cases_on `h` THEN (TRY (imp_res_tac RTC_CASES1 THEN fs [ebbo_cases] THEN rw [] THEN fs [bb_ei_cases] THEN rw [] THEN FULL_SIMP_TAC (srw_ss () ++ intSimps.INT_ARITH_ss) [int_ge] THEN metis_tac []))


Cases_on `stk` THEN1 


fs [ebbo_cases]


val replace_sound = prove(``!prog c c'.(ep prog)^* c c' ==> !n bb.(!stk stk'.ebb (SND (EL n prog)) stk stk' ==> ebb bb stk stk') ==> (ep (LUPDATE (FST (EL n prog), bb) n prog))^* c c'``,

STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN Cases_on `c` THEN Cases_on `EL q prog` THEN fs [FST, SND]

THEN rw [Once RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `c'` THEN Cases_on `c'` THEN Cases_on `c''` THEN fs [FST, SND]

THEN Cases_on `EL q'' prog` THEN fs [FST, SND]

THEN rw [ep_cases] THEN rw [EL_LUPDATE] THEN Cases_on `q'` THEN rw [] THEN fs [ep_cases] THEN rw [] THEN metis_tac []);


val simp_bb_def = Define `simp_bb si (a, b) = (a, si b)`;

val pop_1 = prove(``!prog c c'.(ep prog)^* c c' ==> (ep (MAP (simp_bb sp) prog))^* c c'``,

STRIP_TAC THEN ho_match_mp_tac RTC_STRONG_INDUCT THEN rw [] THEN rw [Once RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `c'` THEN rw [] THEN fs [ep_cases] THEN rw [EL_LUPDATE]
THEN imp_res_tac sound_thm THEN rw [EL_MAP, simp_bb_def] THEN metis_tac []);



val cannot_jump_to_n_def = Define `(cannot_jump_to_n n pc (VSM_Jump x) = (&pc + x + 1 <> n)) /\
(cannot_jump_to_n n pc (VSM_Jz x) = ((&pc + x + 1) <> n)) /\
(cannot_jump_to_n n pc _ = T)`;

val no_jumps_to_instr_def = Define `no_jumps_to_instr prog n = EVERYi (cannot_jump_to_n (&n)) prog`;


val in_is_jmp_def = Define `(in_is_jmp (VSM_Jump x) = T) /\ (in_is_jmp (VSM_Jz x) = T) /\ (in_is_jmp _ = F)`;

val get_bb_len_def = bossLib.tDefine "get_bb_len" `get_bb_len prog start_ind = if (start_ind >= LENGTH prog) then 0 else

if (~no_jumps_to_instr prog (SUC start_ind) \/ (in_is_jmp (EL start_ind prog)))
                                                         then (1:num)
                                                         else 1 + get_bb_len prog (SUC start_ind)` (WF_REL_TAC `measure (\ (x, a).LENGTH x - a)`);

val bbs_def = bossLib.tDefine "bbs" `(bbs prog pc [] = []) /\ (bbs prog pc (i::ins : vsm_prog) = if (pc >= LENGTH prog) then [] else let length = get_bb_len prog pc
in (if length <= 0 then [i]::(bbs prog (pc + 1) ins)
   else (TAKE length (i::ins))::(bbs prog (pc + length) (DROP length (i::ins)))))` (WF_REL_TAC `measure (\(prog, pc, prog').LENGTH prog - pc)`); 

val testD = ``[VSM_Push 0; VSM_Pop; VSM_Push 5; VSM_Push 3; VSM_Push 1; VSM_Jz (-4); VSM_Plus; VSM_Jump (-6)]``;

val foo = EVAL ``MAP conv_bb (bbs ^testD 0 ^testD)``;

val conv_bb_def = Define `(conv_bb [] = (NONE, [])) /\ (conv_bb [VSM_Jump x] = (SOME (VSM_Jump x), [])) /\ (conv_bb [VSM_Jz x] = (SOME (VSM_Jz x), [])) /\ (conv_bb (b::bs) = let (t1, t2) = conv_bb bs in (t1, b::t2))`;

val len_cnt_def = Define `(len_cnt (NONE, bb) = LENGTH bb) /\ (len_cnt (SOME x, bb) = LENGTH bb + 1)`

val fjump_def = Define `(fjump n (x::xs) = if n = (-1) then 1 else  fjump (n - &(len_cnt x)) xs) /\ (fjump n [] = if n = (-1) then 1 else ARB)`

val fj_def = Define `(fj [] = []) /\ (fj ((NONE, bb)::bbs) = SOME 1::fj bbs) /\ (fj ((SOME (VSM_Jump x), bb)::bbs) = if 0 <= x then SOME (fjump x bbs)::(fj bbs) else NONE::(fj bbs)) /\ (fj ((SOME (VSM_Jz x), bb)::bbs) = if 0 <= x then SOME (fjump x bbs)::(fj bbs) else NONE::(fj bbs))`;

val t2 = ``[VSM_Jump 1; VSM_Jump 1; VSM_Pop; VSM_Pop]``

val st1 = EVAL ``MAP conv_bb (bbs ^t2 0 ^t2)``;

val st = EVAL ``fj (MAP conv_bb (bbs ^t2 0 ^t2))``;

val st = EVAL ``ZIP (fj (MAP conv_bb (bbs ^testD 0 ^testD)), MAP conv_bb (bbs ^testD 0 ^testD))``;

val nums_def = Define `nums n = GENLIST (\x.&x) n`;

val pair_sum_def = Define `pair_sum xs ys = MAP (\(x, y).x + y) (ZIP (xs, ys))`;

val st2 = EVAL ``pair_sum (nums (LENGTH ^t2)) (fj (MAP conv_bb (bbs ^t2 0 ^t2)))``;

val get_jmp_dest = Define `get_jmp_dest remn n prog = if remn = 0 then SOME n else (if remn < 0 then NONE else get_jmp_dest (remn - (len_cnt (EL n prog))) (n+1) prog)`

get_jmp_dest (remn + (len_cnt (EL n prog))) (n-1) prog



val sumn_def = Define `(sumn _ [] = []) /\ (sumn acc (x::xs) = (acc + len_cnt x) :: (sumn (acc + (len_cnt x)) xs))`

val x = EVAL ``sumn 0 (MAP conv_bb (bbs ^testD 0 ^testD))``
val y = EVAL ``(MAP conv_bb (bbs ^testD 0 ^testD))``;

val new_pc_def = Define `(new_pc pc NONE = pc + 1) /\ (new_pc pc (SOME (VSM_Jump n)) = pc + 1 + n) /\ (new_pc pc (SOME (VSM_Jz n)) = pc + 1 + n)`;

val find_pc_def = Define `(find_pc pc [] = 0) /\ (find_pc pc (x::xs) = if (x = pc) then 0 else 1 + find_pc pc xs)`




val _ = export_theory ()
