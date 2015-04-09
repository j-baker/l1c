open HolKernel bossLib Parse boolLib listTheory lcsymtacs smallstep_il2Theory relationTheory ast_vsm0Theory integerTheory smallstep_vsm0Theory

val _ = new_theory "smallstep_vsm0_clocked"

val (vsm_exec_c_instr_rules, vsm_exec_c_instr_ind, vsm_exec_c_instr_cases) = Hol_reln `
(!pc stk c.vsm_exec_c_instr VSM_Nop (SOME (pc, c, stk)) (SOME (pc+1, c, stk))) /\
(!pc stk c.vsm_exec_c_instr VSM_Tick (SOME (pc, SUC c, stk)) (SOME (pc+1, c, stk))) /\
(!pc stk.vsm_exec_c_instr VSM_Tick (SOME (pc, 0, stk)) NONE) /\
(!n pc stk c.vsm_exec_c_instr (VSM_Push n) (SOME (pc, c, stk)) (SOME (pc+1, c, n::stk))) /\
(!l pc stk c.vsm_exec_c_instr (VSM_Load l) (SOME (pc, c, stk)) (SOME (pc+1, c, (stk ?? l)::stk))) /\
(!l pc v stk c.vsm_exec_c_instr (VSM_Store l) (SOME (pc, c, v::stk)) (SOME (pc+1, c, update_loc stk l v))) /\
(!pc v stk c.vsm_exec_c_instr VSM_Pop (SOME (pc, c, v::stk)) (SOME (pc+1, c, stk))) /\
(!pc v1 v2 stk c.vsm_exec_c_instr VSM_Plus (SOME (pc, c, v1::v2::stk)) (SOME (pc+1, c, (v1+v2)::stk))) /\
(!pc stk c.vsm_exec_c_instr VSM_Halt (SOME (pc, c, stk)) (SOME (pc, c, stk))) /\
(!n pc stk c.vsm_exec_c_instr (VSM_Jump n) (SOME (pc, c, stk)) (SOME (pc + 1 + n, c, stk))) /\
(!n pc stk c.vsm_exec_c_instr (VSM_Jz n) (SOME (pc, c, 0::stk)) (SOME (pc + 1 + n, c, stk))) /\
(!n pc t stk c.(t <> 0) ==> vsm_exec_c_instr (VSM_Jz n) (SOME (pc, c, t::stk)) (SOME (pc + 1, c, stk))) /\
(!v1 v2 pc stk c.(v1 >= v2) ==> vsm_exec_c_instr (VSM_Geq) (SOME (pc, c, v1::v2::stk)) (SOME (pc + 1, c, true_value::stk))) /\
(!v1 v2 pc stk c.(v1 < v2) ==> vsm_exec_c_instr (VSM_Geq) (SOME (pc, c, v1::v2::stk)) (SOME (pc + 1, c, false_value::stk)))`

val (vsm_exec_c_one_rules, vsm_exec_c_one_ind, vsm_exec_c_one_cases) = Hol_reln `
!instrs pc clk stk r.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (vsm_exec_c_instr (instrs !! pc) (SOME (pc, clk, stk)) r))
    ==> vsm_exec_c_one instrs (SOME (pc, clk, stk)) r`

val vsm_exec_c_def = Define `vsm_exec_c P c c' = (vsm_exec_c_one P)^* c c'`

val _ = export_theory ()
