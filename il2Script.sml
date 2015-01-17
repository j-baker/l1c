open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory l1Theory pred_setTheory pairTheory lcsymtacs il1Theory integerTheory;

val _ = new_theory "il2";

val _ = type_abbrev("il2_expr", ``:il1_expr``);

val _ = Hol_datatype `il2_stm = IL2_Nop
                              | IL2_Push of int
                              | IL2_Load of loc
                              | IL2_Store of loc
                              | IL2_Pop
                              | IL2_Plus
                              | IL2_Halt
                              | IL2_Jump of int
                              | IL2_Jgeq of int`;

val _ = type_abbrev("il2_prog", ``:(il2_stm list)``);

val fetch_def = Define `fetch (x::xs) n = if n = &0 then x else fetch xs (n-1)`;
val _ = Parse.overload_on("!!", ``fetch``);

val FETCH_SUC_THM = store_thm("FETCH_SUC_THM",
``!x xs i.(i >= 0) ==> (xs !! i = (x::xs) !! (i+1))``,
rw [fetch_def] THEN1
full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) []
THEN `i + 1 - 1 = i` by full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss) [] THEN rw []);

val fsa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);
val rwa = full_simp_tac (srw_ss () ++ intSimps.INT_ARITH_ss);

val fetch_append_thm = store_thm("fetch_append_thm",
``!i xs ys.(&0 <= i) ==> ((xs ++ ys) !! i = (if i < &LENGTH xs then xs !! i else ys !! (i - &LENGTH xs)))``,
Induct_on `xs` THEN rw []

THEN1 metis_tac [int_le]

THEN1 (Cases_on `i = 0` THEN rw [APPEND, fetch_def]

THEN `xs ++ ys !! (i-1) = xs !! (i-1)` by (`0 <= (i-1)` by fsa [] THEN `i - 1 < &LENGTH xs` by fsa [] THEN metis_tac []))

THEN fsa [INT_NOT_LT]

THEN `~(i-1 < &LENGTH xs)` by fsa []
THEN `xs ++ ys !! (i-1) = ys !! (i-1) - &LENGTH xs` by (fsa [])

THEN Cases_on `i = 0` THEN fsa [APPEND, fetch_def] THEN rw []
THEN fsa [INT]
THEN `i - 1 - &LENGTH xs = i - (&LENGTH xs + 1)` by fsa [INT, INT_SUB_LNEG, INT_ADD_COMM]
THEN rw []);

val LIST_APPEND_THM = store_thm("LIST_APPEND_THM",
``!xs.(xs ++ [] = xs)``,
rw [APPEND]);


val FETCH_RANGE_THM = store_thm("FETCH_RANGE_THM",
``!xs.&LENGTH xs > 0 ==> !n.(n >= &0) /\ (n < &(LENGTH xs)) ==> ?x.(xs !! n = x)``,
rw []);

val (exec_instr_rules, exec_instr_ind, exec_instr_cases) = Hol_reln `
(exec_instr IL2_Nop (pc, stk, st) (pc+1, stk, st)) /\
(exec_instr (IL2_Push n) (pc, stk, st) (pc+1, n::stk, st)) /\
(exec_instr (IL2_Load l) (pc, stk, st) (pc+1, (st ' l)::stk, st)) /\
(exec_instr (IL2_Store l) (pc, v::stk, st) (pc+1, stk, st |+ (l, v))) /\
(exec_instr IL2_Pop (pc, v::stk, st) (pc+1, stk, st)) /\
(exec_instr IL2_Plus (pc, v1::v2::stk, st) (pc+1, (v1+v2)::stk, st)) /\
(exec_instr IL2_Halt (pc, stk, st) (pc, stk, st)) /\
(exec_instr (IL2_Jump n) (pc, stk, st) (pc + 1 + n, stk, st)) /\
((v1 >= v2) ==> exec_instr (IL2_Jgeq n) (pc, v1::v2::stk, st) (pc + 1 + n, stk, st)) /\
((v1 < v2) ==> exec_instr (IL2_Jgeq n) (pc, v1::v2::stk, st) (pc + 1, stk, st))`;

val (exec_one_rules, exec_one_ind, exec_one_cases) = Hol_reln `
!instrs pc stk st pc' stk' st'.
       ((pc >= 0) /\ (pc < &(LENGTH instrs)) /\
        (exec_instr (instrs !! pc) (pc, stk, st) (pc', stk', st')))
    ==> exec_one instrs (pc, stk, st) (pc', stk', st')`;

val exec_def = Define `exec P c c' = (exec_one P)^* c c'`;

val _ = export_theory ();
