structure printerLib = struct

open ast_vsm0Theory Parse integerTheory

datatype ops = Nop
             | Tick
             | Push of int
             | Load of int
             | Store of int
             | Pop
             | Plus
             | Geq
             | Halt
             | Jump of int
             | Jz of int

fun op_to_string Nop = "nop"
  | op_to_string Tick = "tick"
  | op_to_string (Push x) = "push " ^ (Int.toString x)
  | op_to_string (Load x) = "load " ^ (Int.toString x)
  | op_to_string (Store x) = "store " ^ (Int.toString x)
  | op_to_string Pop = "pop"
  | op_to_string Plus = "plus"
  | op_to_string Geq = "geq"
  | op_to_string Halt = "halt"
  | op_to_string (Jump x) = "jump " ^ (Int.toString x) 
  | op_to_string (Jz x) = "jz " ^ (Int.toString x)

fun syntax_fns s n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} s

val s0 = syntax_fns "ast_vsm0" 0 HolKernel.dest_binder HolKernel.mk_monop
val s1 = syntax_fns "ast_vsm0" 1 HolKernel.dest_monop HolKernel.mk_monop

val nop_tm = prim_mk_const {Name = "VSM_Nop", Thy = "ast_vsm0"}
val tick_tm = prim_mk_const {Name = "VSM_Tick", Thy = "ast_vsm0"}
val push_tm = prim_mk_const {Name = "VSM_Push", Thy = "ast_vsm0"}
val load_tm = prim_mk_const {Name = "VSM_Load", Thy = "ast_vsm0"}
val store_tm = prim_mk_const {Name = "VSM_Store", Thy = "ast_vsm0"}
val pop_tm = prim_mk_const {Name = "VSM_Pop", Thy = "ast_vsm0"}
val plus_tm = prim_mk_const {Name = "VSM_Plus", Thy = "ast_vsm0"}
val geq_tm = prim_mk_const {Name = "VSM_Geq", Thy = "ast_vsm0"}
val halt_tm = prim_mk_const {Name = "VSM_Halt", Thy = "ast_vsm0"}
val jump_tm = prim_mk_const {Name = "VSM_Jump", Thy = "ast_vsm0"}
val jz_tm = prim_mk_const {Name = "VSM_Jz", Thy = "ast_vsm0"}

val dest_push = dest_monop push_tm (ERR "dest_push"      "not push")
val dest_load = dest_monop load_tm (ERR "dest_load"      "not load")
val dest_store = dest_monop store_tm (ERR "dest_store"      "not store")
val dest_jump = dest_monop jump_tm (ERR "dest_jump"      "not jump")
val dest_jz = dest_monop jz_tm (ERR "dest_jz"      "not jz")

fun rhs thm = snd (dest_eq (snd (dest_thm thm)))

fun ignore_unchanged conv x = conv x handle UNCHANGED => EVAL x

fun int_tm_to_int t = Arbintcore.toInt (intSyntax.int_of_term t)
fun num_tm_to_int t = Arbnumcore.toInt (numSyntax.dest_numeral t)

fun get_instr x = if same_const x nop_tm then Nop
else if same_const x tick_tm then Tick
else if same_const x pop_tm then Pop
else if same_const x plus_tm then Plus
else if same_const x geq_tm then Geq
else if same_const x halt_tm then Halt
else if can dest_push x then (Push (int_tm_to_int (dest_push x)))
else if can dest_load x then (Load (num_tm_to_int (dest_load x)))
else if can dest_store x then (Store (num_tm_to_int (dest_store x)))
else if can dest_jump x then (Jump (int_tm_to_int (dest_jump x)))
else (Jz (int_tm_to_int (dest_jz x)))

fun fst (a, b) = a

fun get_instructions prog = map get_instr (fst (listSyntax.dest_list prog))

fun print_prog instrs = List.app (fn x => print ((op_to_string x) ^ "\n")) instrs

end
