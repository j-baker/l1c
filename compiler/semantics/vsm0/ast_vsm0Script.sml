open HolKernel bossLib Parse integerTheory

val _ = new_theory "ast_vsm0"

val _ = Datatype `vsm_stm = VSM_Nop
                          | VSM_Tick
                          | VSM_Push int
                          | VSM_Load num
                          | VSM_Store num
                          | VSM_Pop
                          | VSM_Plus
                          | VSM_Geq
                          | VSM_Halt
                          | VSM_Jump int
                          | VSM_Jz int`

val _ = type_abbrev("vsm_prog", ``:(vsm_stm list)``)

val _ = export_theory ()
