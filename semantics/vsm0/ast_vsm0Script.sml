open HolKernel bossLib Parse integerTheory;

val _ = new_theory "ast_vsm0";

val _ = type_abbrev("vsm_loc", ``:num``);

val _ = Datatype `vsm_stm = VSM_Nop
                            | VSM_Push int
                            | VSM_Load vsm_loc
                            | VSM_Store vsm_loc
                            | VSM_Pop
                            | VSM_Plus
                            | VSM_Geq
                            | VSM_Halt
                            | VSM_Jump int
                            | VSM_Jz int`;

val _ = type_abbrev("vsm_prog", ``:(vsm_stm list)``);

val _ = export_theory ();
