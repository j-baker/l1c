open HolKernel Parse bossLib ast_il1Theory integerTheory;

val _ = new_theory "ast_il2";

val _ = Datatype `il2_stm = IL2_Nop
                          | IL2_Push  int
                          | IL2_Load  il1_loc
                          | IL2_Store il1_loc
                          | IL2_Pop
                          | IL2_Plus
                          | IL2_Geq 
                          | IL2_Halt
                          | IL2_Jump  int
                          | IL2_Jz    int`;

val _ = type_abbrev("il2_prog", ``:(il2_stm list)``);

val _ = export_theory ();
