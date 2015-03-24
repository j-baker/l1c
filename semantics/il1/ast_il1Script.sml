open HolKernel boolLib bossLib listTheory Parse IndDefLib finite_mapTheory relationTheory arithmeticTheory ast_l1Theory bigstep_l1Theory pred_setTheory pairTheory lcsymtacs integerTheory

val _ = new_theory "ast_il1"

val _ = Datatype `il1_loc = User     loc
                          | Compiler loc` 

val _ = Datatype `il1_value = IL1_ESkip
                            | IL1_Integer int
                            | IL1_Boolean bool`

val _ = Datatype `il1_expr = IL1_Value il1_value
                           | IL1_Plus  il1_expr il1_expr
                           | IL1_Geq   il1_expr il1_expr
                           | IL1_Deref il1_loc
                           | IL1_EIf   il1_expr il1_expr il1_expr`

val _ = Datatype `il1_stm = IL1_Expr il1_expr
                          | IL1_Assign il1_loc  il1_expr
                          | IL1_Seq    il1_stm  il1_stm
                          | IL1_SIf    il1_expr il1_stm il1_stm
                          | IL1_While  il1_expr il1_stm
                          | IL1_Tick   il1_stm`

val _ = export_theory ()
