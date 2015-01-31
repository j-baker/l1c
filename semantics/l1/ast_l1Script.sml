open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory;

val _ = new_theory "ast_l1";

val _ = type_abbrev("loc", ``:num``);

val _ = type_abbrev("state", ``:loc |-> int``);

val _ = Datatype `l1_value = L1_Int int
                           | L1_Bool bool
                           | L1_Skip`;

val _ = Datatype `l1_expr = L1_Value  l1_value
                          | L1_Plus   l1_expr l1_expr
                          | L1_Geq    l1_expr l1_expr
                          | L1_If     l1_expr l1_expr l1_expr
                          | L1_Assign loc     l1_expr
                          | L1_Deref  loc
                          | L1_Seq    l1_expr l1_expr
                          | L1_While  l1_expr l1_expr`;

val _ = Datatype `T = intL1 | boolL1 | unitL1`;

val _ = export_theory ();
