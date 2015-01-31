open HolKernel Parse boolLib bossLib integerTheory finite_mapTheory ast_l1Theory smallstep_l1Theory lcsymtacs pairTheory;

val _ = new_theory "l1_type";

val (l1_type_rules, l1_type_ind, l1_type_cases) = Hol_reln `
    (!g.l1_type (L1_Value L1_Skip) g unitL1) /\
    (!n g.l1_type (L1_Value (L1_Int n)) g intL1) /\
    (!b g.l1_type (L1_Value (L1_Bool b)) g boolL1) /\

    (!e1 e2 g.
       (l1_type e1 g intL1 /\
        l1_type e2 g intL1)
    ==> l1_type (L1_Plus e1 e2) g intL1) /\

    (!e1 e2 g.
       (l1_type e1 g intL1 /\
        l1_type e2 g intL1)
    ==> l1_type (L1_Geq e1 e2) g boolL1) /\


    (!e1 e2 e3 g t.
       (l1_type e1 g boolL1 /\
        l1_type e2 g t /\
        l1_type e3 g t)
    ==> l1_type (L1_If e1 e2 e3) g t) /\

    (!l e g.
       (l ∈ g /\
        l1_type e g intL1)
    ==> l1_type (L1_Assign l e) g unitL1) /\

    (!l g.
        l ∈ g
    ==> l1_type (L1_Deref l) g intL1) /\

    (!e1 e2 g t.
       (l1_type e1 g unitL1 /\
        l1_type e2 g t)
    ==> l1_type (L1_Seq e1 e2) g t) /\

    (!e1 e2 g.
       (l1_type e1 g boolL1 /\
        l1_type e2 g unitL1)
    ==> l1_type (L1_While e1 e2) g unitL1)`;

val _ = export_theory ();
