l1c: A simple verified toy compiler for a toy language
==========================================================

[![Build Status](https://travis-ci.org/j-baker/l1c.svg?branch=master)](https://travis-ci.org/j-baker/l1c)

This project was written for my University of Cambridge BA
Computer Science Part II dissertation.

l1c is a verified compiler for the L1
language presented in the Cambridge [Semantics of Programming Languages](http://www.cl.cam.ac.uk/teaching/1415/Semantics/notes.pdf) course.

The target language is a slight modification of the vsm0 VM
presented in the Cambridge [Compiler Construction](http://www.cl.cam.ac.uk/teaching/1314/CompConstr/materials.html) course.

The operational semantics of these two languages can be found in:

- [L1 small step](compiler/semantics/l1/smallstep_l1Script.sml)
- [L1 big step](compiler/semantics/l1/bigstep_l1Script.sml)
- [vsm0 small step](compiler/semantics/vsm0/smallstep_vsm0Script.sml)

The compiler is verified, meaning that there exists a proof that the compiler preserves the semantics of a program. The main correctness result can be found [here](compiler/compiler/compilerScript.sml).

The produced dissertation can be found in the dissertation directory. This repository is made available for illustration purposes; if you have a comprehension issue, feel free to file an issue.

Many thanks to Ramana Kumar and Magnus Myreen, who gave me important feedback over the course of the project.
