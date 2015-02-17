Snorkel: A simple verified toy compiler for a toy language
==========================================================

[![Build Status](https://magnum.travis-ci.com/j-baker/partii.svg?token=KqfCygaVMsrvPPnULqeX&branch=develop)](https://magnum.travis-ci.com/j-baker/partii)

This project is written for my University of Cambridge BA
Computer Science Part II dissertation.

Snorkel (name pending) is a verified compiler for the L1
language presented in the Cambridge [Semantics of Programming Languages](http://www.cl.cam.ac.uk/teaching/1415/Semantics/notes.pdf) course.

The target language is a slight modification of the vsm0 VM
presented in the Cambridge [Compiler Construction](http://www.cl.cam.ac.uk/teaching/1314/CompConstr/materials.html) course.

The operational semantics of these two languages can be found in:

- [L1 small step](semantics/l1/smallstep_l1Script.sml)
- [L1 big step](semantics/l1/bigstep_l1Script.sml)
- [vsm0 small step](semantics/vsm0/smallstep_vsm0Script.sml)

The compiler is verified, meaning that there exists a proof that the compiler preserves the semantics of a program. The main correctness result can be found [here](compiler/compilerScript.sml).
