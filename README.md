# CPSVerification
A repository for Isabelle modules to implement verification of Cyber-Physical Systems

As of 2018, the main file is VC_diffKAD.thy
To run it smoothly you need to have [Isabelle2017 (October 2017)](https://isabelle.in.tum.de/) installed in your computer.
It also depends on two [AFP](https://www.isa-afp.org/) entries:
* A modified version of [Program Construction and Verification Components Based on Kleene Algebra](https://www.isa-afp.org/entries/Algebraic_VCs.html), which you can download directly from this online repository. Alternatively, you could also comment-out the conflicting instantiations in said entry. That is, everything from the second subsection of the theory Kleene_Algebra_Models.thy -except for the first lemma (Un_0_Suc)-, to just before the subsection called Relation Kleene Algebras.
* [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html)
The AFP-entry on Ordinary Differential Equations needs to load a lot of theorems from [Analysis](http://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/index.html). Therefore, we recommend pre-loading them, i.e. building a heap for those files. In order to do that in a Unix system just:
1. Open Terminal.
2. Add the Isabelle bin directory to your path, e.g., $ export PATH=$PATH:/Apps/.../Isabelle2017/bin (replace the ... with the actual path to the Isabelle installation directory).
3. Then execute: $ isabelle build -b Ordinary_Differential_Equations
4. Wait for the build to finish, go for tea or coffee. 
5. To launch, just type $ isabelle jedit -l Ordinary_Differential_Equations
**NOTE:** The build command, is only necessary once. After that, you just need to modify your PATH (step 2) and launch (step 5).
