# CPSVerification
A repository for Isabelle modules to implement verification of Cyber-Physical Systems

As of 2019, there are four different formalizations of similar results. They depend on the codification of systems of Ordinary Differential Equations and on the implementation of the semantics. These are:
* Relational semantics with list representation.
* Relational semantics with vector codification.
* Nondeterministic functions semantics with vector representation.
* Semantics using generalized functions with a vector codification.

To run all these versions smoothly you need to have [Isabelle2018 (August 2018)](https://isabelle.in.tum.de/) installed in your computer. Moreover, they all depend on the [AFP](https://www.isa-afp.org/) entry on [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html). The theory stack behind this entry is enormous as it uses many theorems from [Analysis](http://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/index.html). As a consequence, the verification of this stack takes about 40 minutes which is the reason why we recommend pre-loading them, i.e. building a heap for those files. In order to do that in a Unix system just:
1. Open Terminal.
2. Add the Isabelle bin directory to your path, e.g., $ export PATH=$PATH:/Apps/.../Isabelle2017/bin (replace the ... with the actual path to the Isabelle installation directory).
3. Then execute: $ isabelle build -b Ordinary_Differential_Equations
4. Wait for the build to finish, go for tea or coffee. 
5. To launch, just type $ isabelle jedit -l Ordinary_Differential_Equations

**NOTE:** The build command, is only necessary once. After that, you just need to do step 2 and launch (step 5).

The files implementing a relational semantics require a modified version of [Program Construction and Verification Components Based on Kleene Algebra](https://www.isa-afp.org/entries/Algebraic_VCs.html), which you can download directly from this online repository (the folder afpModified. Alternatively, if you are Isabelle savvy, you could use the original AFP entry commenting-out the conflicting instantiations in it [everything from the second subsection of the theory Kleene_Algebra_Models.thy -except for the first lemma (Un_0_Suc)-, to just before the subsection called Relation Kleene Algebras].
