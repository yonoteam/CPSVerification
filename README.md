# Hybrid Systems Verification
A repository for Isabelle modules to implement verification of Hybrid Systems, a model for Cyber-Physical Systems.

As of mid 2019, there are various different formalizations of similar results. The differences depend on the codification of systems of Ordinary Differential Equations and on the implementation of the semantics. Generally, the implementations are:
* Relational semantics with list representation (in folder HybridVerifLists).
* Relational semantics with vector codification (in folder HybridVerifVecs/rels).
* Nondeterministic functions semantics with vector representation (in folder HybridVerifVecs/nd_funs).
* Semantics using generalized functions with a vector codification (in folder HybridVerifVecs/funcsets). This one is extended to work with the general solution for linear systems of ODEs.

Every file runs smoothly with [Isabelle2019 (August 2019)](https://isabelle.in.tum.de/). Moreover, they all depend on the [AFP](https://www.isa-afp.org/) entry on [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html). The theory stack behind this entry is enormous as it uses many theorems from [Analysis](http://isabelle.in.tum.de/dist/library/HOL/HOL-Analysis/index.html). As a consequence, the verification of this stack takes about 40 minutes which is the reason why we recommend pre-loading them, i.e. building a heap for those files. In order to do that in a Unix system just:
1. Open Terminal.
2. Add the Isabelle bin directory to your path, e.g., $ export PATH=$PATH:/Apps/.../Isabelle2017/bin (replace the ... with the actual path to the Isabelle installation directory).
3. Then execute: $ isabelle build -b Ordinary_Differential_Equations
4. Wait for the build to finish, go for tea or coffee. 
5. To launch, just type $ isabelle jedit -l Ordinary_Differential_Equations

**NOTE:** The build command, is only necessary once. After that, you just need to do step 2 and launch (step 5).

The files implementing a relational semantics require a modified version of [Program Construction and Verification Components Based on Kleene Algebra](https://www.isa-afp.org/entries/Algebraic_VCs.html), which you can download directly from this online repository (the folder afpModified). Alternatively, if you are Isabelle savvy, you could use the original AFP entry and comment-out the conflicting instantiations of sets in [Kleene_Algebra_Models.thy] and [Dioid_Models.thy].
