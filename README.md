# Hybrid Systems Verification
A repository for Isabelle modules to implement verification of hybrid programs, a model for Cyber-Physical Systems.

As of late 2019, the modularity of the approach provides various formalizations of similar results. The differences reside on the codification of systems of Ordinary Differential Equations, on the algebra chosen for verification, and on the implementation of the semantics. The implementations are:
* Spartan version with predicate transformers and a vector representation of the hybrid store. (our most powerful and lightweight version in HybridVerifVecs).
* Semantics of predicate transformers and Kleisli arrows (in HybridVerifVecs/PredTransf)
* Modal Kleene Algebra approach with both, relational and state transformer semantics (in HybridVerifVecs/MKA)
* Hoare logic and refinement calculus in Kleene Algebra with Tests semantics with both, relational and state transformer semantics (in HybridVerifVecs/KAT)
* Relational semantics in MKA with a list representation of systems of ODEs (in folder HybridVerifLists).

Every file runs smoothly with [Isabelle2019 (August 2019)](https://isabelle.in.tum.de/). Moreover, they all depend on the [AFP](https://www.isa-afp.org/) entry on [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html). The theory stack is enormous, hence its verification takes more than 40 minutes. This is the reason why we recommend building a heap that pre-loads the stack. In order to do this in a Unix system, if all the dependencies have already been installed, follow the steps below:
1. Open Terminal.
2. Add the Isabelle bin directory to your path, e.g. $ export PATH=$PATH:/Apps/.../Isabelle2017/bin (replace the ... with the actual path to the Isabelle installation directory).
3. Then execute: $ isabelle build -b Ordinary_Differential_Equations
4. Wait for the build to finish, go for tea or coffee. 
5. To launch, just type $ isabelle jedit -l Ordinary_Differential_Equations

**NOTE:** The build command, is only necessary once. After that, you just need to do step 2 and launch (step 5).

The files using lists as systems of ODEs require a modified version of [Program Construction and Verification Components Based on Kleene Algebra](https://www.isa-afp.org/entries/Algebraic_VCs.html), which you can download directly from this online repository (the folder afpModified). Alternatively, if you are Isabelle savvy, you could use the original AFP entry and comment-out the conflicting instantiations of sets in [Kleene_Algebra_Models.thy] and [Dioid_Models.thy].
