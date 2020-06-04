# Hybrid Systems Verification
A repository with Isabelle theories for verification of hybrid programs, a model for Cyber-Physical Systems. Most of this development is now part of the [AFP](https://www.isa-afp.org/). See [Hybrid Systems VCs](https://www.isa-afp.org/entries/Hybrid_Systems_VCs.html).

As of mid-2020, the modularity of the approach provides various formalisations of similar results. The differences reside on the codification of systems of ordinary differential equations (ODEs), on the algebraic semantics chosen for verification, and on the model of this semantics:

Location                   | Algebraic Semantics       | Algebra Model                   | ODEs implementation | Notes
---------------------------|---------------------------|---------------------------------|---------------------|---------------------------
HybridVerifLists           | Modal Kleene Algebra      | Relational Semantics            | Lists               | Oldest (not recommended)
HybridVerifVecs/MKA        | Modal Kleene Algebra      | Relational Semantics            | Vectors             | Modular
HybridVerifVecs/MKA        | Modal Kleene Algebra      | State Transformer Semantics     | Vectors             | Modular
HybridVerifVecs/KAT        | Kleene Algebra with Tests | Relational Semantics            | Vectors             | Hoare logic and refinement
HybridVerifVecs/KAT        | Kleene Algebra with Tests | State Transformer Semantics     | Vectors             | Hoare logic and refinement
HybridVerifVecs/PredTransf | Modal Kleene Algebra      | Predicate Transformer Semantics | Vectors             | Not optimised
HybridVerifVecs            | None                      | Predicate Transformer Semantics | Vectors             | Lightest. Examples include linear systems.

Every version runs with [Isabelle2020 (April 2020)](https://isabelle.in.tum.de/). Moreover, they all depend on the AFP entry on [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html). The theory stack is enormous and its verification takes more than 40 minutes. We recommend building a heap that pre-loads the stack. In order to do this in a Unix system, if all the dependencies (Isabelle+AFP) have already been installed, follow the steps below:
1. Open Terminal.
2. Add the Isabelle bin directory to your path, e.g. `$ export PATH=$PATH:/Apps/.../Isabelle2020/bin` (replace the `...` with the actual path to the Isabelle installation directory).
3. Then execute: `$ isabelle build -b Ordinary_Differential_Equations`
4. Wait for the build to finish, go for tea or coffee. 
5. To launch, just type `$ isabelle jedit -l Ordinary_Differential_Equations`

**NOTE:** The build command, is only necessary once. After that, you just need to do step 2 and launch (step 5).
