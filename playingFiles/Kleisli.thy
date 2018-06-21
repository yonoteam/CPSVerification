(*section{* Proofs Related to the Kleisli Category of the Powerset Monad *}*)

theory Kleisli

imports Main
begin

notation relcomp (infixl ";" 70)  
(*notation Id_on ("\<lceil>_\<rceil>") (* Id-on embeds sets into subidentity relations *)*)

text \<open>Isabelle' type systems doesn't allow formalising arbitrary monoids like in Haskell, but one can
still work with the category Set.\<close>

text \<open>The powerset functor maps sets to powersets and functions between sets to functions between powersets. 
It is the direct image operation on functions.\<close>

definition Powf :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set \<Rightarrow> 'b set)" ("\<P>") where
  "\<P> f = (\<lambda>X. f ` X)"

lemma Powf_functor: "\<P> (f \<circ> g) = \<P> f \<circ> \<P> g"
  by (force simp: fun_eq_iff Powf_def)

text {* Hence Pow is indeed a covariant functor. Next I define the multiplication and unit of the powerset monad. *}

abbreviation mu :: "'a set set \<Rightarrow> 'a set" ("\<mu>") where
  "\<mu> \<equiv> (\<lambda>X. \<Union>X)"

abbreviation eta :: "'a \<Rightarrow> 'a set" ("\<eta>") where
  "\<eta> \<equiv> (\<lambda>x. {x})"

text {* Pow is clearly an endofunctor, so, to show that the triple is a monad, it remains to verify
 that mu and eta are natural transformations. *}

lemma eta_nt: "(\<P> f) \<circ> \<eta> = \<eta> \<circ> f"
  by (simp add: fun_eq_iff Powf_def)

lemma mu_nt: "\<mu> \<circ> (\<P> (\<P> f)) = (\<P> f) \<circ> \<mu>" 
  by (force simp: fun_eq_iff Powf_def)

text {* This completes Exercise 1(a) on p.142 in Mac Lane' book. 
I now turn to the Kleisli category of the Powerset monad and come back to this exercise later. *}

text {* Now consider a binary relation as a nondeterministic function (Kleisli maps) that maps elements to sets of elements.
 I define the Kleisli composition and Kleisli lifting (or Kleisli extension) for these functions. *}

definition Kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl "\<circ>\<^sub>K" 70) where
  "f \<circ>\<^sub>K g = \<mu> \<circ> (\<P> g) \<circ> f"               

definition Klift :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" ("_\<^sup>\<dagger>" [101] 100) where
  "f\<^sup>\<dagger> = \<mu> \<circ> (\<P> f)"

lemma Kcomp_set: "f \<circ>\<^sub>K g = (\<lambda>x. \<Union>{g y |y. y \<in> f x})"
  by (force simp: fun_eq_iff Kcomp_def Powf_def)

lemma Kcomp_set_var: "f \<circ>\<^sub>K g = (\<lambda>x. \<Union> (g ` f x))"
  by (metis Kcomp_def Powf_def comp_apply)

lemma Klift_set:  "f\<^sup>\<dagger>  = (\<lambda>X. \<Union>{f x |x. x \<in> X})"
  by (force simp: fun_eq_iff Klift_def Powf_def)   

lemma Klift_set_var:  "f\<^sup>\<dagger> = (\<lambda>X. \<Union> (f ` X))"
  by (auto simp: fun_eq_iff Klift_def Powf_def)

text \<open>The next lemma relates Kleisli composition, function composition and Kleisli lifting.\<close>

lemma Kcomp_Klift: "f \<circ>\<^sub>K g = g\<^sup>\<dagger> \<circ> f"
  by (force simp: fun_eq_iff Kcomp_set Klift_set)

text \<open>Next I prove the three fundamental properties of Kleisli lifting, which give one way of defining
the powerset monad.\<close>

lemma Klift_prop1: "(f\<^sup>\<dagger> \<circ> g)\<^sup>\<dagger> = f\<^sup>\<dagger> \<circ> g\<^sup>\<dagger>" 
  by (auto simp: fun_eq_iff Klift_set)

lemma Klift_prop2 [simp]: "f\<^sup>\<dagger> \<circ> \<eta> = f"
  by (simp add: fun_eq_iff Klift_set)

lemma Klift_prop3 [simp]: "\<eta>\<^sup>\<dagger> = id"
  by (force simp: fun_eq_iff Klift_set)

lemma Klift_mu: "id\<^sup>\<dagger> = \<mu>"
  by (simp add: fun_eq_iff Klift_def Powf_def)

text \<open>Using these properties it is easy to verify the more common defining properties of the Kleisli category 
over the powerset monad.\<close>

lemma Kcomp_assoc: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
  by (force simp: Kcomp_Klift Klift_prop1)

lemma Kcomp_unl [simp]: "\<eta> \<circ>\<^sub>K f = f"
  by (simp add: Kcomp_set)

lemma Kcomp_unr [simp]: "f \<circ>\<^sub>K \<eta> = f"
  by (simp add: Kcomp_Klift)

text \<open>Next I show that eta is a (contravariant)  functor from Set to the Kleisli category over the powerset monad.\<close>

lemma eta_hom1: "\<eta> \<circ> (f \<circ> g) = (\<eta> \<circ> g) \<circ>\<^sub>K (\<eta> \<circ> f)"
  by (simp add: fun_eq_iff Kcomp_def Powf_def)

text \<open>For the unit there is nothing to show as it *is* eta id \<close>

text \<open>Next I show that the Eilenberg-Moore algebras of the powerset monad are complete join semilattices.\<close>

definition smap :: "'a set \<Rightarrow> ('a::complete_lattice)" ("\<sigma>") where
  "\<sigma> = Sup"

text {* First I prove the associativity and unit law. *}

lemma me_assoc: "\<sigma> \<circ> \<P> \<sigma> = \<sigma> \<circ> \<mu>"
  apply (clarsimp simp add: fun_eq_iff smap_def Powf_def)
  apply (rule antisym)
   apply (simp add: SUP_least Sup_subset_mono Sup_upper)
  apply (intro Sup_least)
  by (meson SUP_upper2 Sup_upper Union_iff)

lemma  me_id [simp]: "\<sigma> \<circ> \<eta> = id"
  by (simp add: fun_eq_iff smap_def)

text \<open>The morphisms between Pow-algebras are join-preserving maps.\<close>

text \<open>In particular, Powersets with structure map mu form an Eilenberg-Moore algebra.\<close>

lemma me_mu_assoc: "\<mu> \<circ> \<P> \<mu> = \<mu> \<circ> \<mu>"
  by (force simp: fun_eq_iff Powf_def)

lemma me_mu_id [simp]: "\<mu> \<circ> \<eta> = id"
  by (simp add: fun_eq_iff)

text \<open>Next I verify the functor from the Kleisli category to the Eilenberg-Moore category. This functor maps
sets to mu and functions to their Kleisli liftings. But this is just functoriality of lambda!. Jacobs calls this functor 
state transformer.\<close>

text \<open>The next lemma and  Lemma Klift-prop2 show that the Kleisli lifting and eta
form a bijective pair between nondeterministic functions and objects of the Kleisli category.\<close>

lemma eta_lambda_prop: 
assumes "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi>"
shows "(\<phi> \<circ> \<eta>)\<^sup>\<dagger>  = \<phi>"
proof -
  have "(\<phi> \<circ> \<eta>)\<^sup>\<dagger> = \<mu> \<circ> \<P> (\<phi> \<circ> \<eta>)"
    by (simp add: Klift_def)
  also have "... = \<mu> \<circ> \<P> \<phi> \<circ> \<P> \<eta>"
    by (simp add: comp_assoc Powf_functor)
  also have "... = \<phi> \<circ> \<mu> \<circ> \<P> \<eta>"
    by (simp add: assms)
  also have "... = \<phi> \<circ> \<eta>\<^sup>\<dagger>"
    by (simp only: Klift_def comp_assoc)
  finally show ?thesis
    by simp
qed

lemma univ_disj_aux: "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi> \<longleftrightarrow> \<phi> \<circ> \<mu> = \<phi>\<^sup>\<dagger>"
  by (simp add: Klift_def)

text \<open>The assumption expresses the fact that phi is Sup-preserving.\<close>

lemma Klift_inj: "f\<^sup>\<dagger> = g\<^sup>\<dagger> \<Longrightarrow> f = g"
  by (metis Klift_prop2)

lemma eta_inj: 
assumes  "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi>" 
and  "\<psi> \<circ> \<mu> = \<mu> \<circ> \<P> \<psi>"
shows "\<phi> \<circ> \<eta> = \<psi> \<circ> \<eta> \<Longrightarrow> \<phi> = \<psi>"
  by (metis assms eta_lambda_prop)

text \<open>In fact we obtain an isomorphism.\<close>

lemma Klift_hom: "(g \<circ>\<^sub>K f)\<^sup>\<dagger> = f\<^sup>\<dagger> \<circ> g\<^sup>\<dagger>" 
  by (auto simp: fun_eq_iff Klift_set Kcomp_set)

lemma eta_hhom1: 
  assumes  "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi>" 
  shows "\<phi> \<circ> \<psi> \<circ> \<eta> = (\<psi> \<circ> \<eta>) \<circ>\<^sub>K (\<phi> \<circ> \<eta>)"
  by (simp add: Kcomp_Klift assms eta_lambda_prop fun.map_comp)

lemma eta_hom2: "id \<circ> \<eta> = \<eta>"
  by simp

text \<open>Preservation of units by the Kleisli lifting has been proved in Klift-prop3.\<close>

(**********************************************************)

text \<open>Next I establish the isomorphism between binary relations and nondeterministic functions.\<close>

definition r2f :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<F>") where
  "\<F> R = (\<lambda>x. {y. (x,y) \<in> R})"

definition f2r :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

text \<open>The functions form bijective pairs.\<close>

lemma r2f2r [simp]: "\<R> \<circ> \<F> = id"
  by (auto simp: f2r_def r2f_def)

lemma f2r2f [simp]: "\<F> \<circ> \<R> = id"
  by (auto simp: f2r_def r2f_def)

lemma r2f_inj: "\<F> R = \<F> S \<Longrightarrow> R = S"
  by (metis comp_eq_id_dest fun.map_id0 id_apply r2f2r)

lemma f2r_inj: "\<R> f = \<R> g \<Longrightarrow> f = g"
  by (metis f2r2f pointfree_idE)

lemma r2f_surj: "\<forall>f. \<exists>R. \<F> R = f"
  by (meson f2r2f pointfree_idE)

lemma f2r_surj: "\<forall>R. \<exists>f. \<R> f = R"
  by (metis comp_apply id_apply r2f2r)

text \<open>The bijections preserve compositions and units\<close>

lemma r2f_hom1: "\<F> (R ; S) = \<F> R \<circ>\<^sub>K \<F> S" 
  by (auto simp: fun_eq_iff r2f_def Kcomp_set)

lemma f2r_hom1: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  by (auto simp: f2r_def Kcomp_set)

lemma f2r_hom2 [simp]: "\<F> Id = \<eta>"
  by (simp add: fun_eq_iff r2f_def)

lemma r2f_hom2 [simp]: "\<R> \<eta> = Id"
  by (auto simp: fun_eq_iff f2r_def)

text \<open>Next I include a dioid structure. That is, I enrich the homset of the Kleisli category. 
I guess that this is related with the Eilenberg-Moore construction above.
This might have to be linked in the future. At the moment this is a hack.\<close>

definition  plus_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "\<oplus>" 60) where 
  "f \<oplus> g = (\<lambda>x. f x \<union> g x)"

definition zero_fun :: "'a \<Rightarrow> 'b set" ("\<zeta>") where
  "\<zeta> = (\<lambda>x::'a. {})"

text \<open>The bijections preserve the dioid structure.\<close>

lemma r2f_un_hom: "\<F> (R \<union> S) = (\<F> S) \<oplus> (\<F> R)" 
  by (force simp: r2f_def plus_fun_def)

lemma f2r_plus_hom: "\<R> (f \<oplus> g) = (\<R> g) \<union> (\<R> f)"
  by (force simp: f2r_def plus_fun_def)

lemma r2f_zero_hom: "\<F> {} = \<zeta>"
  by (simp add: r2f_def zero_fun_def)

lemma f2r_zero_hom: "\<R> \<zeta> = {}"
  by (simp add: f2r_def zero_fun_def)

text \<open>The two operations satisfy the dioid laws.\<close>

lemma plus_fun_assoc: "(f \<oplus> g) \<oplus> h = f \<oplus> (g \<oplus> h)"
  by (simp add: f2r_inj f2r_plus_hom sup_assoc)

lemma plus_fun_comm: "f \<oplus> g = g \<oplus> f"
  by (simp add: f2r_inj f2r_plus_hom sup_commute)

lemma plus_fun_idem [simp]: "f \<oplus> f = f"
  by (simp add: f2r_inj f2r_plus_hom)

lemma fun_distl: "f \<circ>\<^sub>K (g \<oplus> h) = (f \<circ>\<^sub>K g) \<oplus> (f \<circ>\<^sub>K h)"
  by (simp add: f2r_hom1 f2r_inj f2r_plus_hom)

lemma fun_distr: "(f \<oplus> g) \<circ>\<^sub>K h = (f \<circ>\<^sub>K h) \<oplus> (g \<circ>\<^sub>K h)"
  by (simp add: f2r_hom1 f2r_inj f2r_plus_hom)

lemma plus_fun_zerol [simp]: "\<zeta> \<oplus> f = f"
  by (simp add: f2r_inj f2r_plus_hom f2r_zero_hom)

lemma times_fun_annil [simp]: "\<zeta> \<circ>\<^sub>K f = \<zeta>"
  by (simp add: f2r_hom1 f2r_inj f2r_zero_hom)

lemma times_fun_annir [simp]: "f \<circ>\<^sub>K \<zeta> = \<zeta>"
  by (simp add: f2r_hom1 f2r_inj f2r_zero_hom)

text \<open>The next laws bring us to quantales --- or quantaloids.\<close>

definition "Plus F = (\<lambda>x. \<Union>{f x |f. f \<in> F})"

lemma r2f_Un_hom: "\<F> (\<Union>R) = Plus {\<F> r |r. r \<in> R}" 
  by (auto simp: r2f_def Plus_def)

lemma f2r_Plus_hom: "\<R> (Plus F) = \<Union>{\<R> f |f. f \<in> F}"
  by (auto simp: f2r_def Plus_def) 

lemma fun_distl_Plus: "f \<circ>\<^sub>K (Plus G) = Plus {f \<circ>\<^sub>K g |g. g \<in> G}"
proof-
  have h: "\<forall> r S. r ; \<Union>S = \<Union>{r ; s |s. s \<in> S}"
    apply (clarify, rule antisym) by blast+
  have "f \<circ>\<^sub>K (Plus G) = \<F> ((\<R> f) ; \<Union>{\<R> g |g. g \<in> G})"
    by (metis f2r_Plus_hom f2r_inj pointfree_idE r2f2r r2f_hom1)
  also have "... = \<F> (\<Union>{\<R> f ; \<R> g |g. g \<in> G})"
    by (smt CollectD CollectI Collect_cong h)
  also have "... = Plus {(\<F> (\<R> f)) \<circ>\<^sub>K (\<F> (\<R> g)) |g. g \<in> G}"
    by (smt Collect_cong mem_Collect_eq r2f_Un_hom r2f_hom1)
  finally show ?thesis
    by (smt Collect_cong f2r_inj pointfree_idE r2f2r)
qed

lemma fun_distr_Plus: "(Plus F) \<circ>\<^sub>K g = Plus {f \<circ>\<^sub>K g |f. f \<in> F}"
proof-
  have h: "\<forall> s R. \<Union>R ; s = \<Union>{r ; s |r. r \<in> R}"
    apply (clarify, rule antisym) by blast+
  have "(Plus F) \<circ>\<^sub>K g = \<F> (\<Union>{\<R> f |f. f \<in> F} ; \<R> g)"
    by (metis f2r_Plus_hom f2r_inj pointfree_idE r2f2r r2f_hom1)
  also have "... = \<F> (\<Union>{\<R> f ; \<R> g |f. f \<in> F})"
    by (smt CollectD CollectI Collect_cong h)
  also have "... = Plus {(\<F> (\<R> f)) \<circ>\<^sub>K (\<F> (\<R> g)) |f. f \<in> F}"
    by (smt Collect_cong mem_Collect_eq r2f_Un_hom r2f_hom1)
  finally show ?thesis
    by (smt Collect_cong f2r_inj pointfree_idE r2f2r)
qed       

text \<open>Next we set up the semilattice order\<close>

lemma le_le_fun: "f \<le> g \<longleftrightarrow> f \<oplus> g = g"
  by (force simp add: fun_eq_iff le_fun_def plus_fun_def)

lemma f2r_leq: "f \<le> g \<longleftrightarrow> \<R> f \<subseteq> \<R> g"
  by (force simp add: f2r_def le_fun_def)

lemma r2f_leq: "R \<subseteq> S \<longleftrightarrow> \<F> R \<le> \<F> S"
  by (simp add: f2r_leq pointfree_idE)

text \<open>Finally we define an antidomain operation and prove the axioms of antidomain semirings.\<close>

definition "ad_fun f = (\<lambda>x. if (f x = {}) then {x} else {})"

definition "ad_rel R = {(x,x) |x. \<not> (\<exists>y. (x,y) \<in> R)}"

lemma f2r_ad_fun_hom: "\<R> (ad_fun f) = ad_rel (\<R> f)"
  apply (simp add: ad_fun_def ad_rel_def f2r_def)
  apply safe
  apply (metis empty_iff singletonD)
  by simp
  
lemma r2f_ad_rel_hom: "\<F> (ad_rel R) = ad_fun (\<F> R)"
  by (simp add: ad_fun_def ad_rel_def r2f_def fun_eq_iff)

lemma ad_fun_as1 [simp]: "(ad_fun f) \<circ>\<^sub>K f = \<zeta>"
  by (simp add: ad_fun_def Kcomp_def fun_eq_iff Powf_def zero_fun_def)

lemma ad_fun_as2 [simp]: "ad_fun (f \<circ>\<^sub>K g) \<oplus> ad_fun (f \<circ>\<^sub>K ad_fun (ad_fun g)) = ad_fun (f \<circ>\<^sub>K ad_fun (ad_fun g))"
  by (auto simp: ad_fun_def Kcomp_def plus_fun_def fun_eq_iff Powf_def)

lemma ad_fun_as3 [simp]: "ad_fun (ad_fun f) \<oplus> ad_fun f = \<eta>"
  by (simp add: ad_fun_def plus_fun_def fun_eq_iff Powf_def)


text \<open>Next I define a backward transformer that corresponds to a backward modal diamond operator
or a strongest precondition operator.\<close>

definition BD :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"  ("\<langle> _|" [61] 82) where
  "BD = Klift \<circ> \<F>"

lemma BD_set: "BD R = (\<lambda>Y. R `` Y)"
  by (auto simp: BD_def Klift_set r2f_def)

lemma BD_hom1: "BD (R ; S) = BD S \<circ> BD R"
  by (simp add: BD_def Klift_hom r2f_hom1)  

lemma BD_hom2: "BD Id = \<eta>\<^sup>\<dagger>"
  by (simp add: BD_def)

text {* Finally, the inverse homomorphism is obtained as follows. *}

definition iBD :: "('a set \<Rightarrow> 'b set) \<Rightarrow> ('a \<times> 'b) set" where
  "iBD = (\<lambda>\<phi>. \<R> (\<phi> \<circ> \<eta>))"

lemma BDiBD [simp]: "iBD \<circ> BD = id"
  by (simp add: fun_eq_iff BD_def iBD_def Klift_def f2r_def r2f_def Powf_def)

lemma iBDBD: 
  assumes "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi>"
  shows "(BD \<circ> iBD) \<phi> = \<phi>"
  by (smt BD_def BDiBD assms comp_def eta_lambda_prop pointfree_idE r2f_surj)

lemma iBD_hom1: 
  assumes  "\<phi> \<circ> \<mu> = \<mu> \<circ> \<P> \<phi>"
  shows "iBD (\<phi> \<circ> \<psi>) = iBD \<psi> ; iBD \<phi>"
  by (simp add: assms eta_hhom1 f2r_hom1 iBD_def)

lemma IBD_hom2 [simp]: "iBD id  = Id"
  by (simp add: iBD_def)

lemma "\<F> (Id_on X) = (\<lambda>x. if x \<in> X then {x} else {})"
  by (simp add: fun_eq_iff r2f_def Id_on_def)

text {* This shows that relations are isomorphic to predicate transformers. *}

text {* tbd: Eilenberg-Moore algebras; functor from Kleisli to EM; backward predicate transformers; adjunction. *}

lemma "\<F> (Id_on X) \<circ>\<^sub>K f = (\<lambda>x. if x \<in> X then f x else {})"
  by (simp add: fun_eq_iff Kcomp_set r2f_def Id_on_def)

lemma "f \<circ>\<^sub>K \<F> (Id_on X) = (\<lambda>x. X \<inter> f x)"  
  by (auto simp: Kcomp_set r2f_def Id_on_def)

end

