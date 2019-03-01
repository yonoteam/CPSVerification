theory cat2funcset
  imports "../hs_prelims" "Transformer_Semantics.Kleisli_Quantale" "KAD.Modal_Kleene_Algebra"
                        
begin
section{* Hybrid System Verification *}

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
no_notation Range_Semiring.antirange_semiring_class.ars_r ("r")
type_synonym 'a pred = "'a \<Rightarrow> bool"

subsection{* Verification of regular programs *}

text{* First we add lemmas for computation of weakest liberal preconditions (wlps). *}

lemma ffb_eta[simp]:"fb\<^sub>\<F> \<eta> X = X"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

lemma ffb_wlp:"fb\<^sub>\<F> F X = {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> X}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

lemma ffb_eq_univD:"fb\<^sub>\<F> F P = UNIV \<Longrightarrow> (\<forall>y. y \<in> (F x) \<longrightarrow> y \<in> P)"
proof
  fix y assume "fb\<^sub>\<F> F P = UNIV"
  from this have "UNIV = {s. \<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P}" 
    by(subst ffb_wlp[THEN sym], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P)}" by auto
  then show "s2p (F x) y \<longrightarrow> y \<in> P" by auto
qed

text{* Next, we introduce assignments and their wlps. *}

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) 
  where "x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) \<Rightarrow> ('a^'b) set" ("(2[_ ::== _])" [70, 65] 61) 
  where "[x ::== expr]\<equiv> (\<lambda>s. {s[x :== expr s]})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> ([x ::== expr]) Q = {s. (s[x :== expr s]) \<in> Q}"
  by(subst ffb_wlp, simp)

text{* The wlp of a (kleisli) composition is just the composition of the wlps. *}

lemma ffb_kcomp:"fb\<^sub>\<F> (G \<circ>\<^sub>K F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by(auto simp: kcomp_def)

text{* We also have an implementation of the conditional operator and its wlp. *}

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where 
  "IF P THEN X ELSE Y FI \<equiv> (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
  using assms apply(subst ffb_wlp)
  apply(subst (asm) ffb_wlp)+
  unfolding ifthenelse_def by auto

lemma ffb_if_then_elseD:
  assumes "T x \<longrightarrow> x \<in> fb\<^sub>\<F> X Q"
    and "\<not> T x \<longrightarrow> x \<in> fb\<^sub>\<F> Y Q"
  shows "x \<in> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
  using assms apply(subst ffb_wlp)
  apply(subst (asm) ffb_wlp)+
  unfolding ifthenelse_def by auto

text{* The final part corresponds to the finite iteration. *}

lemma kstar_inv:"I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  by(auto simp: kcomp_prop) 

lemma ffb_star_induct_self:"I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (kstar F) I"
  apply(subst ffb_wlp, subst (asm) ffb_wlp)
  unfolding kstar_def apply clarsimp
  using kstar_inv by blast

lemma ffb_starI:
assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  from assms(2) have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using ffb_star_induct_self by blast
  then have "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  from this and assms(3) show ?thesis
    by(subst ffb_wlp, subst (asm) ffb_wlp, auto)
qed

subsection{* Verification by providing solutions *}

abbreviation "orbital f T S t0 x0 \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T \<and> (\<forall> r \<in> {t0--t}. G (x r))}"

abbreviation 
g_evolution ::"(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
("(1{[x\<acute>=_]_ _ @ _ & _})") where "{[x\<acute>=f]T S @ t0 & G} \<equiv> (\<lambda> s. g_orbital f T S t0 s G)"

context picard_ivp
begin

lemma orbital_collapses: 
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "orbital f T S t0 s = {\<phi> t s| t. t \<in> T}"
  apply safe apply(rule_tac x="t" in exI, simp)
   apply(rule_tac x="xa" and s="xa t0" in unique_solution, simp_all add: assms)
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI)
  using assms init_time by auto

lemma g_orbital_collapses: 
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "{[x\<acute>=f]T S @ t0 & G} s = {\<phi> t s| t. t \<in> T \<and> (\<forall> r \<in> {t0--t}. G (\<phi> r s))}"
  apply safe apply(rule_tac x="t" in exI, simp) 
  using assms unique_solution apply(metis closed_segment_subset_domainI)
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI) 
  using assms init_time by auto

lemma ffb_orbit:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "fb\<^sub>\<F> (\<lambda>s. orbital f T S t0 s) Q = {s. \<forall> t \<in> T. s \<in> S \<longrightarrow> \<phi> t s \<in> Q}"
  apply(subst ffb_wlp, safe)
   apply(erule_tac x="\<phi> t x" in allE, erule impE, simp)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t x" in exI)
    apply(simp add: assms init_time, simp)
  apply(rename_tac s y t x)
  apply(subgoal_tac "\<phi> t (x t0) = x t")
   apply(erule_tac x="t" in ballE, simp, simp)
  by(rule_tac y="x" and s="x t0" in unique_solution, simp_all add: assms)

theorem ffb_g_orbit:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "fb\<^sub>\<F> {[x\<acute>=f]T S @ t0 & G} Q = {s. \<forall>t\<in>T. s\<in>S \<longrightarrow> (\<forall>r\<in>{t0--t}. G (\<phi> r s)) \<longrightarrow> (\<phi> t s) \<in> Q}"
  apply(subst ffb_wlp, safe)
   apply(erule_tac x="\<phi> t x" in allE, erule impE, simp)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t x" in exI)
    apply(simp add: assms init_time, simp)
  apply(rename_tac s y t x)
  apply(subgoal_tac "\<forall>r\<in>{t0--t}. \<phi> r (x t0) = x r")
   apply(erule_tac x="t" in ballE, safe)
    apply(erule_tac x="r" in ballE)+ apply simp_all
  apply(erule_tac x="t" in ballE)+ apply simp_all
  apply(rule_tac y="x" and s="x t0" in unique_solution, simp_all add: assms)
  using subsegment by blast 

end

text{* The previous theorem allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.*}

lemma dSolution:
  assumes "picard_ivp f T S L t0" and ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {t0..t}.G (\<phi> r s)) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) Q"
  using assms apply(subst picard_ivp.ffb_g_orbit)
  by (auto simp: Starlike.closed_segment_eq_real_ivl)

corollary ffb_line: "0 \<le> t \<Longrightarrow> fb\<^sub>\<F> {[x\<acute>=\<lambda>t s. c]{0..t} UNIV @ 0 & G} Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> (x + \<tau> *\<^sub>R c) \<in> Q}"
  apply(subst picard_ivp.ffb_g_orbit[of "\<lambda> t s. c" _ _ "1/(t + 1)" _ "(\<lambda> t x. x + t *\<^sub>R c)"])
  using constant_is_picard_ivp apply blast
  using line_solves_constant by auto

subsection{* Verification with differential invariants *}

text{* We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in our verification proofs.*}

subsubsection{* Differential Weakening *}
        
theorem DW:
  shows "fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) Q = fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) {s. G s \<longrightarrow> s \<in> Q}"
  by(subst ffb_wlp, subst ffb_wlp, auto)
  
theorem dWeakening: 
assumes "{s. G s} \<le> Q"
shows "P \<le> fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) Q"
  using assms apply(subst ffb_wlp)
  by(auto simp: le_fun_def)

subsubsection{* Differential Cut *}

lemma ffb_g_orbit_eq_univD:
  assumes "fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) {s. C s} = UNIV" 
    and "\<forall> r\<in>{t0--t}. x r \<in> g_orbital f T S t0 a G"
  shows "\<forall>r\<in>{t0--t}. C (x r)"
proof
  fix r assume "r \<in> {t0--t}"
  then have "x r \<in> g_orbital f T S t0 a G" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f T S t0 a G) \<longrightarrow> C y" 
    using assms(1) ffb_eq_univD by fastforce
  ultimately show "C (x r)" by blast
qed

theorem DC:
  assumes "t0 \<in> T" and "interval T"
    and "fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & G}) Q = fb\<^sub>\<F> ({[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym, simp_all)
  fix a show "g_orbital f T S t0 a G \<subseteq> g_orbital f T S t0 a (\<lambda>s. G s \<and> C s)"
  proof
    fix b assume "b \<in> g_orbital f T S t0 a G" 
    then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode f) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
      using assms(1) unfolding f2r_def by blast
    from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
      using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1))
    also have "\<forall>r\<in>{t0--t}. r \<in> T"
      using assms(1,2) \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
    ultimately have "\<forall> r\<in>{t0--t}. x r \<in> g_orbital f T S t0 a G"
      using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
    from this have "\<forall>r\<in>{t0--t}. C (x r)" using ffb_g_orbit_eq_univD assms(3) by blast
    thus "b \<in> g_orbital f T S t0 a (\<lambda> s. G s \<and> C s)" unfolding f2r_def
      using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> x_solves \<open>\<forall>r\<in>{t0--t}. r \<in> T\<close> by fastforce 
  qed
next show "\<And> a. g_orbital f T S t0 a (\<lambda> s. G s \<and> C s) \<subseteq> g_orbital f T S t0 a G" by auto
qed

theorem dCut:
  assumes "t0 \<le> t" and ffb_C:"P \<le> fb\<^sub>\<F> ({[x\<acute>=f]{t0..t} S @ t0 & G}) {s. C s}"
    and ffb_Q:"P \<le> fb\<^sub>\<F> ({[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)}) Q"
  shows "P \<le> fb\<^sub>\<F> ({[x\<acute>=f]{t0..t} S @ t0 & G}) Q"
proof(subst ffb_wlp, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "(x t0) \<in> P" and "t0 \<le> \<tau>" and "\<tau> \<le> t" and "x t0 \<in> S"
    and x_solves:"(x solves_ode f){t0..t} S " and guard_x:"(\<forall> r \<in> {t0--\<tau>}. G (x r))"
  hence "{t0--\<tau>} \<subseteq> {t0--t}" using closed_segment_eq_real_ivl by auto
  from this and guard_x have "\<forall>r\<in>{t0--\<tau>}.\<forall>\<tau>\<in>{t0--r}. G (x \<tau>)"
    using closed_segment_closed_segment_subset by blast
  then have "\<forall>r\<in>{t0--\<tau>}. x r \<in> {[x\<acute>=f]{t0..t} S @ t0 & G} (x t0)"
    using x_solves \<open>x t0 \<in> S\<close> \<open>t0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce 
  from this have "\<forall>r\<in>{t0--\<tau>}. C (x r)" using ffb_C \<open>(x t0) \<in> P\<close> by(subst (asm) ffb_wlp, auto)
  hence "x \<tau> \<in> {[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)} (x t0)"
    using guard_x \<open>t0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> x_solves \<open>x t0 \<in> S\<close> by fastforce
  from this \<open>(x t0) \<in> P\<close> and ffb_Q show "(x \<tau>) \<in> Q"
    by(subst (asm) ffb_wlp, auto simp: closed_segment_eq_real_ivl)
qed

subsubsection{* Differential Invariant *}

lemma DI_sufficiency:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "t0 \<in> T"
  shows "fb\<^sub>\<F> {[x\<acute>=f]T S @ t0 & G} Q \<le> fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) {s. s \<in> S \<longrightarrow> s \<in> Q}"
  using assms apply(subst ffb_wlp, subst ffb_wlp, clarsimp, rename_tac s)
  apply(erule_tac x="s" in allE, erule impE)
  by(rule_tac x="t0" in exI, rule_tac x="(\<lambda>t. \<phi> t s)" in exI, simp_all)

definition ode_invariant :: "'a pred \<Rightarrow> (real \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
'a set \<Rightarrow> bool" ("(_)/ is'_ode'_invariant'_of (_) (_) (_)" [70,65]61) 
  where "I is_ode_invariant_of f T S \<equiv> bdd_below T \<and> (\<forall> x. (x solves_ode f)T S \<longrightarrow>
I (x (Inf T)) \<longrightarrow> (\<forall> t \<in> T. I (x t)))"

lemma dInvariant:
  assumes "I is_ode_invariant_of f {t0..t} S"
  shows "{s. I s} \<le> fb\<^sub>\<F> ({[x\<acute>=f]{t0..t} S @ t0 & G}) {s. I s}"
  using assms unfolding ode_invariant_def apply(subst ffb_wlp)
  by(clarify, erule_tac x="xa" in allE, clarsimp)

lemma dInvariant':
assumes "I is_ode_invariant_of f {t0..t} S" and "t0 \<le> t"
    and "P \<le> {s. I s}" and "{s. I s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> ({[x\<acute>=f]{t0..t} S @ t0 & G}) Q"
  apply(rule_tac C="I" in dCut, simp add: \<open>t0 \<le> t\<close>)
  using dInvariant assms apply blast
  apply(rule dWeakening)
  using assms by auto

text{* Finally, we obtain some conditions to prove specific instances of differential invariants. *}

named_theorems ode_invariant_rules "compilation of rules for differential invariants."

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0--\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>) ) has_derivative (\<lambda>\<tau>.  \<tau> *\<^sub>R 0)) (at r within {t0--\<tau>}))"
shows "(\<lambda>s. \<theta> s = \<nu> s) is_ode_invariant_of f {t0..t} S"
proof(simp add: ode_invariant_def, clarsimp)
fix x \<tau> assume x_ivp:"(x solves_ode f){t0..t} S" "\<theta> (x t0) = \<nu> (x t0)" and tHyp:"t0 \<le> \<tau>" "\<tau> \<le> t"
  from this and assms have "\<forall> r \<in> {t0--\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>) ) has_derivative 
  (\<lambda>\<tau>.  \<tau> *\<^sub>R 0)) (at r within {t0--\<tau>})" by auto
  then have "\<exists>r\<in>{t0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x t0) - \<nu> (x t0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R 0) (\<tau> - t0)" by(rule_tac closed_segment_mvt, auto simp: tHyp) 
  thus "\<theta> (x \<tau>) = \<nu> (x \<tau>)" by (simp add: x_ivp(2))
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0--\<tau>}. \<theta>' (x r) \<ge> \<nu>' (x r)
\<and> ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {t0--\<tau>}))"
shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_ode_invariant_of f {t0..t} S"
proof(simp add: ode_invariant_def, clarsimp)
fix x \<tau> assume x_ivp:"(x solves_ode f){t0..t} S" "\<nu> (x t0) \<le> \<theta> (x t0)" and tHyp:"t0 \<le> \<tau>" "\<tau> \<le> t"
  from this and assms have primed:"\<forall> r \<in> {t0--\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative 
(\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {t0--\<tau>}) \<and> \<theta>' (x r) \<ge> \<nu>' (x r)" by auto
  then have "\<exists>r\<in>{t0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x t0) - \<nu> (x t0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - t0)" by(rule_tac closed_segment_mvt, auto simp: \<open>t0 \<le> \<tau>\<close>)
  from this obtain r where "r \<in> {t0--\<tau>}" and 
    "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - t0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x t0) - \<nu> (x t0))" by force 
  also have "... \<ge> 0" using tHyp(1) x_ivp(2) primed by (simp add: calculation(1))  
  ultimately show "\<nu> (x \<tau>) \<le> \<theta> (x \<tau>)" by simp
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0--\<tau>}. \<theta>' (x r) \<ge> \<nu>' (x r)
\<and> ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {t0--\<tau>}))"
shows "(\<lambda>s. \<nu> s < \<theta> s) is_ode_invariant_of f {t0..t} S"
proof(simp add: ode_invariant_def, clarsimp)
fix x \<tau> assume x_ivp:"(x solves_ode f){t0..t} S" "\<nu> (x t0) < \<theta> (x t0)" and tHyp:"t0 \<le> \<tau>" "\<tau> \<le> t"
  from this and assms have primed:"\<forall> r \<in> {t0--\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative 
(\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {t0--\<tau>}) \<and> \<theta>' (x r) \<ge> \<nu>' (x r)" by auto
  then have "\<exists>r\<in>{t0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x t0) - \<nu> (x t0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - t0)" by(rule_tac closed_segment_mvt, auto simp: \<open>t0 \<le> \<tau>\<close>)
  from this obtain r where "r \<in> {t0--\<tau>}" and 
    "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - t0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x t0) - \<nu> (x t0))" by force 
  also have "... > 0" 
    using tHyp(1) x_ivp(2) primed by (metis (no_types,hide_lams) Groups.add_ac(2) add_sign_intros(1) 
        calculation(1) diff_gt_0_iff_gt ge_iff_diff_ge_0 less_eq_real_def zero_le_scaleR_iff) 
  ultimately show "\<nu> (x \<tau>) < \<theta> (x \<tau>)" by simp
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "I1 is_ode_invariant_of f {t0..t} S" and "I2 is_ode_invariant_of f {t0..t} S"
shows "(\<lambda>s. I1 s \<and> I2 s) is_ode_invariant_of f {t0..t} S"
  using assms unfolding ode_invariant_def by auto

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "I1 is_ode_invariant_of f {t0..t} S" and "I2 is_ode_invariant_of f {t0..t} S"
shows "(\<lambda>s. I1 s \<or> I2 s) is_ode_invariant_of f {t0..t} S"
  using assms unfolding ode_invariant_def by auto

end