theory cat2rel
  imports
  "../hs_prelims"
  "../../afpModified/VC_KAD"

begin

section{* Hybrid System Verification with relations *}

\<comment> \<open>We start by deleting some conflicting notation.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Relation.Domain ("r2s")

subsection{* Verification of regular programs *}

text{* Below we explore the behavior of the forward box operator from the antidomain kleene algebra
with the lifting ($\lceil-\rceil$*) operator from predicates to relations @{thm p2r_def[no_vars]} 
and its dropping counterpart @{thm r2p_def[no_vars]}. *}

lemma p2r_IdD:"\<lceil>P\<rceil> = Id \<Longrightarrow> P s"
  by (metis (full_types) UNIV_I impl_prop p2r_subid top_empty_eq)

lemma wp_rel:"wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
  have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
    by (simp add: wp_trafo pointfree_idE)
  thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
    by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

corollary wp_relD:"(x,x) \<in> wp R \<lceil>P\<rceil> \<Longrightarrow> \<forall> y. (x,y) \<in> R \<longrightarrow> P y"
proof-
  assume "(x,x) \<in> wp R \<lceil>P\<rceil>"
  hence "(x,x) \<in> \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" using wp_rel by auto
  thus "\<forall> y. (x,y) \<in> R \<longrightarrow> P y" by (simp add: p2r_def)
qed

lemma p2r_r2p_wp_sym:"wp R P = \<lceil>\<lfloor>wp R P\<rfloor>\<rceil>"
  using d_p2r wp_simp by blast

lemma p2r_r2p_wp:"\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  by(rule sym, subst p2r_r2p_wp_sym, simp)

text{* Next, we introduce assignments and compute their @{text "wp"}. *}

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) where 
"x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2[_ ::== _])" [70, 65] 61) where 
"[x ::== expr]\<equiv> {(s, s[x :== expr s])| s. True}"

lemma wp_assign [simp]: "wp ([x ::== expr]) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s[x :== expr s])\<rceil>"
  by(auto simp: rel_antidomain_kleene_algebra.fbox_def rel_ad_def p2r_def)

lemma wp_assign_var [simp]: "\<lfloor>wp ([x ::== expr]) \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. Q (s[x :== expr s]))"
  by(subst wp_assign, simp add: pointfree_idE)

text{* The @{text "wp"} of the composition was already obtained in KAD.Antidomain\_Semiring:
@{thm fbox_mult[no_vars]}. *}

text{* There is also already an implementation of the conditional operator @{thm cond_def[no_vars]} 
and its @{text "wp"}: @{thm fbox_cond[no_vars]}. *}

text{* Finally, we add a wp-rule for a simple finite iteration. *}

lemma (in antidomain_kleene_algebra) fbox_starI: 
assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
shows "d p \<le> |x\<^sup>\<star>] q"
proof-
from \<open>d i \<le> |x] i\<close> have "d i \<le> |x] (d i)"
  using local.fbox_simp by auto 
hence "|1] p \<le> |x\<^sup>\<star>] i" using \<open>d p \<le> d i\<close> by (metis (no_types) 
  local.dual_order.trans local.fbox_one local.fbox_simp local.fbox_star_induct_var)
thus ?thesis using \<open>d i \<le> d q\<close> by (metis (full_types)
  local.fbox_mult local.fbox_one local.fbox_seq_var local.fbox_simp)
qed

lemma rel_ad_mka_starI:
assumes "P \<subseteq> I" and "I \<subseteq> wp R I" and "I \<subseteq> Q"
shows "P \<subseteq> wp (R\<^sup>*) Q"
proof-
  have "wp R I \<subseteq> Id"
    by (simp add: rel_antidomain_kleene_algebra.a_subid rel_antidomain_kleene_algebra.fbox_def)
  hence "P \<subseteq> Id" using assms(1,2) by blast
  from this have "rdom P = P" by (metis d_p2r p2r_surj)
  also have "rdom P \<subseteq> wp (R\<^sup>*) Q"
    by (metis \<open>wp R I \<subseteq> Id\<close> assms d_p2r p2r_surj 
        rel_antidomain_kleene_algebra.dka.dom_iso rel_antidomain_kleene_algebra.fbox_starI)
  ultimately show ?thesis by blast
qed

subsection{* Verification by providing solutions *}

abbreviation "orbital f T S t0 x0 \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T \<and> (\<forall> r \<in> {t0--t}. G (x r))}"

abbreviation 
g_evolution :: "(real \<Rightarrow> ('a::banach) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" 
("(1{[x\<acute>=_]_ _ @ _ & _})") where "{[x\<acute>=f]T S @ t0 & G} \<equiv> {(s,s'). s' \<in> g_orbital f T S t0 s G}"

context picard_ivp
begin

lemma orbital_collapses: 
  assumes "((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "orbital f T S t0 s = {\<phi> t s| t. t \<in> T}"
  apply safe apply(rule_tac x="t" in exI, simp)
  using assms unique_solution apply blast
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI) 
  using assms init_time by auto

lemma g_orbital_collapses: 
  assumes "((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "g_orbital f T S t0 s G = {\<phi> t s| t. t \<in> T \<and> (\<forall> r \<in> {t0--t}. G (\<phi> r s))}"
  apply safe apply(rule_tac x="t" in exI, simp) 
  using assms unique_solution apply(metis closed_segment_subset_domainI)
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI) 
  using assms init_time by auto

lemma wp_orbit:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "wp {(s,s'). s' \<in> orbital f T S t0 s} \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_rel, simp, safe)
   apply(erule_tac x="\<phi> t s" in allE, erule impE)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t s" in exI)
  using assms init_time apply(simp, simp)
  apply(subgoal_tac "\<phi> t (x t0) = x t")
   apply(erule_tac x="t" in ballE, simp, simp)
  by(rule_tac y="x" and s="x t0" in unique_solution, simp_all add: assms)

lemma wp_g_orbit:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {t0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_rel, simp, safe)
   apply(erule_tac x="\<phi> t s" in allE, erule impE)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t s" in exI)
  apply(simp add: assms init_time, simp)
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
    and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {t0..t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst picard_ivp.wp_g_orbit)
  by(auto simp: Starlike.closed_segment_eq_real_ivl)

corollary line_DS: "0 \<le> t \<Longrightarrow> wp {[x\<acute>=\<lambda>t s. c]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> =  
\<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst picard_ivp.wp_g_orbit[of "\<lambda> t s. c" _ _ "1/(t + 1)" _ "(\<lambda> t x. x + t *\<^sub>R c)"])
  using constant_is_picard_ivp apply blast
  using line_solves_constant by auto
  

subsection{* Verification with differential invariants *}

text{* We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.*}

subsubsection{* Differential Weakening *}

theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding rel_antidomain_kleene_algebra.fbox_def rel_ad_def
  apply(simp add: relcomp.simps p2r_def)
  apply(rule subset_antisym)
  by fastforce+

theorem dWeakening: 
  assumes "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by auto

subsubsection{* Differential Cut *}

lemma wp_g_orbit_IdD:
  assumes "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = Id" and "\<forall> r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
  shows "\<forall>r\<in>{t0--t}. C (x r)"
proof-
  {fix r :: real
    have "\<And>R P s. wp R \<lceil>P\<rceil> \<noteq> Id \<or> (\<forall>y. (s::'a, y) \<in> R \<longrightarrow> P y)"
      by (metis (lifting) p2r_IdD wp_rel)
    then have "r \<notin> {t0--t} \<or> C (x r)" using assms by meson}
  then show ?thesis by blast
qed

theorem DC:
  assumes "t0 \<in> T" and "interval T"
    and "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = Id"
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s} \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule subset_antisym)
  {fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}" 
  then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode f) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t" by blast
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using assms(1,2) \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
  ultimately have "\<forall>r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> by blast 
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_IdD assms(3) by blast
  hence "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}"
    using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> x_solves \<open>\<forall>r\<in>{t0--t}. r \<in> T\<close> by fastforce}
  from this show "{[x\<acute>=f]T S @ t0 & G} \<subseteq> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}" by blast
next show "{[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s} \<subseteq> {[x\<acute>=f]T S @ t0 & G}" by blast
qed

theorem dCut:
  assumes wp_C:"\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: p2r_def, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "P (x t0)" and "t0 \<le> \<tau>" and "\<tau> \<le> t" and "x t0 \<in> S"
    and x_solves:"(x solves_ode f){t0..t} S " and guard_x:"(\<forall> r \<in> {t0--\<tau>}. G (x r))"
  hence "{t0--\<tau>} \<subseteq> {t0--t}" using closed_segment_eq_real_ivl by auto
  from this and guard_x have "\<forall>r\<in>{t0--\<tau>}.\<forall>\<tau>\<in>{t0--r}. G (x \<tau>)"
    using closed_segment_closed_segment_subset by blast
  then have "\<forall>r\<in>{t0--\<tau>}. x r \<in> g_orbital f {t0..t} S t0 (x t0) G"
    using x_solves \<open>x t0 \<in> S\<close> \<open>t0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce
  from this have "\<forall>r\<in>{t0--\<tau>}. C (x r)" using wp_C \<open>P (x t0)\<close> 
    by(subst (asm) wp_rel, auto)
  hence "x \<tau> \<in> g_orbital f {t0..t} S t0 (x t0) (\<lambda> s. G s \<and> C s)"
    using guard_x \<open>t0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> x_solves \<open>x t0 \<in> S\<close> by fastforce
  from this \<open>P (x t0)\<close> and wp_Q show "Q (x \<tau>)"
    by(subst (asm) wp_rel, auto)
qed

subsubsection{* Differential Invariant *}

lemma DI_sufficiency:
  assumes "\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "t0 \<in> T"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> \<le> wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>"
  apply(subst wp_rel, subst wp_rel, simp add: p2r_def, clarsimp)
  apply(erule_tac x="s" in allE, erule impE, rule_tac x="t0" in exI, simp_all)
  using assms by metis

definition ode_invariant :: "'a pred \<Rightarrow> (real \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
'a set \<Rightarrow> bool" ("(_)/ is'_ode'_invariant'_of (_) (_) (_)" [70,65]61) 
  where "I is_ode_invariant_of f T S \<equiv> bdd_below T \<and> (\<forall> x. (x solves_ode f)T S \<longrightarrow>
I (x (Inf T)) \<longrightarrow> (\<forall> t \<in> T. I (x t)))"

lemma dInvariant:
  assumes "I is_ode_invariant_of f {t0..t} S"
  shows "\<lceil>I\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I\<rceil>"
  using assms unfolding ode_invariant_def apply(subst wp_rel)
  apply(simp add: p2r_def, clarify)
  apply(rule exI, rule conjI, simp)
  apply(clarify, erule_tac x="x" in allE)
  by(erule impE, simp_all)

lemma dInvariant':
  assumes "I is_ode_invariant_of f {t0..t} S" 
    and "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac C="I" in dCut)
   apply(drule_tac G="G" in dInvariant)
  using assms(2,3) dual_order.trans apply blast 
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