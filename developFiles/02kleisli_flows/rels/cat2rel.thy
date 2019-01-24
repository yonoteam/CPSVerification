theory cat2rel
  imports cat2rel_pre

begin

section{* Hybrid System Verification *}

subsection{* Verification by providing solutions *}

abbreviation "orbital f T S t0 x0 \<equiv> {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> (\<forall> r \<in> {t0--t}. G (x r)) \<and> x0 \<in> S}"

lemma (in picard_ivp) orbital_collapses:
  shows "orbital f T S t0 s = {phi t s| t. t \<in> T \<and> s \<in> S}"
  apply(rule subset_antisym)
  using fixed_point_usolves apply(clarsimp, rule_tac x="t" in exI, simp)
  apply(clarsimp, rule_tac x="t" in exI, rule_tac x="(\<lambda> t. phi t s)" in exI, simp)
  using fixed_point_solves by blast

lemma (in picard_ivp) g_orbital_collapses:
  shows "g_orbital f T S t0 s G = {phi t s| t. t \<in> T \<and> (\<forall> r \<in> {t0--t}. G (phi r s)) \<and> s \<in> S}"
  apply(rule subset_antisym)
  using fixed_point_usolves apply(clarsimp, rule_tac x="t" in exI, simp)
  apply (metis closed_segment_subset_domainI init_time)
  apply(clarsimp, rule_tac x="t" in exI, rule_tac x="(\<lambda> t. phi t s)" in exI)
  by(simp add: fixed_point_solves)

abbreviation (in local_flow) "orbit s \<equiv> {\<phi> t s |t. t \<in> T \<and> s \<in> S}"
abbreviation (in local_flow) "g_orbit s G \<equiv> {\<phi> t s |t. t \<in> T \<and> (\<forall> r \<in> {0--t}. G (\<phi> r s)) \<and> s \<in> S}"

lemma (in local_flow) orbital_is_orbit:
  shows "orbital (\<lambda> t. f) T S 0 s = orbit s"
  by (metis (no_types, lifting) fixed_point_solves flow_def) 

lemma (in local_flow) g_orbital_is_orbit:
  shows "g_orbital (\<lambda> t. f) T S 0 s G = g_orbit s G"
  using is_fixed_point unfolding g_orbital_collapses
  by (metis (mono_tags, lifting) closed_segment_subset_domainI picard_ivp.init_time picard_ivp_axioms) 

lemma (in local_flow) "\<R> (\<lambda> s. orbit s) = {(s, \<phi> t s)|s t. t \<in> T \<and> s \<in> S}"
  apply(safe, simp_all add: f2r_def)
  by(rule_tac x="t" in exI, simp)

theorem (in local_flow) wp_orbit:"wp (\<R> (\<lambda> s. orbit s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding f2r_def by (subst wp_rel, auto)

abbreviation 
g_orbit :: "(('a::banach) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1{[x\<acute>=_]_ _ @ _ & _})")
where "{[x\<acute>=f]T S @ t0 & G} \<equiv> \<R> (\<lambda> s. g_orbital (\<lambda> t. f) T S t0 s G)"

theorem wp_g_orbit:
  assumes "local_flow f S T L \<phi>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding f2r_def apply(subst wp_rel)
  using assms apply(subst local_flow.g_orbital_is_orbit, simp)
  by auto

text{* This last theorem allows us to compute weakest liberal preconditions for known systems of ODEs: *}
corollary line_DS:
  assumes "0 \<le> t"
  shows " wp {[x\<acute>=\<lambda>s. c]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda> s. c" _ _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow and assms by (blast, simp)

subsection{* Verification with differential invariants *}

text{* We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.*}

subsubsection{* Differential Weakening *}

theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding rel_antidomain_kleene_algebra.fbox_def rel_ad_def f2r_def
  apply(simp add: relcomp.simps p2r_def)
  apply(rule subset_antisym)
  by fastforce+

theorem dWeakening: 
assumes "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: f2r_def)

subsubsection{* Differential Cut *}

lemma wp_g_orbit_IdD:
  assumes "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = Id" and "\<forall> r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
  shows "\<forall>r\<in>{t0--t}. C (x r)"
proof-
  {fix r :: real
    have "\<And>R P s. wp R \<lceil>P\<rceil> \<noteq> Id \<or> (\<forall>y. (s::'a, y) \<in> R \<longrightarrow> P y)"
      by (metis (lifting) p2r_IdD wp_rel)
    then have "r \<notin> {t0--t} \<or> C (x r)" using assms by blast}
  then show ?thesis by blast
qed

theorem DC:
  assumes "t0 \<in> T" and "interval T"
    and "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = Id"
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s} \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, safe)
  fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}" 
  then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode (\<lambda>t. f)) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
    unfolding f2r_def by blast
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using assms(1,2) \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
  ultimately have "\<forall>r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_IdD assms(3) by blast
  thus "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}"
    using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> f2r_def x_solves by fastforce 
next
  fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}" 
  then show "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}"
    unfolding f2r_def by blast
qed

theorem dCut:
  assumes "t0 \<in> T" and "interval T"
    and wp_C:"\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: p2r_def, clarsimp)
  fix a y assume "P a" and "(a, y) \<in> {[x\<acute>=f]T S @ t0 & G}"
  then obtain x t where "t \<in> T" and x_solves:"(x solves_ode (\<lambda> t s. f s))T S " and "x t = y"
    and "x t0 = a" and guard_x:"(\<forall> r \<in> {t0--t}. G (x r))"  and "a \<in> S" by(auto simp: f2r_def)
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using assms(1,2) \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
  ultimately have "\<forall>r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using assms(3) \<open>P a\<close> by(subst (asm) wp_rel) auto
  hence "(a, y) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}"
    using guard_x \<open>a \<in> S\<close> \<open>x t = y\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> f2r_def x_solves by fastforce 
  from this \<open>P a\<close> and wp_Q show "Q y"
    by(subst (asm) wp_rel, simp add: f2r_def)
qed

corollary dCut_interval:
  assumes "t0 \<le> t" and "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>C\<rceil>" 
    and "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="C" in dCut)
  using assms by(simp_all add: interval_def)

subsubsection{* Differential Invariant *}

lemma DI_sufficiency:
  assumes picard:"picard_ivp (\<lambda> t. f) T S L t0"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> \<subseteq> wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>"
proof(subst wp_rel, subst wp_rel, simp add: p2r_def, clarsimp)
  fix s assume wlpQ:"\<forall>y. (s, y) \<in> {[x\<acute>=f]T S @ t0 & G} \<longrightarrow> Q y" and "s \<in> S" and "G s"
  from this and picard obtain x where "(x solves_ode (\<lambda> t. f))T S \<and> x t0 = s"
    using picard_ivp.fixed_point_solves by blast
  then also have "\<forall> r \<in> {t0--t0}. G (x r)" using \<open>G s\<close> by simp 
  ultimately have "(s,s) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using picard picard_ivp.init_time \<open>s \<in> S\<close> f2r_def by fastforce
  thus "Q s" using wlpQ by blast
qed

lemma dInvariant:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<lceil>G\<rceil> \<subseteq> \<lceil>F\<rceil>" and "bdd_below T"
    and FisPrimedI:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> I (x (Inf T)) \<longrightarrow>
    (\<forall> t \<in> T. (\<forall>r\<in>{(Inf T)--t}. F (x r)) \<longrightarrow> (I (x t)))"
  shows "\<lceil>I\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>I\<rceil>"
proof(subst wp_rel, simp add: p2r_def, clarsimp)
  fix s y assume "(s,y) \<in> {[x\<acute>=f]T S @ (Inf T) & G}" and sHyp:"I s"
  then obtain x and t where x_ivp:"(x solves_ode (\<lambda> t. f))T S \<and> x (Inf T) = s" 
    and xtHyp:"x t = y \<and> t \<in> T" and GHyp:"\<forall>r\<in>{(Inf T)--t}. G (x r)" 
    by(simp add: f2r_def, clarify, auto)
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower)
  from GHyp and \<open>\<lceil>G\<rceil> \<subseteq> \<lceil>F\<rceil>\<close> have geq0:"\<forall>r\<in>{(Inf T)--t}. F (x r)"
    by (auto simp: p2r_def)
  thus "I y" using xtHyp x_ivp sHyp and FisPrimedI by blast 
qed

lemma invariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s = 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t 
  assume x_ivp:"(x solves_ode (\<lambda>t. f)) T S" "\<theta> (x (Inf T)) = 0"  
    and tHyp:"t \<in> T" and eq0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) = 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R 0)) 
    (at r within {(Inf T)--t})" using eq0 by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  thus "\<theta> (x t) = 0" 
    using x_ivp(2) by (metis right_minus_eq scale_zero_right)
qed

corollary invariant_eq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode (\<lambda> t. f)){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply simp
  apply(rule invariant_eq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. \<theta> s = 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s = 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
  using impls apply blast
   apply(rule_tac \<nu>="\<nu>" in invariant_eq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t
  assume x_ivp:"\<theta> (x (Inf T)) \<ge> 0" "(x solves_ode (\<lambda>t. f)) T S" 
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<ge> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(2) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T)) " by force 
  thus "0 \<le> \<theta> (x t)" by (simp add: \<open>Inf T \<le> t\<close> ge0 x_ivp(1))
qed

corollary invariant_geq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode (\<lambda> t. f)){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_geq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<subseteq> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<ge> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
  using impls apply blast
  apply(rule_tac \<nu>="\<nu>" in invariant_geq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t
  assume x_ivp:"\<theta> (x (Inf T)) \<le> 0" "(x solves_ode (\<lambda>t. f)) T S" 
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<le> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(2) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T))" by force 
  thus "\<theta> (x t) \<le> 0" using \<open>(Inf T) \<le> t\<close> ge0 x_ivp(1)
    by (metis add_decreasing2 ge_iff_diff_ge_0 split_scaleR_neg_le)
qed

corollary invariant_leq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode (\<lambda> t. f)){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_leq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<subseteq> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<le> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
  using impls apply blast
  apply(rule_tac \<nu>="\<nu>" in invariant_leq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t
  assume x_ivp:"(x solves_ode (\<lambda>t. f)) T S" "\<theta> (x (Inf T)) > 0"
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<ge> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T)) " by force 
  thus "0 < \<theta> (x t)"  
    by (metis \<open>(Inf T) \<le> t\<close> ge0 x_ivp(2) Groups.add_ac(2) add_mono_thms_linordered_field(3) 
        ge_iff_diff_ge_0 monoid_add_class.add_0_right scaleR_nonneg_nonneg)
qed

corollary invariant_above_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode (\<lambda> t. f)){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_above_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. \<theta> s > 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<subseteq> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s > 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
  using impls apply blast
  apply(rule_tac \<nu>="\<nu>" in invariant_above_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t
  assume x_ivp:"(x solves_ode (\<lambda>t. f)) T S" "\<theta> (x (Inf T)) < 0"
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<le> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  thus "\<theta> (x t) < 0"  using \<open>(Inf T) \<le> t\<close> ge0 x_ivp(2)
    by (metis add_mono_thms_linordered_field(3) diff_gt_0_iff_gt ge_iff_diff_ge_0 linorder_not_le 
        monoid_add_class.add_0_left monoid_add_class.add_0_right split_scaleR_neg_le) 
qed

corollary invariant_below_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode (\<lambda> t. f)){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_below_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. \<theta> s < 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<subseteq> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  using \<open>t0 \<le> t\<close> apply(rule_tac C="\<lambda>s. \<theta> s < 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
  using impls apply blast
  apply(rule_tac \<nu>="\<nu>" in invariant_below_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_meet:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>"
  using assms apply(subst (asm) wp_rel, subst (asm) wp_rel)
  apply(subst wp_rel, simp add: p2r_def)
  by blast

theorem dInvariant_meet:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<subseteq> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<and> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>")
  using impls apply blast
    apply(rule invariant_meet)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_join:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>"
  using assms apply(subst (asm) wp_rel, subst (asm) wp_rel)
  apply(subst wp_rel, simp add: p2r_def)
  by blast

theorem dInvariant_join:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<subseteq> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<or> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>")
  using impls apply blast
    apply(rule invariant_join)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by auto

end