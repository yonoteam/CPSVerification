theory cat2funcset
  imports cat2funcset_pre
                        
begin

section{* Hybrid System Verification *}

subsection{* Verification by providing solutions *}

abbreviation "orbital f T S t0 x0 \<equiv> {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> (\<forall> r \<in> {t0--t}. G (x r)) \<and> x0 \<in> S}"
(************** doesn't guarantee that initial time is in interval... ******************************)

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

theorem (in local_flow) wp_orbit:"wp (orbit\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  by(subst wp_nd_fun, rule nd_fun_ext, auto)

abbreviation 
g_orbit ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1{[x\<acute>=_]_ _ @ _ & _})")
where "{[x\<acute>=f]T S @ t0 & G} \<equiv> (\<lambda> s. g_orbital (\<lambda> t. f) T S t0 s G)\<^sup>\<bullet>"
(************************************************************************************)
lemma "(x solves_ode (\<lambda>a. f)) T S \<and> x t0 = s \<and> G (x t0) \<and> s \<in> S \<Longrightarrow> x t0 \<in> ({[x\<acute>=f]T S @ t0 & G}\<^sub>\<bullet>) s"
  apply simp
  apply(rule_tac x="t0" in exI)
  apply(rule_tac x="x" in exI)
  apply auto
  unfolding solves_ode_def apply(auto simp: Pi_def)
  oops

theorem wp_g_orbit:
  assumes "local_flow f S T L \<phi>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_nd_fun, rule nd_fun_ext)
  using assms apply(subst local_flow.g_orbital_is_orbit, simp) by auto

text{* This last theorem allows us to compute weakest liberal preconditions for known systems of ODEs: *}

corollary line_DS:
  assumes "0 \<le> t"
  shows "wp {[x\<acute>=\<lambda>s. c]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda> s. c" _ _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow and assms by auto

subsection{* Verification with differential invariants *}

text{* We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.*}

subsubsection{* Differential Weakening *}

thm kcomp_def kcomp_prop le_fun_def
        
theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding fbox_def apply(rule nd_fun_ext) apply transfer apply simp
proof(subst kcomp_prop)+
  fix x::'a and T f S t0 G Q 
  let ?Y = "g_orbital (\<lambda>a. f) T S t0 x G"
  have *:"\<forall>y \<in> ?Y. G y" by blast
  {assume "(\<Union>y\<in>?Y . if \<not> Q y then \<eta> y else {}) = {}"
    then have "\<forall>y\<in>?Y . (if \<not> Q y then \<eta> y else {}) = {}" by blast
    hence "\<forall>y\<in>?Y . Q y" by (metis (mono_tags, lifting) bot_pres_del) 
    then have "\<forall>y\<in>?Y . (if G y \<and> \<not> Q y then \<eta> y else {}) = {}" by auto
    from this have "(\<Union>y\<in>?Y . if G y \<and> \<not> Q y then \<eta> y else {}) = {}" by blast}
  moreover
  {assume "(\<Union>y\<in>?Y .  if \<not> Q y then \<eta> y else {}) \<noteq> {}"
    then have "\<exists>y\<in>?Y. (if \<not> Q y then \<eta> y else {}) \<noteq> {}" by blast
    hence "\<exists>y\<in>?Y. \<not> Q y" by (metis (mono_tags, lifting)) 
    then have "\<exists>y\<in>?Y. (if G y \<and> \<not> Q y then \<eta> y else {}) \<noteq> {}"
      by (metis (mono_tags, lifting) * bot_pres_del) 
    from this have "(\<Union>y\<in>?Y. if G y \<and> \<not> Q y then \<eta> y else {}) \<noteq> {}" by blast}
  ultimately show "((\<Union>y\<in>?Y. if \<not> Q y then \<eta> y else {}) = {} \<longrightarrow>
        (\<Union>y\<in>?Y. if G y \<and> \<not> Q y then \<eta> y else {}) = {}) \<and>
       ((\<Union>y\<in>?Y. if \<not> Q y then \<eta> y else {}) \<noteq> {} \<longrightarrow>
        (\<Union>y\<in>?Y. if G y \<and> \<not> Q y then \<eta> y else {}) \<noteq> {})"
    by blast
qed

theorem dWeakening: 
assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun)
  by(auto simp: le_fun_def)

subsubsection{* Differential Cut *}

lemma wp_g_orbit_etaD:
  assumes "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>" and "\<forall> r\<in>{t0--t}. x r \<in> g_orbital (\<lambda>t. f) T S t0 a G"
  shows "\<forall>r\<in>{t0--t}. C (x r)"
proof
  fix r assume "r \<in> {t0--t}"
  then have "x r \<in> g_orbital (\<lambda>t. f) T S t0 a G" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital (\<lambda>t. f) T S t0 a G) \<longrightarrow> C y" 
    using assms(1) wp_nd_fun_etaD by fastforce
  ultimately show "C (x r)" by blast
qed

theorem DC:
  assumes "picard_ivp (\<lambda> t. f) T S L t0" 
    and "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym, simp_all)
  fix a
  show "g_orbital (\<lambda>a. f) T S t0 a G \<subseteq> g_orbital (\<lambda>a. f) T S t0 a (\<lambda>s. G s \<and> C s)"
  proof
    fix b assume "b \<in> g_orbital (\<lambda>a. f) T S t0 a G" 
    then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode (\<lambda>t. f)) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
      using assms(1) unfolding f2r_def by blast
    from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
      using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1))
    also have "\<forall>r\<in>{t0--t}. r \<in> T"
      using assms(1) \<open>t \<in> T\<close> picard_ivp.subsegment picard_ivp.init_time by blast
    ultimately have "\<forall> r\<in>{t0--t}. x r \<in> g_orbital (\<lambda>t. f) T S t0 a G"
      using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
    from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_etaD assms(2) by blast
    thus "b \<in> g_orbital (\<lambda>t. f) T S t0 a (\<lambda> s. G s \<and> C s)"
      using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> f2r_def x_solves by fastforce 
  qed
next show "\<And> a. g_orbital (\<lambda>t. f) T S t0 a (\<lambda> s. G s \<and> C s) \<subseteq> g_orbital (\<lambda>t. f) T S t0 a G" by auto
qed

theorem dCut:
  assumes "t0 \<in> T" and "interval T"
    and wp_C:"\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
proof(subst wp_nd_fun, clarsimp)
  fix t::real and x::"real \<Rightarrow> 'a" assume "P (x t0)" and "t \<in> T"  and "x t0 \<in> S"
and x_solves:"(x solves_ode (\<lambda> t s. f s))T S " and guard_x:"(\<forall> r \<in> {t0--t}. G (x r))"
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using \<open>t0 \<in> T\<close> by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using \<open>t0 \<in> T\<close> \<open>interval T\<close> \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
  ultimately have "\<forall>r\<in>{t0--t}. x r \<in> g_orbital (\<lambda>a. f) T S t0 (x t0) G"
    using x_solves \<open>x t0 \<in> S\<close> by blast
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_C \<open>P (x t0)\<close> by(subst (asm) wp_nd_fun, simp)
  hence "x t \<in> g_orbital (\<lambda>a. f) T S t0 (x t0) (\<lambda> s. G s \<and> C s)"
    using guard_x  \<open>t \<in> T\<close>  x_solves \<open>x t0 \<in> S\<close> by fastforce
  from this \<open>P (x t0)\<close> and wp_Q show "Q (x t)"
    by(subst (asm) wp_nd_fun, simp)
qed

corollary dCut_interval:
  assumes "t0 \<le> t" and "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>C\<rceil>" 
    and "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="C" in dCut)
  using assms by(simp_all add: interval_def)

subsubsection{* Differential Invariant *}

lemma DI_sufficiency:
  assumes "picard_ivp (\<lambda> t. f) T S L t0"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> \<le> wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>"
  apply(subst wp_nd_fun, subst wp_nd_fun, clarsimp)
  apply(erule_tac x="s" in allE, erule impE, rule_tac x="t0" in exI, simp_all)
  using assms picard_ivp.fixed_point_solves picard_ivp.init_time by metis

lemma 
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<lceil>G\<rceil> \<le> \<lceil>I'\<rceil>" and "t \<ge> 0"
    and "\<forall> x. (x solves_ode (\<lambda> t. f)){0..t} S \<longrightarrow> I (x 0) \<longrightarrow>
 (\<forall> t \<ge> 0. (\<forall>r\<in>{0--t}. I' (x r)) \<longrightarrow> (I (x t)))"
  shows "\<lceil>I\<rceil> \<le> wp ({[x\<acute>=f]{0..t} S @ 0 & G}) \<lceil>I\<rceil>"
  using assms apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff) apply clarify
  apply(erule_tac x="x" in allE)
  apply(erule impE, simp)+
  apply(erule_tac x="ta" in allE)
  by simp

definition pderivative :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
'a set \<Rightarrow> bool" ("(_)/ is'_pderivative'_of (_)/ with'_respect'_to (_) (_) (_)" [70, 65] 61) where
"I' is_pderivative_of I with_respect_to f T S \<equiv> bdd_below T \<and> (\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> 
I (x (Inf T)) \<longrightarrow> (\<forall> t \<in> T. (\<forall>r\<in>{(Inf T)--t}. I' (x r)) \<longrightarrow> (I (x t))))"

lemma dInvariant:
  assumes "\<lceil>G\<rceil> \<le> \<lceil>I'\<rceil>" and "I' is_pderivative_of I with_respect_to f T S"
  shows "\<lceil>I\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>I\<rceil>"
  using assms unfolding pderivative_def apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff)
  apply(clarify) by simp

lemma invariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s = 0"])
  using assms apply(simp, simp add: pderivative_def)
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
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply simp
  apply(rule invariant_eq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s = 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s = 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
   apply(rule_tac \<nu>="\<nu>" in invariant_eq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp add: pderivative_def)
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
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_geq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<ge> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_geq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp add: pderivative_def)
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
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_leq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<le> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_leq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp add: pderivative_def)
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
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_above_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s > 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s > 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_above_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls  by auto

lemma invariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp add: pderivative_def)
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
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_below_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode (\<lambda>t. f)) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s < 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  using \<open>t0 \<le> t\<close> apply(rule_tac C="\<lambda>s. \<theta> s < 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_below_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_meet:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>"
  using assms by(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun, subst wp_nd_fun, simp, blast)

theorem dInvariant_meet:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<and> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>")
  using impls apply(transfer, simp add: le_fun_def) apply auto[1]
    apply(rule invariant_meet)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_join:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>"
  using assms by(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun, subst wp_nd_fun, simp)

theorem dInvariant_join:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<or> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>")
  using impls apply(transfer, simp add: le_fun_def) apply auto[1]
    apply(rule invariant_join)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by auto


locale_deps

thm Rep_nd_fun  Rep_nd_fun_inject Rep_nd_fun_cases Rep_nd_fun_inverse
thm           Abs_nd_fun_inject Abs_nd_fun_cases Abs_nd_fun_inverse 

end