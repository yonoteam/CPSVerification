theory flow_locales
  imports
  "Ordinary_Differential_Equations.Initial_Value_Problem"

begin

section {* Flow Locales *}

named_theorems ubc_definitions "definitions used in the locale unique_on_bounded_closed"

declare unique_on_bounded_closed_def [ubc_definitions]
    and unique_on_bounded_closed_axioms_def [ubc_definitions]
    and unique_on_closed_def [ubc_definitions]
    and compact_interval_def [ubc_definitions]
    and compact_interval_axioms_def [ubc_definitions]
    and self_mapping_def [ubc_definitions]
    and self_mapping_axioms_def [ubc_definitions]
    and continuous_rhs_def [ubc_definitions]
    and closed_domain_def [ubc_definitions]
    and global_lipschitz_def [ubc_definitions]
    and interval_def [ubc_definitions]
    and nonempty_set_def [ubc_definitions]

lemma(in unique_on_bounded_closed) unique_on_bounded_closed_on_compact_subset:
  assumes "t0 \<in> T'" and "x0 \<in> X" and "T' \<subseteq> T" and "compact_interval T'" 
  shows "unique_on_bounded_closed t0 T' x0 f X L"
  apply(unfold_locales)
  using \<open>compact_interval T'\<close> unfolding ubc_definitions apply simp+
  using \<open>t0 \<in> T'\<close> apply simp
  using \<open>x0 \<in> X\<close> apply simp
  using \<open>T' \<subseteq> T\<close> self_mapping apply blast
  using \<open>T' \<subseteq> T\<close> continuous apply(meson Sigma_mono continuous_on_subset subsetI)
  using \<open>T' \<subseteq> T\<close> lipschitz apply blast
  using \<open>T' \<subseteq> T\<close> lipschitz_bound by blast

text{* The first locale imposes conditions for applying the Picard-Lindeloef theorem following 
the people who created the Ordinary Differential Equations entry in the AFP. *}

locale picard_ivp = continuous_rhs T S f + global_lipschitz T S f L 
  for f::"real \<Rightarrow> ('a::banach) \<Rightarrow> 'a" and T::"real set" and S L + 
  fixes t0::real
  assumes init_time:"t0 \<in> T"
    and nonempty_time: "T \<noteq> {}"
    and interval_time: "is_interval T"
    and compact_time: "compact T"
    and lipschitz_bound: "\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> abs (s - t) * L < 1"
    and closed_domain: "closed S"
    and solution_in_domain:"\<And>x s t. t \<in> T \<Longrightarrow> x t0 = s \<Longrightarrow> x \<in> {t0--t} \<rightarrow> S \<Longrightarrow> 
      continuous_on {t0--t} x \<Longrightarrow> x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> S"
begin

sublocale compact_interval
  using interval_time nonempty_time compact_time by(unfold_locales, auto)

lemma min_max_interval:
  obtains m M where "T = {m .. M}"
  using T_def by blast

lemma subinterval:
  assumes "t \<in> T"
  obtains t1 where  "{t .. t1} \<subseteq> T"
  using assms interval_subset_is_interval interval_time by fastforce 

lemma subsegment:
  assumes "t1 \<in> T" and "t2 \<in> T"
  shows "{t1 -- t2} \<subseteq> T"
  using assms closed_segment_subset_domain by blast

lemma is_ubc:
  assumes "s \<in> S"
  shows "unique_on_bounded_closed t0 T s f S L"
  using assms unfolding ubc_definitions apply safe
  prefer 6 using solution_in_domain apply simp
  prefer 2 using nonempty_time apply fastforce
  by(auto simp: compact_time interval_time init_time
      closed_domain lipschitz lipschitz_bound continuous)

lemma unique_solution:
  assumes "(x solves_ode f)T S" and "x t0 = s"
    and "(y solves_ode f)T S" and "y t0 = s"
    and "s \<in> S" and "t \<in> T" 
  shows "x t = y t"
  using unique_on_bounded_closed.unique_solution is_ubc assms by blast

abbreviation "phi t s \<equiv> (apply_bcontfun (unique_on_bounded_closed.fixed_point t0 T s f S)) t"

lemma fixed_point_solves:
  assumes "s \<in> S"
  shows "((\<lambda> t. phi t s) solves_ode f)T S" and "phi t0 s = s "
  using assms is_ubc unique_on_bounded_closed.fixed_point_solution apply(metis (full_types)) 
  using assms is_ubc unique_on_bounded_closed.fixed_point_iv by(metis (full_types)) 

lemma fixed_point_usolves:
  assumes "(x solves_ode f)T S" and "x t0 = s" and "t \<in> T"
  shows "x t = phi t s"
  using assms(1,2) unfolding solves_ode_def apply(subgoal_tac "s \<in> S")
  using unique_solution fixed_point_solves assms apply blast
  unfolding Pi_def using init_time by auto

end

text{* The next locale particularizes the previous one to an initial time equal to 0. Thus making
the function that maps every initial point to its solution a (local) ``flow''. *}
locale local_flow = picard_ivp "(\<lambda> t. f)" T S L 0 for f::"('a::banach) \<Rightarrow> 'a" and S T L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (* delete s below *)
  assumes flow_def:"\<And> x s t. t \<in> T \<Longrightarrow> (x solves_ode (\<lambda> t. f))T S \<Longrightarrow> x 0 = s \<Longrightarrow> \<phi> t s = x t"
begin

lemma is_fixed_point:
  assumes "s \<in> S" and "t \<in> T"
  shows "\<phi> t s = phi t s"
  using flow_def assms fixed_point_solves init_time by simp

theorem solves:
  assumes "s \<in> S"
  shows "((\<lambda> t. \<phi> t s) solves_ode (\<lambda> t. f))T S"
  using assms init_time fixed_point_solves(1) and is_fixed_point by auto

theorem on_init_time:
  assumes "s \<in> S"
  shows "\<phi> 0 s = s"
  using assms init_time fixed_point_solves(2) and is_fixed_point by auto

lemma is_banach_endo:
  assumes "s \<in> S" and "t \<in> T"
  shows "\<phi> t s \<in> S"
  apply(rule_tac A="T" in Pi_mem)
  using assms solves
  unfolding solves_ode_def by auto

lemma solves_on_compact_subset:
  assumes "T' \<subseteq> T" and "compact_interval T'" and "0 \<in> T'"
  shows "t \<in> T' \<Longrightarrow> (x solves_ode (\<lambda>t. f)) T' S \<Longrightarrow> \<phi> t (x 0) = x t"
proof-
  fix t and x assume "t \<in> T'" and x_solves:"(x solves_ode (\<lambda>t. f))T' S"
  from this and \<open>0 \<in> T'\<close> have "x 0 \<in> S" unfolding solves_ode_def by blast
  then have "((\<lambda> \<tau>. \<phi> \<tau> (x 0)) solves_ode (\<lambda> \<tau>. f))T S" using solves by blast
  hence flow_solves:"((\<lambda> \<tau>. \<phi> \<tau> (x 0)) solves_ode (\<lambda> \<tau>. f))T' S" 
    using \<open>T' \<subseteq> T\<close> solves_ode_on_subset by (metis subset_eq) 
  have "unique_on_bounded_closed 0 T (x 0) (\<lambda> \<tau>. f) S L"
    using is_ubc and \<open>x 0 \<in> S\<close> by blast
  then have "unique_on_bounded_closed 0 T' (x 0) (\<lambda> \<tau>. f) S L" 
    using unique_on_bounded_closed.unique_on_bounded_closed_on_compact_subset
    \<open>0 \<in> T'\<close> \<open>x 0 \<in> S\<close> \<open>T' \<subseteq> T\<close> and \<open>compact_interval T'\<close> by blast
  moreover have "\<phi> 0 (x 0) = x 0" 
    using on_init_time and \<open>x 0 \<in> S\<close> by blast
  ultimately show "\<phi> t (x 0) = x t" 
    using unique_on_bounded_closed.unique_solution flow_solves x_solves and \<open>t \<in> T'\<close> by blast 
qed

end

lemma flow_on_compact_subset:
  assumes flow_from_Y:"local_flow f S T' L \<phi>" and "T \<subseteq> T'" and "compact_interval T" and "0 \<in> T"
  shows "local_flow f S T L \<phi>"
  unfolding ubc_definitions apply(unfold_locales, safe)
  prefer 10 using assms and local_flow.solves_on_compact_subset apply blast
  using assms unfolding local_flow_def picard_ivp_def ubc_definitions 
    apply(meson Sigma_mono continuous_on_subset subsetI)
  using assms unfolding local_flow_def picard_ivp_def picard_ivp_axioms_def 
    local_flow_axioms_def ubc_definitions apply (simp_all add: subset_eq)
  by blast

text{* The last locale shows that the function introduced in its predecesor is indeed a flow. That
is, it is a group action on the additive part of the real numbers.*}
locale global_flow = local_flow f UNIV UNIV L \<phi> for f L \<phi>
begin 

lemma add_flow_solves:"((\<lambda>\<tau>. \<phi> (\<tau> + t) s) solves_ode (\<lambda> t. f))UNIV UNIV"
  unfolding solves_ode_def apply safe
  apply(subgoal_tac "((\<lambda>\<tau>. \<phi> \<tau> s) \<circ> (\<lambda>\<tau>. \<tau> + t) has_vderiv_on 
    (\<lambda>x. (\<lambda>\<tau>. 1) x *\<^sub>R (\<lambda>t. f (\<phi> t s)) ((\<lambda>\<tau>. \<tau> + t) x))) UNIV", simp add: comp_def)
  apply(rule has_vderiv_on_compose) 
  using solves min_max_interval unfolding solves_ode_def apply auto[1]
  apply(rule_tac f'1="\<lambda> x. 1 " and g'1="\<lambda> x. 0" in derivative_intros(190))
  apply(rule derivative_intros, simp)+
  by auto

theorem flow_is_group_action:
  shows "\<phi> 0 s = s"
    and "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
proof-
  show "\<phi> 0 s = s" using on_init_time by simp
  have g1:"\<phi> (0 + t2) s = \<phi> t2 s" by simp
  have g2:"((\<lambda> \<tau>. \<phi> (\<tau> + t2) s) solves_ode (\<lambda> t. f))UNIV UNIV" 
    using add_flow_solves by simp
  have h0:"\<phi> t2 s \<in> UNIV" 
    using is_banach_endo by simp
  hence h1:"\<phi> 0 (\<phi> t2 s) = \<phi> t2 s" 
    using on_init_time by simp
  have h2:"((\<lambda> \<tau>. \<phi> \<tau> (\<phi> t2 s)) solves_ode (\<lambda> t. f))UNIV UNIV"
    apply(rule_tac S="UNIV" and Y="UNIV" in solves_ode_on_subset)
    using h0 solves by auto 
  from g1 g2 h1 and h2 have "\<And> t. \<phi> (t + t2) s = \<phi> t (\<phi> t2 s)"
    using unique_on_bounded_closed.unique_solution is_ubc by blast
  thus "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)" by simp
qed

end

lemma localize_global_flow:
  assumes "global_flow f L \<phi>" and "compact_interval T" and "closed S"
  shows "local_flow f S T L \<phi>"
  using assms unfolding global_flow_def local_flow_def 
    picard_ivp_def picard_ivp_axioms_def by simp

subsection{* Example *}

text{* Finally, we exemplify a procedure for introducing pairs of vector fields and their respective 
flows using the previous locales. *}

lemma constant_is_ubc:"0 \<le> t \<Longrightarrow> unique_on_bounded_closed 0 {0..t} s (\<lambda>t s. c) UNIV (1 / (t + 1))"
  unfolding ubc_definitions by(simp add: nonempty_set_def lipschitz_on_def, safe, simp)

lemma line_solves_constant:"((\<lambda> \<tau>. x + \<tau> *\<^sub>R c) solves_ode (\<lambda>t s. c)) {0..t} UNIV"
  unfolding solves_ode_def apply simp
  apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(190))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma line_is_local_flow:
"0 \<le> t \<Longrightarrow> local_flow (\<lambda> s. (c::'a::banach)) UNIV {0..t} (1/(t + 1)) (\<lambda> t x. x + t *\<^sub>R c)"
  unfolding local_flow_def local_flow_axioms_def picard_ivp_def
    picard_ivp_axioms_def ubc_definitions
  apply(simp add: nonempty_set_def lipschitz_on_def del: real_scaleR_def, safe, simp)
  subgoal for x \<tau>
    apply(rule unique_on_bounded_closed.unique_solution
        [of 0 "{0..t}" "x 0" "(\<lambda>t s. c)" UNIV "(1 / (t + 1))" "(\<lambda>a. x 0 + a *\<^sub>R c)"])
    using constant_is_ubc apply blast
    using line_solves_constant by(blast, simp_all).

end