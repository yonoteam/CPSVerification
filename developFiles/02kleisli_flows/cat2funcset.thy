theory cat2funcset
imports
  "Abstract_HL"
  "Ordinary_Differential_Equations.Initial_Value_Problem"

begin

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and P2S2R.p2r ("\<lceil>_\<rceil>")
        and P2S2R.r2p ("\<lfloor>_\<rfloor>")
        and Modal_Kleene_Algebra_Models.rel_antidomain_kleene_algebra.fbox ("wp")

notation nd_fun.fbox ("wp")
abbreviation p2f :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

thm Abs_nd_fun_inverse Rep_nd_fun_inverse Abs_nd_fun_inject

lemma nd_fun_ext:"(\<And> z. x z = y z) \<Longrightarrow> (x\<^sup>\<bullet>) = (y\<^sup>\<bullet>)"
  by meson

lemma wp_nd_fun:"wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. y \<in> (F x) \<longrightarrow> P y\<rceil>"
  apply(simp add: Abstract_HL.nd_fun.fbox_def Abs_nd_fun_inverse)
  apply(simp add: Kleisli.ad_fun_def Kleisli.Kcomp_def)
  apply(simp add: Kleisli.Powf_def)
  apply(rule nd_fun_ext)
  by auto

lemma wp_nd_fun_etaD:"wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<eta>\<^sup>\<bullet> \<Longrightarrow> (\<forall>y. y \<in> (F x) \<longrightarrow> P y)"
  unfolding nd_fun.fbox_def apply(simp add: Abs_nd_fun_inverse ad_fun_def Kcomp_def Powf_def, clarify)
  apply(subst (asm) Abs_nd_fun_inject, simp_all)
  by (metis Int_Collect empty_iff empty_not_insert)

lemma p2f_etaD:"\<lceil>P\<rceil> = \<eta>\<^sup>\<bullet> \<Longrightarrow> P s"
  apply(subst (asm) Abs_nd_fun_inject, simp_all)
  by (metis Collect_conv_if empty_not_insert)

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

thm ubc_definitions

lemma(in continuous_rhs) continuous_currying:
  "x \<in> X \<Longrightarrow> continuous_on T (\<lambda> t. f t x)"
  using continuous by(auto intro: continuous_intros)

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

abbreviation "orbital f T S t0 x0 \<equiv> {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> (\<forall> r \<in> {t0--t}. G (x r)) \<and> x0 \<in> S}"

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

abbreviation "phi t s \<equiv> (apply_bcontfun (unique_on_bounded_closed.fixed_point t0 T s f S)) t"

lemma fixed_point_solves:
  assumes "s \<in> S"
  shows "((\<lambda> t. phi t s) solves_ode f)T S" and "phi t0 s = s "
  using assms is_ubc unique_on_bounded_closed.fixed_point_solution apply(metis (full_types)) 
  using assms is_ubc unique_on_bounded_closed.fixed_point_iv by(metis (full_types)) 

lemma fixed_point_usolves:
  assumes "s \<in> S" and "(x solves_ode f)T S" and "x t0 = s" and "t \<in> T"
  shows "x t = phi t s"
  using unique_on_bounded_closed.unique_solution is_ubc fixed_point_solves assms by blast

lemma orbital_collapses:
  shows "orbital f T S t0 s = {phi t s| t. t \<in> T \<and> s \<in> S}"
  apply(rule subset_antisym)
  using fixed_point_usolves apply(clarsimp, rule_tac x="t" in exI, simp)
  apply(clarsimp, rule_tac x="t" in exI, rule_tac x="(\<lambda> t. phi t s)" in exI, simp)
  using fixed_point_solves by blast

lemma g_orbital_collapses:
  shows "g_orbital f T S t0 s G = {phi t s| t. t \<in> T \<and> (\<forall> r \<in> {t0--t}. G (phi r s)) \<and> s \<in> S}"
  apply(rule subset_antisym)
  using fixed_point_usolves apply(clarsimp, rule_tac x="t" in exI, simp)
  apply (metis closed_segment_subset_domainI init_time)
  apply(clarsimp, rule_tac x="t" in exI, rule_tac x="(\<lambda> t. phi t s)" in exI)
  by(simp add: fixed_point_solves)

end

locale local_flow = picard_ivp "(\<lambda> t. f)" T S L 0 for f::"('a::banach) \<Rightarrow> 'a" and S T L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a" 
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

abbreviation "orbit s \<equiv> {\<phi> t s |t. t \<in> T \<and> s \<in> S}"
abbreviation "g_orbit s G \<equiv> {\<phi> t s |t. t \<in> T \<and> (\<forall> r \<in> {0--t}. G (\<phi> r s)) \<and> s \<in> S}"

lemma orbital_is_orbit:
  shows "orbital (\<lambda> t. f) T S 0 s = orbit s"
  by (metis (no_types, lifting) fixed_point_solves flow_def) 

lemma g_orbital_is_orbit:
  shows "g_orbital (\<lambda> t. f) T S 0 s G = g_orbit s G"
  using is_fixed_point unfolding g_orbital_collapses
  by (metis (mono_tags, lifting) closed_segment_subset_domainI picard_ivp.init_time picard_ivp_axioms) 

lemma "\<R> (\<lambda> s. orbit s) = {(s, \<phi> t s)|s t. t \<in> T \<and> s \<in> S}"
  apply(safe, simp_all add: f2r_def)
  by(rule_tac x="t" in exI, simp)

theorem wlp_orbit:"wp (orbit\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding f2r_def by (subst wp_nd_fun, rule nd_fun_ext, auto)

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

theorem flow_is_monoid_action:
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
    picard_ivp_def picard_ivp_axioms_def apply safe
  unfolding ubc_definitions by simp_all

abbreviation 
g_orbit :: "(('a :: banach) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 
'a nd_fun" ("(1[{x\<acute>=_}_ _ @ _ & _])") where 
"[{x\<acute>=f}T S @ t0 & G] \<equiv> ((\<lambda> s. g_orbital (\<lambda> t. f) T S t0 s G)\<^sup>\<bullet>)"

theorem wp_g_orbit:
  assumes "local_flow f S T L \<phi>"
  shows "wp [{x\<acute>=f}T S @ 0 & G] \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_nd_fun, rule nd_fun_ext)
  using assms by(subst local_flow.g_orbital_is_orbit, auto)

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

corollary line_DS:
  assumes "0 \<le> t"
  shows " wp [{x\<acute>=\<lambda>s. c}{0..t} UNIV @ 0 & G] \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda> s. c" _ _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow and assms by (blast, simp)

theorem DW:
  shows "wp [{x\<acute>=f}T S @ t0 & G] \<lceil>Q\<rceil> = wp [{x\<acute>=f}T S @ t0 & G] \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding nd_fun.fbox_def apply(simp add: Abs_nd_fun_inverse ad_fun_def Kcomp_def Powf_def)
  by(rule nd_fun_ext, auto)

thm nd_fun_ext p2f_etaD wp_nd_fun

lemma wp_g_orbit_etaD:
  assumes "wp [{x\<acute>=f}T S @ t0 & G] \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>" and "\<forall> r\<in>{t0--t}. x r \<in> g_orbital (\<lambda>t. f) T S t0 a G"
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
    and "wp [{x\<acute>=f}T S @ t0 & G] \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp [{x\<acute>=f}T S @ t0 & G] \<lceil>Q\<rceil> = wp [{x\<acute>=f}T S @ t0 & \<lambda>s. G s \<and> C s] \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym)
  fix a
  show "g_orbital (\<lambda>t. f) T S t0 a G \<subseteq> g_orbital (\<lambda>t. f) T S t0 a (\<lambda> s. G s \<and> C s)"
  proof
    fix b assume "b \<in> g_orbital (\<lambda>t. f) T S t0 a G" 
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
  next show "\<And> a. g_orbital (\<lambda>t. f) T S t0 a (\<lambda> s. G s \<and> C s) \<subseteq> g_orbital (\<lambda>t. f) T S t0 a G"
      by auto
qed

lemma DI_sufficiency:
  assumes picard:"picard_ivp (\<lambda> t. f) T S L t0"
  shows "((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>Q\<rceil>)\<^sub>\<bullet>) s \<subseteq> ((wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>)\<^sub>\<bullet>) s"
  apply(subst wp_nd_fun, subst wp_nd_fun, simp add: Abs_nd_fun_inverse)
  apply(clarsimp, erule_tac x="s" in allE)
  using picard_ivp.fixed_point_solves picard_ivp.init_time picard
  by (metis closed_segment_idem equals0D insert_iff)

lemma closed_segment_mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "(\<And>r. r\<in>{a--b} \<Longrightarrow> (f has_derivative f' r) (at r within {a--b}))" and "a \<le> b"
  shows "\<exists>r\<in>{a--b}. f b - f a = f' r (b - a)"
  using assms closed_segment_eq_real_ivl and mvt_very_simple by auto

lemma dInvariant:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<And>s. G s \<Longrightarrow> F s" and "bdd_below T"
    and FisPrimedI:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> I (x (Inf T)) \<longrightarrow>
    (\<forall> t \<in> T. (\<forall>r\<in>{(Inf T)--t}. F (x r)) \<longrightarrow> (I (x t)))"
  shows "(\<lceil>I\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ (Inf T) & G] \<lceil>I\<rceil>)\<^sub>\<bullet>) s"
  apply(subst wp_nd_fun, simp add: Abs_nd_fun_inverse, clarsimp)
  using assms by (simp add: cInf_lower) 

lemma dInvariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<And>s. G s \<Longrightarrow> \<nu> s = 0" and "bdd_below T"
  shows "(\<lceil>\<lambda>s. \<theta> s = 0\<rceil>\<^sub>\<bullet>)s \<subseteq> ((wp [{x\<acute>=f}T S @ (Inf T) & G] \<lceil>\<lambda>s. \<theta> s = 0\<rceil>)\<^sub>\<bullet>) s"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s = 0"])
  using assms apply(simp, simp)
proof(clarify)
  fix x and t 
  assume x_ivp:"(x solves_ode (\<lambda>t. f)) T S" "\<theta> (x (Inf T)) = 0"  
    and tHyp:"t \<in> T" and eq0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) = 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R 0)) 
    (at r within {(Inf T)--t})" using eq0 by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  thus "\<theta> (x t) = 0" 
    using x_ivp(2) by (metis right_minus_eq scale_zero_right)
qed

lemma dInvariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<And>s. G s \<Longrightarrow> \<nu> s \<ge> 0" and "bdd_below T"
  shows "(\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>\<^sub>\<bullet>)s \<subseteq> ((wp [{x\<acute>=f}T S @ (Inf T) & G] \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>)\<^sub>\<bullet>) s"
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

lemma dInvariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<And>s. G s \<Longrightarrow> \<nu> s \<ge> 0" and "bdd_below T"
  shows "(\<lceil>\<lambda>s. \<theta> s > 0\<rceil>\<^sub>\<bullet>)s \<subseteq> ((wp [{x\<acute>=f}T S @ (Inf T) & G] \<lceil>\<lambda>s. \<theta> s > 0\<rceil>)\<^sub>\<bullet>) s"
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

lemma dInvariant_meet:
  assumes "(\<lceil>I1\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>I1\<rceil>)\<^sub>\<bullet>) s"
    and "(\<lceil>I2\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>I2\<rceil>)\<^sub>\<bullet>) s"
  shows "(\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>)\<^sub>\<bullet>) s"
  using assms apply(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun)
  apply(subst wp_nd_fun, simp add: Abs_nd_fun_inverse)
  by blast

lemma dInvariant_join:
  assumes "(\<lceil>I1\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>I1\<rceil>)\<^sub>\<bullet>) s"
    and "(\<lceil>I2\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>I2\<rceil>)\<^sub>\<bullet>) s"
  shows "(\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>\<^sub>\<bullet>) s \<subseteq> ((wp [{x\<acute>=f}T S @ t0 & G] \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>)\<^sub>\<bullet>) s"
  using assms apply(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun)
  apply(subst wp_nd_fun, simp add: Abs_nd_fun_inverse)
  by blast

end