theory playing_flows
imports
  "Abstract_HL"
  "Ordinary_Differential_Equations.Initial_Value_Problem"
  "HOL-Library.FSet" (* Finite sets. *)
  "HOL-Analysis.Cartesian_Euclidean_Space"

begin

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and VC_KAD.gets ("_ ::= _" [70, 65] 61)

lemma wp_rel:"wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
  have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
    by (simp add: wp_trafo pointfree_idE)
  thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
    by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

lemma p2r_IdD:"\<lceil>P\<rceil> = Id \<Longrightarrow> P s"
  by (metis Id_O_R VC_KAD.p2r_neg_hom d_p2r empty_iff p2r_eq_prop p2r_subid 
      rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.addual.bbox_def
      rel_antidomain_kleene_algebra.am1 rel_antidomain_kleene_algebra.fbox_one rpr wp_trafo)

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

print_commands
print_facts
print_context

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

definition invariant :: "'a pred \<Rightarrow> bool" 
  where "invariant P = (\<forall> x. (x solves_ode f)T S \<longrightarrow> (\<forall> t \<in> T. P (x t)))"

lemma invariantI:
  assumes "\<forall> x. (x solves_ode f)T S \<longrightarrow> (\<forall> t \<in> T. P (x t))"
  shows "invariant P"
  using assms unfolding invariant_def by simp

end

lemma 
  fixes f::"real \<Rightarrow> (real^'a \<Rightarrow> real^'a)" 
  assumes pic:"picard_ivp f T S L t0"
    and "\<forall> x. (x solves_ode f) T S \<longrightarrow> (\<forall> t \<in> T. (f t (x t)) $ i = 0)"
  shows "picard_ivp.invariant f T S (\<lambda> x. x $ i = 0)"
  using pic apply(rule picard_ivp.invariantI)
proof(clarsimp)
  fix t::real and x assume sol:"(x solves_ode f) T S" and "t \<in> T"
  from this and assms(2) have "\<forall> \<tau> \<in> T. (f \<tau> (x \<tau>)) $ i = 0" by blast
  also from pic obtain t1 where "{t .. t1} \<subseteq> T"
    using picard_ivp.subinterval \<open>t \<in> T\<close> by blast
  hence "\<forall> \<tau> \<in> {t .. t1}. (f \<tau> (x \<tau>)) $ i = 0"
    using calculation by blast 
oops

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

theorem wp_orbit:"wp (\<R> (\<lambda> s. orbit s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding f2r_def by (subst wp_rel, auto)

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
g_orbit :: "(('a :: banach) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1{[x\<acute>=_]_ _ @ _ & _})")
  where "{[x\<acute>=f]T S @ t0 & G} \<equiv> \<R> (\<lambda> s. g_orbital (\<lambda> t. f) T S t0 s G)"

theorem wp_g_orbit:
  assumes "local_flow f S T L \<phi>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding f2r_def apply(subst wp_rel)
  using assms apply(subst local_flow.g_orbital_is_orbit, simp)
  by auto

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
  shows " wp {[x\<acute>=\<lambda>s. c]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda> s. c" _ _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow and assms by (blast, simp)

theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding rel_antidomain_kleene_algebra.fbox_def rel_ad_def f2r_def
  apply(simp add: relcomp.simps p2r_def)
  apply(rule subset_antisym) apply fastforce
  by fastforce


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
  assumes "picard_ivp (\<lambda> t. f) T S L t0" 
    and "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = Id"
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s} \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, safe)
fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}" 
  then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode (\<lambda>t. f)) T S" and "x t0 = a" 
    and "(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
    using assms(1) unfolding f2r_def by blast
  from \<open>\<forall>r\<in>{t0--t}. G (x r)\<close> have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using assms(1) \<open>t \<in> T\<close> picard_ivp.subsegment picard_ivp.init_time by blast
  ultimately have "\<forall> r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_IdD assms(2) by blast
  thus "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}"
    using \<open>\<forall>r\<in>{t0--t}. G (x r)\<close> \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> f2r_def x_solves by fastforce 
next
  fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}" 
  then show "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}"
    unfolding f2r_def by blast
qed

lemma DI_sufficiency:
  assumes "local_flow f S T L \<phi>"
  shows "\<lceil>\<lambda>s. \<forall>t\<in>T. s \<in> S \<longrightarrow> (\<forall>r\<in>{0--t}. G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil> \<subseteq> wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>"
  apply(clarsimp, erule_tac x="0" in ballE)
  using assms apply(simp_all add: picard_ivp.init_time local_flow.on_init_time local_flow_def)
  by(simp add: picard_ivp_def picard_ivp_axioms_def)

theorem DI_constant:
  assumes "local_flow f S T L \<phi>"
    and "\<lceil>G\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda>s. 0 = 0\<rceil>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda> s. Q c\<rceil> = wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q c\<rceil>"
  apply(subst wp_g_orbit) using assms(1) apply simp
  apply(rule subset_antisym, rule DI_sufficiency) using assms(1) apply simp
  using assms apply(subst (asm) wp_g_orbit, simp, simp)
  apply(clarsimp, erule_tac x="0" in ballE)
  by(simp_all add: local_flow.on_init_time)

lemma 
  fixes f::"('c::{zero,ord,real_normed_vector}) \<Rightarrow> ('a::real_normed_vector)^'b"
  assumes "(f has_derivative f') (at x within I)"
  shows "((\<lambda> t. (f t) $ i) has_derivative (\<lambda> t. (f' t) $ i)) (at x within I)"
  unfolding has_derivative_def bounded_linear_def bounded_linear_axioms_def apply(rule conjI)+
  using assms unfolding has_derivative_def bounded_linear_def bounded_linear_axioms_def linear_def
  oops

lemma postcondition_is_guard:
  assumes "t \<in> T" and "0 \<le> (t::('a::{zero,preorder}))" and "{0..t} \<subseteq> T" 
    and pHyp:"\<forall>r\<in>{0..t}. P (g r)" and *:" \<forall>\<tau>. \<tau> \<in> T \<and> 0 \<le> \<tau> \<longrightarrow> (\<forall>r\<in>{0..\<tau>}. P (g r)) \<longrightarrow> Q (g \<tau>)"
  shows "\<forall>r\<in>{0..t}. Q (g r)"
proof(clarsimp)
  fix r assume "0 \<le> r" and "r \<le> t"
  have "\<forall>\<tau>\<in>{0..r}. P (g \<tau>)"
    using pHyp and \<open>r \<le> t\<close> by (meson atLeastAtMost_iff le_left_mono)
  moreover have "r \<in> T \<and> 0 \<le> r" 
    using \<open>{0..t} \<subseteq> T\<close> \<open>0 \<le> r\<close> and \<open>r \<le> t\<close> by auto
  ultimately show "Q (g r)"
    using * by blast
qed

lemma 
  assumes flow:"local_flow f UNIV T L \<phi>" and "G s \<longrightarrow> (s::real^'a) = 0" 
    and "t \<in> T" and "0 \<le> t" and "\<forall>r\<in>{0..t}. G (\<phi> r s)"
    and " \<forall>\<tau>. \<tau> \<in> T \<and> 0 \<le> \<tau> \<longrightarrow> (\<forall>r\<in>{0..\<tau>}. G (\<phi> r s)) \<longrightarrow> (f (\<phi> \<tau> s)) $ i = 0"
  shows "(\<phi> t s) $ i = 0"
proof-
  have "((\<lambda>t. \<phi> t s) solves_ode (\<lambda>t. f)) T UNIV" 
    using assms and local_flow.solves by blast
  then have "\<forall>\<tau> \<in> T. ((\<lambda>t. \<phi> t s) has_derivative (\<lambda>x. x *\<^sub>R f (\<phi> \<tau> s))) (at \<tau> within T)"
    by (simp add: solves_ode_def has_vderiv_on_def has_vector_derivative_def)
  also have "{0..t} \<subseteq> T" using \<open>t\<in>T\<close> assms(1) local_flow.axioms(1) interval_subset_is_interval
    by (metis interval_cbox  picard_ivp.init_time picard_ivp.interval_time) 
  ultimately have dv:"\<forall>\<tau> \<in> {0..t}. ((\<lambda>t. \<phi> t s) has_derivative (\<lambda>x. x *\<^sub>R f (\<phi> \<tau> s))) (at \<tau> within {0..t})"
    by (meson contra_subsetD has_derivative_subset)
  from assms have "\<forall>r\<in>{0..t}. (f (\<phi> r s)) $ i = 0"
    apply(rule_tac g="\<lambda> r. \<phi> r s" and T="T" and P="G" in postcondition_is_guard)
    by(simp_all add: local_flow.axioms(1) \<open>{0..t} \<subseteq> T\<close>)
  hence "\<forall>\<tau> \<in> {0..t}. ((\<lambda>t. (\<phi> t s) $ i) has_derivative (\<lambda>x. 0)) (at \<tau> within {0..t})"
    using dv sorry
  then have "\<exists>x\<in>{0..t}. (\<phi> t s) $ i - (\<phi> 0 s) $ i = (\<lambda>t. 0) (t - 0)"
    using \<open>0\<le>t\<close> by(rule_tac f="\<lambda> t. (\<phi> t s) $ i" and f'="\<lambda>x t. 0" in mvt_very_simple, simp_all)
  thus "(\<phi> t s) $ i = 0" using local_flow.on_init_time sorry
qed

lemma 
  assumes flow:"local_flow f UNIV T L \<phi>" and "G s \<longrightarrow> (s::real) = 0" 
    and "t \<in> T" and "0 \<le> t" and "\<forall>r\<in>{0..t}. G (\<phi> r s)" 
    and " \<forall>\<tau>. \<tau> \<in> T \<and> 0 \<le> \<tau> \<longrightarrow> (\<forall>r\<in>{0..\<tau>}. G (\<phi> r s)) \<longrightarrow> f (\<phi> \<tau> s) = 0"
  shows "\<phi> t s = 0"
proof-
  have "((\<lambda>t. \<phi> t s) solves_ode (\<lambda>t. f)) T UNIV" 
    using assms and local_flow.solves by blast
  then have "\<forall>\<tau> \<in> T. ((\<lambda>t. \<phi> t s) has_derivative (\<lambda>x. x *\<^sub>R f (\<phi> \<tau> s))) (at \<tau> within T)"
    by (simp add: solves_ode_def has_vderiv_on_def has_vector_derivative_def)
  also have "{0..t} \<subseteq> T" using \<open>t\<in>T\<close> assms(1) local_flow.axioms(1) interval_subset_is_interval
    by (metis interval_cbox  picard_ivp.init_time picard_ivp.interval_time) 
  ultimately have dv:"\<forall>\<tau> \<in> {0..t}. ((\<lambda>t. \<phi> t s) has_derivative (\<lambda>x. x *\<^sub>R f (\<phi> \<tau> s))) (at \<tau> within {0..t})"
    by (meson contra_subsetD has_derivative_subset)
  from assms have "\<forall>r\<in>{0..t}. (f (\<phi> r s)) = 0"
    apply(rule_tac g="\<lambda> r. \<phi> r s" and T="T" and P="G" in postcondition_is_guard)
    by(simp_all add: local_flow.axioms(1) \<open>{0..t} \<subseteq> T\<close>)
  hence "\<forall>\<tau> \<in> {0..t}. ((\<lambda>t. \<phi> t s) has_derivative (\<lambda>t. 0)) (at \<tau> within {0..t})" using dv by auto
  then have "\<exists>x\<in>{0..t}. \<phi> t s - \<phi> 0 s = (\<lambda>t. 0) (t - 0)"
    using \<open>0\<le>t\<close> by(rule_tac f="\<lambda> t. \<phi> t s" and f'="\<lambda>x t. 0" in mvt_very_simple, simp_all)
  thus "\<phi> t s = 0" using local_flow.on_init_time 
    by (metis UNIV_I flow assms(2) \<open>0\<le>t\<close> assms(5) atLeastAtMost_iff order_refl right_minus_eq)
qed

theorem 
  assumes "local_flow f S T L \<phi>"
    and "\<lceil>G\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda>s. 0 = 0\<rceil>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda> s. Q c\<rceil> = wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q c\<rceil>"
  using assms(1) apply(subst wp_g_orbit, simp)
  apply(rule subset_antisym) apply(rule DI_sufficiency) apply simp
  using assms(2) apply(subst (asm) wp_g_orbit, simp)
  apply(clarsimp, erule_tac x="0" in ballE)
  by(simp_all add: local_flow.on_init_time)

theorem DI_var:
  assumes "local_flow f S T L \<phi>"
    and "\<lceil>G\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda>x. f x = 0\<rceil>"
  shows "wp ({[x\<acute>=f]T S @ 0 & G}) \<lceil>\<lambda> x. x = 0\<rceil> = wp \<lceil>G\<rceil> \<lceil>\<lambda> x. x \<in> S \<longrightarrow> x = 0\<rceil>"
  using assms(1) apply(subst wp_g_orbit, simp)
  apply(rule subset_antisym) apply(rule DI_sufficiency) apply simp
  using assms(2) apply(subst (asm) wp_g_orbit, simp, clarsimp)
  apply(thin_tac "\<lceil>G\<rceil> \<subseteq> wp _ _", erule_tac x="s" in allE)
  apply(erule_tac impE)
   apply(erule_tac x="0" in ballE, simp_all add: local_flow.axioms(1) local_flow.on_init_time)
  oops


(**************************************************************************************************)
term "x ** x"
term "linear x"

term "x::real^('a::finite)"
term "r_orbit (\<lambda> t x. x + t *\<^sub>R (c::real^'a)) {-t .. t}"
term "(($) (x::real^'a))"
term "\<chi> i. (1::real)"
term "vec_lambda ((($) (x::real^'a))(i := \<pi>))"
term "\<lambda> f x y. f(x := y)"
term "override_on (($) (x::real^'a))"
term "\<chi> i. (($) (x::real^'a))(i := \<pi>)"
(* OBS: instance vec :: (banach, finite) banach *)
(* definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
   "v ::= e = {(s,s (v := e s)) |s. True}" 
   string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel                'a store = string  \<Rightarrow> 'a
   string \<Rightarrow> ((string  \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> (string  \<Rightarrow> 'a) rel  real^'a = 'a \<Rightarrow> real
   string \<Rightarrow> ((string  \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> real) rel
*)

abbreviation assign :: "('a::finite) \<Rightarrow> real \<Rightarrow> (real, 'a) vec \<Rightarrow> ((real, 'a) vec) set" 
("_ ::= _" [70, 70] 70) where "i ::= r \<equiv> (\<lambda>x. {vec_lambda ((($) x)(i:= r))})"

term "\<R>(i ::= r)"

lemma "y \<in> (i ::= r) x  \<Longrightarrow> ($) y = (($) x)(i := r)"
by auto

typedef vars ="{''x'',''v'',''a'',''c''}" (*morphisms var str*)
apply(rule_tac x="''x''" in exI)
by simp

lemma card_of_vars:"card {''x'',''v'',''a'',''c''} = 4"
by auto

lemma CARD_of_vars:"CARD(vars) = 4"
using type_definition.card type_definition_vars by fastforce 

instance vars::finite
apply(standard, subst bij_betw_finite[of Rep_vars UNIV "{''x'',''v'',''a'',''c''}"])
apply(rule bij_betwI')
apply (simp add: Rep_vars_inject)
using Rep_vars apply blast
apply (metis Abs_vars_inverse UNIV_I)
by simp

abbreviation ith :: "(real, vars) vec \<Rightarrow> string \<Rightarrow> real" (infixl "\<downharpoonleft>" 90) where
"s \<downharpoonleft> x \<equiv> s $ Abs_vars x"

term "(\<chi> i::vars. x \<downharpoonleft> ''v'')"
thm line_DS

corollary(* cannot apply the subst rule because \<chi> i. x \<downharpoonleft> ''v'' depends on the function input x. *)
assumes "0 \<le> t"
shows " wp (\<R>(orbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R (\<chi> i. x \<downharpoonleft> ''v'')) {0..t})) \<lceil>Q\<rceil> = 
\<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. Q (x + \<tau> *\<^sub>R (\<chi> i. x \<downharpoonleft> ''v''))\<rceil>"
apply(subst line_DS[of "(\<chi> i. x \<downharpoonleft> ''v'')"])
oops

lemma
"PRE (\<lambda> s. s \<downharpoonleft> ''x'' = 0 \<and> s \<downharpoonleft> ''c'' > 0)
((\<R>((Abs_vars ''a'') ::= s \<downharpoonleft> ''c''));(\<R>(orbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R (\<chi> i. x \<downharpoonleft> ''v'')) {0..t})))\<^sup>*
POST (\<lambda> s. s \<downharpoonleft> ''x'' \<ge> 0)"
oops

(* 
TYPE: {v1, v2, v3, ..., vN}
VECTORS: (\<lbrakk>v1\<rbrakk>,\<lbrakk>v2\<rbrakk>,\<lbrakk>v3\<rbrakk>,...,\<lbrakk>vN\<rbrakk>)

*)

term "x::('a::finite_UNIV)"
lemma (in type_definition) "UNIV > 0"
oops(**)

thm bij_betw_same_card bij_betwI
term "of_real"    (* real \<Rightarrow> 'a *)
term "of_nat"     (* nat \<Rightarrow> 'a *)
term "real_of_nat"(* nat \<Rightarrow> real *)
term "int"        (* nat \<Rightarrow> int *)
term "nat"        (* int \<Rightarrow> nat *)
term "real"       (* nat \<Rightarrow> real *)
term "numeral" 

typedef ('a::finite) sized_real_sets = "{x::real set|x. CARD('a) = card x}"
proof-
obtain n::nat where "card(UNIV::'a set) = n" by simp
let ?x = "{(of_nat m)::real |m. m < n}"
have "card {m|m. m < n} = n" by simp
have "card ?x = card {m|m. m < n}"
apply(subst bij_betw_same_card[of "\<lambda> n. of_nat n" "{m|m. m < n}" ?x])
apply(rule bij_betwI[of real "{m |m. m < n}" ?x "\<lambda> x. if (\<exists> n. real n = x) then n else 0"])
apply simp
unfolding Pi_def apply(clarsimp, safe)
oops

(**************************************************************************************************)

definition subst :: "string \<Rightarrow> 'a \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> ('a store \<Rightarrow> 'a)" where
"subst x t f = (\<lambda> s. f (s(x := t)))"

value "subst ''x'' t (\<lambda> s. s ''x'' + c \<cdot> s ''y'')"

record ('a,'b,'c,'d)fila =
  entrada1 :: "'a \<Rightarrow> 'a" ("c\<index>")
  entrada2 :: "'d \<Rightarrow> 'b" ("c\<two>")
  entrada3 :: "'c"

term "\<lambda> s. s (x::string) + s y"
term "\<lambda> s. s (x::string) + (f s)"

lemma "OP (\<lambda> (s::'a \<Rightarrow> 'b::plus). s x + s y) = (\<lambda> (s::'a \<Rightarrow> 'b::plus). s x + (f s))"
proof(rule ext)
oops

definition vdiff ::"string \<Rightarrow> string" ("\<partial> _" [55] 70) where
"(\<partial> x) = ''d[''@x@'']''"

(*primrec subst :: "string \<Rightarrow> ('a::ring) \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> ('a store \<Rightarrow> 'a)" where
"subst x t (\<lambda> s. c) = (\<lambda> s. c)"|
"subst x t (\<lambda> s. s x) = (\<lambda> s. t)"|
"subst x t (\<lambda> s. f s + g s) = (\<lambda> s. (subst x t f) s + (subst x t g) s)"|
"subst x t (\<lambda> s. f s * g s) = (\<lambda> s. (subst x t f) s * (subst x t g) s)"*)


term "\<lambda> (s::'a \<Rightarrow> 'b::ring). s x"
term "\<lambda> (s::'a \<Rightarrow> 'b::ring). (cnstnt::('b::ring))"
term "\<lambda> (s::'a \<Rightarrow> 'b::ring). (f::('a \<Rightarrow> 'b) \<Rightarrow> 'b) s + (g::('a \<Rightarrow> 'b) \<Rightarrow> 'b) s"
term "\<lambda> (s::'a \<Rightarrow> 'b::ring). (f::('a \<Rightarrow> 'b) \<Rightarrow> 'b) s * (g::('a \<Rightarrow> 'b) \<Rightarrow> 'b) s"
typ "'a::ab_semigroup_add"

(**************************************************************************************************)
definition scale :: "nat \<Rightarrow> ('a::monoid_add) \<Rightarrow> 'a" (infixr "\<star>" 68) where
  "n \<star> a = (((+) a) ^^ n) 0"
  
class differential_ring = ring +
fixes D::"'a \<Rightarrow> 'a"
assumes dplus[simp]:"D (x + y) = (D x) + (D y)"
    and leibniz:"D (x * y) = (D x) * y + x * (D y)"
    and [simp]:"D 0 = 0"
begin

lemma "D (x - y) = (D x) - (D y)"
by (metis local.add_diff_cancel local.diff_add_cancel local.dplus)

lemma "D (n \<star> x) = n \<star> D x"
by(induct n, simp_all add: scale_def)

end
(**************************************************************************************************)

(* So the problem here is that we need to define the following operation over real-store-predicates:
  D(f=g) \<equiv> D(f)=D(g)      D(f<g)\<equiv>D(f)\<le>D(g)      D(f\<le>g)\<equiv>D(f)\<le>D(g)
  D(\<not>P) \<equiv> D(P)            D(P\<and>Q)\<equiv>D(P)\<and>D(Q)      D(P\<or>Q)\<equiv>D(P)\<and>D(Q)
   So that we have in isabelle the following theorem:
          P,G \<turnstile> Q        G \<turnstile>[x':=f(x)]D(Q)
        ------------------------------------dInv
              P \<turnstile> [x' = f(x) & G]Q

   I have thought of two solutions and a wishful-solution:
    1. Define inductive datatypes that allow me to define my operation on them. Then use them to
    prove the rule, and later on add syntax theorems so that the user does not experience the 
    datatype.
    2. Prove the dInv rule for each one of the possible cases. Then make a general case that 
    invoques all of these rules.
    3. (Wishful) Magically, some Isabelle command/theorem lets me do what I want easily, for example 
    typedef or function, which reduces my problem to just proving properties...

    UPDATE: Here's the situation...
      · Method 3 is ruled out because of the following argument (provided by Andreas Lochbihler). 
      Suppose that you are able to create operators "D" such that "D:(a' \<Rightarrow> bool) \<Rightarrow> (a' \<Rightarrow> bool)" 
      depends on the inductive structure of its argument. Then you could define a D such that 
      D(\<lambda> x. P x) = (\<lambda> x. True) and D(\<lambda> x. P x \<and> True) = (\<lambda> x. False). Notice then that by the 
      "substitution axiom", (\<lambda> x. False) = D(\<lambda> x. True \<and> True) = D(\<lambda> x. True) = (\<lambda> x. True).
      Picking any arbitrary "x::'a", we would have a proof of True = False within Isabelle. =/
      · Method 2 is then the suggested approach. However, as shown in the dInvForVars-lemma (below),
      it requires us to talk about the semantics of differential variables. This in turn requires us
      to expand our domain of work from "string" to "string \<union> string'", or modify our definitions 
      so that "solvesStoreIVP" has a special treatment for the subset "{d@\<alpha>| \<alpha>::string }". However,
      doing any of these will affect "solvesStoreIVP" in a way that we won't be able to generalize
      later to many variables with the approach: 
        "(D[x] = f, D[x]=g with G) = (D[x]=f with G) \<inter> (D[y]=g with G)"
      Moreover, assuming that we can use this approach in a way that it generalizes nicely to many
      variables, we still have to learn how to define "simprocs in Isabelle/ML" so that we can
      automate the tool enough that it competes with KeYmaera X's invariant rules.
      · Finally, method 1 is quickly discarded by Andreas Lochbihler.
*) 

ML {* 2 + 5 *}
ML {* writeln "any string" *}

(* NEW APPROACH: TRY TO IMPLEMENT THE DIFFERENTIATION WITH TYPEDEF's: *)
typedef ccc ="{(\<lambda> (s::real store). c) | c \<in> (UNIV::real set)}" (*morphisms var str*)
apply(rule_tac x="(\<lambda> (s::real store). 0)" in exI)
by auto

typedef vvv ="{(\<lambda> (s::real store). s x) |x. x \<in> (UNIV::string set)}" (*morphisms var str*)
apply(rule_tac x="(\<lambda> (s::real store). s ''x'')" in exI)
  by auto


(*
abbreviation "\<C> t \<equiv> {x \<in> T. t + x \<in> T}"

lemma is_interval_sub_translation:
shows "is_interval (\<C> t)" 
unfolding is_interval_def apply(clarify, safe, simp_all)
by (meson interval_time is_interval_1 add_left_mono)+

lemma is_compact_sub_translation:
shows "compact (\<C> t)"
proof-
obtain t0 t1 where "T = {t0 .. t1}"
using min_max_T by blast
have "\<C> t = {x. t + x \<in> T} \<inter> T" by auto
hence *:"\<C> t = {t0 - t .. t1 - t} \<inter> {t0 .. t1}"
using \<open>T = {t0 .. t1}\<close> by(safe, simp_all)
then have "closed (\<C> t)" by simp
thus "compact (\<C> t)" by (simp add: * )
qed

lemma is_sub_translation: "(\<C> t \<times> S) \<subseteq> (T \<times> S)"
apply(rule subsetI) by auto

lemma ubc_sub_translation:"t \<in> T \<Longrightarrow> unique_on_bounded_closed 0 (\<C> t) (\<phi> t s) (\<lambda>t. f) UNIV L"
apply(rule_tac T="T" in unique_on_bounded_closed.unique_on_bounded_closed_on_compact_subset)
using non_empty_domain_ubc flow_is_banach_endo apply blast
apply(simp_all add: init_time flow_is_banach_endo)
unfolding ubc_definitions apply(simp add: is_compact_sub_translation is_interval_sub_translation)
apply(rule_tac x="0" in exI)
using init_time by simp

lemma shifted_flow_solves:"((\<lambda> \<tau>. \<phi> \<tau> s) solves_ode (\<lambda> \<tau>. f))((\<lambda>x. x + t) ` \<C> t) UNIV"
apply(rule_tac S="T" and Y="UNIV" in solves_ode_on_subset)
using flow_solves apply (simp_all add: Groups.add_ac(2) image_def)
by auto

lemma add_flow_solves:"((\<lambda>\<tau>. \<phi> (\<tau> + t) s) solves_ode (\<lambda> t. f))(\<C> t) UNIV"
using shifted_flow_solves unfolding solves_ode_def apply safe
apply(subgoal_tac "((\<lambda>\<tau>. \<phi> \<tau> s) \<circ> (\<lambda>\<tau>. \<tau> + t) has_vderiv_on 
(\<lambda>x. (\<lambda>\<tau>. 1) x *\<^sub>R (\<lambda>t. f (\<phi> t s)) ((\<lambda>\<tau>. \<tau> + t) x))) (\<C> t)", simp add: comp_def)
apply(rule has_vderiv_on_compose, simp)
apply(rule_tac f'1="\<lambda> x. 1 " and g'1="\<lambda> x. 0" in derivative_intros(190))
apply(rule derivative_intros, simp)+
by auto

theorem flow_action2:
assumes "t1 \<in> \<C> t2" and "t2 \<in> T"
shows "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
using assms 
proof-
have g1:"\<phi> (0 + t2) s = \<phi> t2 s" by simp
have g2:"((\<lambda> \<tau>. \<phi> (\<tau> + t2) s) solves_ode (\<lambda> t. f))(\<C> t2) UNIV" 
  using add_flow_solves assms(1) by simp
have h0:"\<phi> t2 s \<in> UNIV" 
  using assms flow_is_banach_endo by simp
hence h1:"\<phi> 0 (\<phi> t2 s) = \<phi> t2 s" 
  using flow_on_init_time by simp
have h2:"((\<lambda> \<tau>. \<phi> \<tau> (\<phi> t2 s)) solves_ode (\<lambda> t. f))(\<C> t2) UNIV"
  apply(rule_tac S="T" and Y="UNIV" in solves_ode_on_subset)
  using h0 flow_solves by auto 
from g1 g2 h1 and h2 have "\<And> t. t \<in> \<C> t2 \<Longrightarrow> \<phi> (t + t2) s = \<phi> t (\<phi> t2 s)"
  using assms unique_on_bounded_closed.unique_solution 
  ubc_sub_translation by blast
thus "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)" 
  using assms(1) by simp
qed*)

end