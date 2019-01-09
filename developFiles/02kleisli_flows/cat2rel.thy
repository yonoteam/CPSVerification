theory cat2rel
imports
  "Abstract_HL"
  "Ordinary_Differential_Equations.Initial_Value_Problem"

begin

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")

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

lemma p2r_IdD:"\<lceil>P\<rceil> = Id \<Longrightarrow> P s"
  by (metis (full_types) UNIV_I impl_prop p2r_subid top_empty_eq)

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

term "the_inv"
term "the_inv_into"

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

named_theorems poly_derivatives "temporal compilation of derivatives for kinematics or polynomials."

lemma vector_derivative_line_at_origin:"((\<cdot>) a has_vector_derivative a) (at x within T)"
by (auto intro: derivative_eq_intros)

lemma [poly_derivatives]:"((\<cdot>) a has_derivative (\<lambda>x. x *\<^sub>R a)) (at x within T)"
using vector_derivative_line_at_origin unfolding has_vector_derivative_def by simp

lemma quadratic_monomial_derivative:
"((\<lambda>t::real. a \<cdot> t\<^sup>2) has_derivative (\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t))) (at x within T)"
apply(rule_tac g'1="\<lambda> t. 2 \<cdot> x \<cdot> t" in derivative_eq_intros(6))
apply(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15))
by (auto intro: derivative_eq_intros) 

lemma quadratic_monomial_derivative2:
"((\<lambda>t::real. a \<cdot> t\<^sup>2 / 2) has_derivative (\<lambda>t. a \<cdot> x \<cdot> t)) (at x within T)"
apply(rule_tac f'1="\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t)" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
using quadratic_monomial_derivative by auto

lemma quadratic_monomial_vderiv[poly_derivatives]:"((\<lambda>t. a \<cdot> t\<^sup>2 / 2) has_vderiv_on (\<cdot>) a) T"
apply(simp add: has_vderiv_on_def has_vector_derivative_def, clarify)
using quadratic_monomial_derivative2 by (simp add: mult_commute_abs)

lemma galilean_position[poly_derivatives]:
"((\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) has_vderiv_on (\<lambda>t. a \<cdot> t + v)) T"
apply(rule_tac f'="\<lambda> x. a \<cdot> x + v" and g'1="\<lambda> x. 0" in derivative_intros(190))
apply(rule_tac f'1="\<lambda> x. a \<cdot> x" and g'1="\<lambda> x. v" in derivative_intros(190))
using poly_derivatives(2) by(auto intro: derivative_intros)

lemma [poly_derivatives]:
"t \<in> T \<Longrightarrow> ((\<lambda>\<tau>. a \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + x) has_derivative (\<lambda>x. x *\<^sub>R (a \<cdot> t + v))) (at t within T)"
using galilean_position unfolding has_vderiv_on_def has_vector_derivative_def by simp

lemma galilean_velocity[poly_derivatives]:"((\<lambda>r. a \<cdot> r + v) has_vderiv_on (\<lambda>t. a)) T"
apply(rule_tac f'1="\<lambda> x. a" and g'1="\<lambda> x. 0" in derivative_intros(190))
unfolding has_vderiv_on_def by(auto intro: derivative_eq_intros)

lemma [poly_derivatives]:
"((\<lambda>t. v \<cdot> t - a \<cdot> t\<^sup>2 / 2 + x) has_vderiv_on (\<lambda>x. v - a \<cdot> x)) {0..t}"
apply(subgoal_tac "((\<lambda>t. - a \<cdot> t\<^sup>2 / 2 + v \<cdot> t  +x) has_vderiv_on (\<lambda>x. - a \<cdot> x + v)) {0..t}", simp)
by(rule poly_derivatives)

lemma [poly_derivatives]:
"((\<lambda>t. v - a \<cdot> t) has_vderiv_on (\<lambda>x. - a)) {0..t}"
apply(subgoal_tac "((\<lambda>t. - a \<cdot> t + v) has_vderiv_on (\<lambda>x. - a)) {0..t}", simp)
by(rule poly_derivatives)

abbreviation "orbital f T S t0 x0 \<equiv> {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> (\<forall> r \<in> {t0--t}. G (x r)) \<and> x0 \<in> S}"

(**************************************************************************************************)
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
  assumes "s \<in> S" and "(x solves_ode f)T S" and "x t0 = s" and "t \<in> T"
  shows "x t = phi t s"
  using unique_solution fixed_point_solves assms by blast

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

(**************************************************************************************************)
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

(**************************************************************************************************)
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

(**************************************************************************************************)
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

(**************************************************************************************************)
lemma case_of_fst[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> fst) x)"
  by auto

lemma case_of_snd[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f x) = (\<lambda> x. (f \<circ> snd) x)"
  by auto

(*declare [[show_types, show_sorts]]*)

thm L2_set_def norm_vec_def component_le_norm_cart norm_bound_component_le_cart
thm matrix_vector_mult_def matrix_mult_dot matrix_mult_sum vector_componentwise basis_expansion
thm card_eq_sum sum_def real_scaleR_def Connected.bounded_has_Sup sum_norm_allsubsets_bound
thm dist_norm matrix_vector_mult_diff_distrib

lemma norm_scalar_mult: "norm ((c::real) *s x) = \<bar>c\<bar> \<cdot> norm x"
  unfolding norm_vec_def L2_set_def real_norm_def vector_scalar_mult_def apply simp
  apply(subgoal_tac "(\<Sum>i\<in>UNIV. (c \<cdot> x $ i)\<^sup>2) = \<bar>c\<bar>\<^sup>2 \<cdot> (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2) ")
   apply(simp add: real_sqrt_mult)
  apply(simp add: sum_distrib_left)
  by (meson power_mult_distrib)

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis basic_trans_rules(23) monoid_mult_class.power2_eq_square more_arith_simps(6) 
      mult_left_mono real_sqrt_le_iff' zero_le_one)

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  by (metis (full_types) abs_of_nat le_square of_nat_mono of_nat_mult real_sqrt_abs2 real_sqrt_le_iff)

lemma norm_diff_vector_mult:
  fixes A::"('a::{real_normed_vector, ring_1})^'n^'m"
  shows "norm (A *v x - A *v y) = norm (A *v (x - y))"
  by(subst matrix_vector_mult_diff_distrib, simp)

lemma sgn_is_unit_vec:"sgn x = 1 / norm x *s x"
  unfolding sgn_vec_def scaleR_vec_def by(simp add: vector_scalar_mult_def divide_inverse_commute)

lemma squared_norm:"(norm x)\<^sup>2 = (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
  unfolding norm_vec_def L2_set_def by (simp add: sum_nonneg)

lemma norm_sgn_unit:"(x::real^'n) \<noteq> 0 \<Longrightarrow> norm (sgn x) = 1"
proof(subst sgn_is_unit_vec, unfold norm_vec_def L2_set_def, simp add: power_divide)
  assume "x \<noteq> 0"
  have "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2 / (norm x)\<^sup>2) = 1 / (norm x)\<^sup>2 \<cdot> (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
    by (simp add: sum_divide_distrib)
  also have "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2) = (norm x)\<^sup>2" by(subst squared_norm, simp)
  ultimately show "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2 / (sqrt (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2))\<^sup>2) = 1"
    using \<open>x \<noteq> 0\<close> by simp
qed

lemma norm_matrix_sgn:"norm (A *v (x::real^'n)) = norm (A *v (sgn x)) \<cdot> norm x"
  unfolding sgn_is_unit_vec vector_scalar_commute norm_scalar_mult by simp

lemma "(\<Sum>j\<in>UNIV. axis i 1 $ j \<cdot> f j) = f i"
  unfolding axis_def apply simp
  apply(subgoal_tac "axis i 1 $ i = 1") ñ
  oops


abbreviation "norm\<^sub>S (A::real^'n^'m) \<equiv> Sup {norm (A *v x) | x. norm x = 1}"

lemma unit_norms_bound:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "norm x = 1 \<Longrightarrow> norm (A *v x) \<le> norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)"
proof-
  assume "norm x = 1"
  from this have "\<And> j. \<bar>x $ j\<bar> \<le> 1"
    by (metis component_le_norm_cart)
  then have "\<And>i j. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar> \<le> \<bar>A $ i $ j\<bar> \<cdot> 1"
    using mult_left_mono by (simp add: mult_left_le) 
  from this have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar>)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    by (simp add: power_mono sum_mono sum_nonneg)
  also have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j \<cdot> x $ j\<bar>)\<^sup>2"
    using abs_le_square_iff by force 
  moreover have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j \<cdot> x $ j\<bar>)\<^sup>2 = (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar>)\<^sup>2"
    by (simp add: abs_mult)
  ultimately have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    using order_trans by fastforce
  hence "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2) \<le> (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2)"
    by(simp add: sum_mono)
  then have "(sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2)) \<le> (sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2))"
    using real_sqrt_le_mono by blast
  thus "norm (A *v x) \<le> norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)"
    by(simp add: norm_vec_def L2_set_def matrix_vector_mult_def)
qed

lemma unit_norms_exists:
  fixes A::"real^('n::finite)^('m::finite)"
  shows bounded:"bounded {norm (A *v x) | x. norm x = 1}"
    and bdd_above:"bdd_above {norm (A *v x) | x. norm x = 1}"
    and non_empty:"{norm (A *v x) | x. norm x = 1} \<noteq> {}" (is "?U \<noteq> {}")
proof-
  show "bounded ?U"
    apply(unfold bounded_def,rule_tac x="0" in exI, simp add: dist_real_def)
    apply(rule_tac x="norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)" in exI, clarsimp)
    using unit_norms_bound by blast
next
  show "bdd_above ?U"
    apply(unfold bdd_above_def, rule_tac x="norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)" in exI, clarsimp)
    using unit_norms_bound by blast
next
  have "\<And>k::'n. norm (axis k (1::real)) = 1"
    using norm_axis_1 by blast
  hence "\<And>k::'n. norm ((A::real^('n::finite)^'m) *v (axis k (1::real))) \<in> ?U"
    by blast
  thus "?U \<noteq> {}" by blast
qed

lemma unit_norms: "norm x = 1 \<Longrightarrow> norm (A *v x) \<le> norm\<^sub>S A"
  using cSup_upper mem_Collect_eq unit_norms_exists(2) by (metis (mono_tags, lifting)) 

lemma unit_norms_ge_0:"0 \<le> norm\<^sub>S A"
  using ex_norm_eq_1 norm_ge_zero unit_norms basic_trans_rules(23) by blast

lemma norm_sgn_le_norms:"norm (A *v sgn x) \<le> norm\<^sub>S A"
  apply(cases "x=0")
  using sgn_zero unit_norms_ge_0 apply force
  using norm_sgn_unit unit_norms by blast

abbreviation "entries (A::real^'n^'m) \<equiv> {A $ i $ j | i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}"
abbreviation "maxAbs (A::real^'n^'m) \<equiv> Max (abs ` (entries A))"

lemma maxAbs_def:"maxAbs (A::real^'n^'m) = Max { \<bar>A $ i $ j\<bar> |i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}"
  apply(simp add: image_def, rule arg_cong[of _ _ Max])
  by auto

lemma finite_matrix_abs:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "finite {\<bar>A $ i $ j\<bar> |i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}" (is "finite ?X")
proof-
  {fix i::'m
    have "finite {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)}" 
      using finite_Atleast_Atmost_nat by fastforce}
  hence "\<forall> i::'m. finite {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)}" by blast
  then have "finite (\<Union>i\<in>UNIV. {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)})" (is "finite ?Y")
    using finite_class.finite_UNIV by blast
  also have "?X \<subseteq> ?Y" by auto
  ultimately show ?thesis using finite_subset by blast
qed

lemma maxAbs_ge_0:"maxAbs A \<ge> 0"
proof-
  have "\<And> i j. \<bar>A $ i $ j\<bar> \<ge> 0" by simp
  also have "\<And> i j. maxAbs A \<ge> \<bar>A $ i $ j\<bar>"
    unfolding maxAbs_def using finite_matrix_abs Max_ge maxAbs_def by blast
  finally show "0 \<le> maxAbs A" .
qed

lemma norms_le_dims_maxAbs:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "norm\<^sub>S A \<le> real CARD('n) \<cdot> real CARD('m) \<cdot>(maxAbs A)" (is "norm\<^sub>S A \<le>?n \<cdot> ?m \<cdot> (maxAbs A)")
proof-
  {fix x::"(real, 'n) vec" assume "norm x = 1"
    hence comp_le_1:"\<forall> i::'n. \<bar>x $ i\<bar> \<le> 1"
      by (simp add: norm_bound_component_le_cart)
    have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)"
      using matrix_mult_sum by blast
    hence "norm (A *v x) \<le> (\<Sum>(i::'n)\<in>UNIV. norm ( x $ i *s column i A))"
      by (simp add: sum_norm_le)
    also have "... = (\<Sum>(i::'n)\<in>UNIV. \<bar>x $ i\<bar> \<cdot> norm (column i A))"
      by (simp add: norm_scalar_mult) 
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. norm (column i A))"
      by (metis (no_types, lifting) Groups.mult_ac(2) comp_le_1 mult_left_le norm_ge_zero sum_mono)
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. ?m \<cdot> maxAbs A)"
    proof(unfold norm_vec_def L2_set_def real_norm_def)
      have "\<And>i j. \<bar>column i A $ j\<bar> \<le> maxAbs A"
        using finite_matrix_abs Max_ge unfolding column_def maxAbs_def by(simp, blast)
      hence "\<And>i j. \<bar>column i A $ j\<bar>\<^sup>2 \<le> (maxAbs A)\<^sup>2"
        by (metis (no_types, lifting) One_nat_def abs_ge_zero numerals(2) order_trans_rules(23) 
            power2_abs power2_le_iff_abs_le)
      then have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> (\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2)"
        by (meson sum_mono)
      also have "(\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2) = ?m \<cdot> (maxAbs A)\<^sup>2" by simp
      ultimately have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> ?m \<cdot> (maxAbs A)\<^sup>2" by force
      hence "\<And>i. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> sqrt (?m \<cdot> (maxAbs A)\<^sup>2)"
        by(simp add: real_sqrt_le_mono)
      also have "sqrt (?m \<cdot> (maxAbs A)\<^sup>2) \<le> sqrt ?m \<cdot> maxAbs A"
        using maxAbs_ge_0 real_sqrt_mult by auto
      also have "... \<le> ?m \<cdot> maxAbs A"
        using sqrt_real_nat_le maxAbs_ge_0 mult_right_mono by blast  
      finally show "(\<Sum>i\<in>UNIV. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2)) \<le> (\<Sum>(i::'n)\<in>UNIV. ?m \<cdot> maxAbs A)"
        by (meson sum_mono)
    qed
    also have "(\<Sum>(i::'n)\<in>UNIV. (maxAbs A)) = ?n \<cdot> (maxAbs A)"
      using sum_constant_scale by auto
    ultimately have "norm (A *v x) \<le> ?n \<cdot> ?m \<cdot> (maxAbs A)" by simp}
  from this show ?thesis 
    using unit_norms_exists[of A] Connected.bounded_has_Sup(2) by blast
qed

lemma matrix_lipschitz_constant:
  fixes A::"real^('n::finite)^'n"
  shows "dist (A *v x) (A *v y) \<le> (real CARD('n))\<^sup>2 \<cdot> maxAbs A \<cdot> dist x y"
  unfolding dist_norm norm_diff_vector_mult proof(subst norm_matrix_sgn)
  have "norm\<^sub>S A \<le> maxAbs A \<cdot> (real CARD('n) \<cdot> real CARD('n))"
    by (metis (no_types) Groups.mult_ac(2) norms_le_dims_maxAbs)
  then have "norm\<^sub>S A \<cdot> norm (x - y) \<le> (real (card (UNIV::'n set)))\<^sup>2 \<cdot> maxAbs A \<cdot> norm (x - y)"
    by (simp add: cross3_simps(11) mult_left_mono semiring_normalization_rules(29))
  also have "norm (A *v sgn (x - y)) \<cdot> norm (x - y) \<le> norm\<^sub>S A \<cdot> norm (x - y)"
    by (simp add: norm_sgn_le_norms cross3_simps(11) mult_left_mono) 
  ultimately show "norm (A *v sgn (x - y)) \<cdot> norm (x - y) \<le> (real CARD('n))\<^sup>2 \<cdot> maxAbs A \<cdot> norm (x - y)"
    using order_trans_rules(23) by blast
qed

lemma picard_ivp_linear_system:
  fixes A::"real^('n::finite)^'n" 
  assumes "0 < ((real CARD('n))\<^sup>2 \<cdot> (maxAbs A))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_ivp (\<lambda> t s. A *v s) {0..t} UNIV ?L 0"
  apply unfold_locales
  subgoal by(simp, metis continuous_on_compose2 continuous_on_cong continuous_on_id 
        continuous_on_snd matrix_vector_mult_linear_continuous_on top_greatest) 
  subgoal using matrix_lipschitz_constant maxAbs_ge_0 zero_compare_simps(4,12) 
    unfolding lipschitz_on_def by blast
  apply(simp_all add: assms)
  subgoal for r s apply(subgoal_tac "\<bar>r - s\<bar> < 1/((real CARD('n))\<^sup>2 \<cdot> maxAbs A)")
     apply(subst (asm) pos_less_divide_eq[of ?L "\<bar>r - s\<bar>" 1])
    using assms by auto
  done

(**************************************************************************************************)
(******************************************** H E R E *********************************************)
instance vec:: (real_normed_vector,finite) real_normed_vector
by standard

\<comment> \<open>Generating a finite type...\<close>
(*declare [[show_sorts, show_types]]
term "x::4" term "x::5" term "x::10" term "x::1000" term "(x::0) = x :: 5"*)

lemma exhaust5:
  fixes x::5
  shows "x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or> x=5"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 5" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4" by arith
  then show ?case by auto
qed

typedef three ="{m::nat. m < 3}"
  apply(rule_tac x="0" in exI)
  by simp

typedef four ="{m::nat. m < 4}"
  apply(rule_tac x="0" in exI)
  by simp

lemma card_of_three:"card {m::nat. m < 3} = 3"
  by auto

lemma card_of_four:"card {m::nat. m < 4} = 4"
  by auto

lemma CARD_of_three:"CARD(three) = 3"
  using type_definition.card type_definition_three by fastforce

lemma "CARD(three) = CARD(3)" (* there is already a 3-type *)
  oops
  term "CARD(three)"
  typ 3
  typ "'a^'n"
  term "tendsto "

lemma CARD_of_four:"CARD(four) = 4"
  using type_definition.card type_definition_four by fastforce

instance three::finite
  apply(standard, subst bij_betw_finite[of Rep_three UNIV "{m::nat. m < 3}"])
   apply(rule bij_betwI')
     apply (simp add: Rep_three_inject)
  using Rep_three apply blast
   apply (metis Abs_three_inverse UNIV_I)
  by simp

instance four::finite
  apply(standard, subst bij_betw_finite[of Rep_four UNIV "{m::nat. m < 4}"])
   apply(rule bij_betwI')
     apply (simp add: Rep_four_inject)
  using Rep_four apply blast
   apply (metis Abs_four_inverse UNIV_I)
  by simp

lemma three_univD:"(UNIV::three set) = {Abs_three 0, Abs_three 1, Abs_three 2}"
proof-
  have "(UNIV::three set) = Abs_three ` {m::nat. m < 3}"
    apply auto by (metis Rep_three Rep_three_inverse image_iff)
  also have "{m::nat. m < 3} = {0, 1, 2}" by auto
  ultimately show ?thesis by auto
qed

lemma four_univD:"(UNIV::four set) = {Abs_four 0, Abs_four 1, Abs_four 2, Abs_four 3}"
proof-
  have "(UNIV::four set) = Abs_four ` {m::nat. m < 4}"
    apply auto by (metis Rep_four Rep_four_inverse image_iff)
  also have "{m::nat. m < 4} = {0, 1, 2,3}" by auto
  ultimately show ?thesis by auto
qed

lemma three_exhaust:"\<forall> x::three. x = Abs_three 0 \<or> x = Abs_three 1 \<or> x = Abs_three 2"
  using three_univD by auto

lemma four_exhaust:"\<forall> x::four. x = Abs_four 0 \<or> x = Abs_four 1 \<or> x = Abs_four 2 \<or> x = Abs_four 3"
  using four_univD by auto

abbreviation "free_fall_kinematics (s::real^three) \<equiv> (\<chi> i. if i=(Abs_three 0) then s $ (Abs_three 1) else 
if i=(Abs_three 1) then s $ (Abs_three 2) else 0)"

abbreviation "free_fall_flow t s \<equiv> 
(\<chi> i. if i=(Abs_three 0) then s $ (Abs_three 2) \<cdot> t ^ 2/2 + s $ (Abs_three 1) \<cdot> t + s $ (Abs_three 0)
else if i=(Abs_three 1) then s $ (Abs_three 2) \<cdot> t + s $ (Abs_three 1) else s $ (Abs_three 2))"

lemma "axis (1::3) (1::real) = (\<chi> j. if j= 0 then 0 else if j = 1 then 1 else 0)"
  unfolding axis_def by(rule Cart_lambda_cong, simp)

abbreviation "K \<equiv> (\<chi> i. if i= (0::3) then axis (1::3) (1::real)
else if i= 1 then axis (2::3) (1::real)
else 0)"

abbreviation "flow_for_K t s \<equiv> (\<chi> i. if i= (0::3) then s $ 2 \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0
else if i=1 then s $ 2 \<cdot> t + s $ 1 else s $ 2)"

lemma entries_K:"entries K = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma "0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> picard_ivp (\<lambda> t s. K *v s) {0..t} UNIV ((real CARD(3))\<^sup>2 \<cdot> maxAbs K) 0"
  apply(rule picard_ivp_linear_system)
  unfolding entries_K by auto

lemma bounded_linear_free_fall_kinematics:"bounded_linear free_fall_kinematics"
  apply unfold_locales
    apply(simp_all add: plus_vec_def scaleR_vec_def ext norm_vec_def L2_set_def)
  apply(rule_tac x="1" in exI, clarsimp)
  apply(subst three_univD, subst three_univD)
  by(auto simp: Abs_three_inject)

lemma free_fall_kinematics_continuous_on: "continuous_on X free_fall_kinematics"
  using bounded_linear_free_fall_kinematics linear_continuous_on by blast

lemma free_fall_kinematics_is_picard_ivp:"0 \<le> t \<Longrightarrow> t < 1 \<Longrightarrow> 
picard_ivp (\<lambda> t s. free_fall_kinematics s) {0..t} UNIV 1 0"
  unfolding picard_ivp_def picard_ivp_axioms_def ubc_definitions
  apply(simp_all add: nonempty_set_def lipschitz_on_def, safe)
     apply(rule continuous_on_compose2[of UNIV _ "{0..t} \<times> UNIV" snd])
  apply(simp_all add: free_fall_kinematics_continuous_on continuous_on_snd)
   apply(simp add: dist_vec_def L2_set_def dist_real_def)
   apply(subst three_univD, subst three_univD)
  by(simp add: Abs_three_inject)
  (*by(subst power2_commute, simp)*)

thm bij_betwI  bij_betwI' bij_betw_finite
thm Rep_four  Rep_four_inject Rep_four_cases Rep_four_inverse
thm           Abs_four_inject Abs_four_cases Abs_four_inverse
thm vec_nth   vec_nth_inject vec_nth_cases vec_nth_inverse 
thm           vec_lambda_inject vec_lambda_cases vec_lambda_inverse

lemma componentwise_solves:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)" and \<phi>::"real \<Rightarrow> ('a^'n)"
  assumes "\<forall> i::'n. ((\<lambda> t. (\<phi> t) $ i) solves_ode (\<lambda> t s. (f (\<phi> t)) $ i)) {0..t} UNIV"
  shows "(\<phi> solves_ode (\<lambda> t. f)) {0..t} UNIV"
  using assms unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def has_derivative_def
  apply safe defer
    apply(rule Finite_Cartesian_Product.vec_tendstoI)
  by(auto simp: bounded_linear_def bounded_linear_axioms_def)

lemma free_fall_flow_solves_free_fall_kinematics:
  "((\<lambda> \<tau>. free_fall_flow \<tau> s) solves_ode (\<lambda>t s. free_fall_kinematics s)) {0..t} UNIV"
  apply (rule componentwise_solves)
  apply(simp add: solves_ode_def has_vderiv_on_def)
  apply(auto simp: Abs_three_inject has_vector_derivative_def)
  using poly_derivatives(3, 5) unfolding has_vderiv_on_def has_vector_derivative_def by auto

lemma UNIV_3:"(UNIV::3 set) = {0, 1, 2}"
  apply safe using exhaust_3 three_eq_zero by(blast, auto)

lemma sum_UNIV_3[simp]:"(\<Sum>j\<in>(UNIV::3 set). axis i 1 $ j \<cdot> f j) = (f::3 \<Rightarrow> real) i"
  unfolding axis_def UNIV_3 apply simp
  using exhaust_3 by force

lemma flow_for_K_solves_K:
  "((\<lambda> \<tau>. flow_for_K \<tau> s) solves_ode (\<lambda>t s.  K *v s)) {0..t} UNIV"
  apply (rule componentwise_solves)
  apply(simp add: solves_ode_def)
  apply(auto simp: matrix_vector_mult_def)
  using poly_derivatives(3, 5) apply auto
  unfolding has_vderiv_on_def has_vector_derivative_def by auto

lemma free_fall_flow_is_local_flow:
"0 \<le> t \<Longrightarrow> t < 1 \<Longrightarrow> local_flow (\<lambda> s. free_fall_kinematics s) UNIV {0..t} 1 (\<lambda> t x. free_fall_flow t x)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using free_fall_kinematics_is_picard_ivp apply simp
  subgoal for x _ \<tau>
    apply(rule picard_ivp.unique_solution [of "\<lambda> t s. free_fall_kinematics s" "{0..t}" 
          UNIV 1 0 "(\<lambda> t. free_fall_flow t (x 0))" "x 0"])
    using free_fall_kinematics_is_picard_ivp apply simp
         apply(rule free_fall_flow_solves_free_fall_kinematics)
        apply(simp_all add: vec_eq_iff Abs_three_inject)
    using three_univD by fastforce
  done

corollary free_fall_flow_DS:
  assumes "0 \<le> t" and "t < 1"
  shows " wp {[x\<acute>=\<lambda>s. free_fall_kinematics s]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (free_fall_flow r x)) \<longrightarrow> Q (free_fall_flow \<tau> x)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda>s. free_fall_kinematics s" _ _ 1 "(\<lambda> t x. free_fall_flow t x)"])
  using free_fall_flow_is_local_flow and assms by (blast, simp)

term "{[x\<acute>= (f::real^four \<Rightarrow> real^four)]T S @ t0 & G}"
term "{[x\<acute>= (f::real^three \<Rightarrow> real^three)]T S @ t0 & G}"
term "{(s, (\<chi> i. ((($) s)(x := expr)) i))| s. True}" (* assignment *)

lemma single_evolution_ball:
  assumes "0 \<le> t" and "t < 1" 
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ (Abs_three 0) \<and> s $ (Abs_three 0) = H \<and> s $ (Abs_three 1) = 0 \<and> 0 > s $ (Abs_three 2)\<rceil> 
\<subseteq> wp ({[x\<acute>=\<lambda>s. free_fall_kinematics s]{0..t} UNIV @ 0 & (\<lambda> s. s $ (Abs_three 0) \<ge> 0)})
     \<lceil>\<lambda>s. 0 \<le> s $ (Abs_three 0) \<and> s $ (Abs_three 0) \<le> H\<rceil>"
  apply(subst free_fall_flow_DS)
  by(simp_all add: assms mult_nonneg_nonpos2)

lemma bouncing_ball:
  fixes  x v g ::three
  (* assumes "x \<noteq> v" and "v \<noteq> g" and "x \<noteq> g" *)
  (* assumes "x = Abs_three 0" and "v = Abs_three 1" and "g = Abs_three 2" *)
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ x \<and> s $ x = H \<and> s $ v = 0 \<and> 0 < s $ g\<rceil> \<subseteq> wp 
  (({[x\<acute>=\<lambda>s. (\<chi> i. if i=x then s $ v else 
                (if i=v then - s $ g else 0))]{0..t} UNIV @ 0 & (\<lambda> s. s $ x \<ge> 0)};
  (IF (\<lambda> s. s $ x = 0) 
   THEN ({(s, (\<chi> i. ((($) s)(v := (- s $ v))) i))| s. True}) 
   ELSE ({(s, (\<chi> i. ((($) s)(v := s $ v)) i))| s. True}) FI)
  )\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ x \<and> s $ x \<le> H\<rceil>"
  apply simp
  oops


(**************************************************************************************************)

theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding rel_antidomain_kleene_algebra.fbox_def rel_ad_def f2r_def
  apply(simp add: relcomp.simps p2r_def)
  apply(rule subset_antisym)
  by fastforce+

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
  then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode (\<lambda>t. f)) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
    unfolding f2r_def by blast
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using assms(1) \<open>t \<in> T\<close> picard_ivp.subsegment picard_ivp.init_time by blast
  ultimately have "\<forall> r\<in>{t0--t}. (a, x r) \<in> {[x\<acute>=f]T S @ t0 & G}"
    using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_IdD assms(2) by blast
  thus "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}"
    using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> f2r_def x_solves by fastforce 
next
  fix a b assume "(a, b) \<in> {[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}" 
  then show "(a, b) \<in> {[x\<acute>=f]T S @ t0 & G}"
    unfolding f2r_def by blast
qed

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

lemma closed_segment_mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "(\<And>r. r\<in>{a--b} \<Longrightarrow> (f has_derivative f' r) (at r within {a--b}))" and "a \<le> b"
  shows "\<exists>r\<in>{a--b}. f b - f a = f' r (b - a)"
  using assms closed_segment_eq_real_ivl and mvt_very_simple by auto

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

term "(x has_vector_derivative f)"
term "frechet_derivative"

lemma dInvariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode (\<lambda> t. f))T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<subseteq> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
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

lemma dInvariant_above_0:
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

lemma dInvariant_meet:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>"
  using assms apply(subst (asm) wp_rel, subst (asm) wp_rel)
  apply(subst wp_rel, simp add: p2r_def)
  by blast

lemma dInvariant_join:
  assumes "\<lceil>I1\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<subseteq> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>"
  using assms apply(subst (asm) wp_rel, subst (asm) wp_rel)
  apply(subst wp_rel, simp add: p2r_def)
  by blast

end