theory hs_prelims
  imports "Ordinary_Differential_Equations.Initial_Value_Problem"

begin

chapter\<open> Hybrid Systems Preliminaries \<close>

text\<open> This chapter contains preliminary lemmas for verification of Hybrid Systems.\<close>

section\<open> Miscellaneous \<close>

subsection\<open> Functions \<close>

lemma case_of_fst[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> fst) x)"
  by auto

lemma case_of_snd[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f x) = (\<lambda> x. (f \<circ> snd) x)"
  by auto

subsection\<open> Orders \<close>

lemma cSup_eq_linorder:
  fixes c::"'a::conditionally_complete_linorder"
  assumes "X \<noteq> {}" and "\<forall>x \<in> X. x \<le> c" 
    and "bdd_above X" and "\<forall>y<c. \<exists>x\<in>X. y < x"
  shows "Sup X = c"
  apply(rule order_antisym)
  using assms apply(simp add: cSup_least)
  using assms by(subst le_cSup_iff)

lemma cSup_eq:
  fixes c::"'a::conditionally_complete_lattice"
  assumes "\<forall>x \<in> X. x \<le> c" and "\<exists>x \<in> X. c \<le> x"
  shows "Sup X = c"
  apply(rule order_antisym)
   apply(rule cSup_least)
  using assms apply(blast, blast)
  using assms(2) apply safe
  apply(subgoal_tac "x \<le> Sup X", simp)
  by (metis assms(1) cSup_eq_maximum eq_iff)

lemma bdd_above_ltimes:
  fixes c::"'a::linordered_ring_strict"
  assumes "c \<ge> 0" and "bdd_above X"
  shows "bdd_above {c * x |x. x \<in> X}"
  using assms unfolding bdd_above_def apply clarsimp
  apply(rule_tac x="c * M" in exI, clarsimp)
  using mult_left_mono by blast

lemma finite_nat_minimal_witness:
  fixes P :: "('a::finite) \<Rightarrow> nat \<Rightarrow> bool"
  assumes "\<forall>i. \<exists>N::nat. \<forall>n \<ge> N. P i n"
  shows "\<exists>N. \<forall>i. \<forall>n \<ge> N. P i n" 
proof-
  let "?bound i" = "(LEAST N. \<forall>n \<ge> N. P i n)"
  let ?N = "Max {?bound i |i. i \<in> UNIV}"
  {fix n::nat and i::'a 
    obtain M where "\<forall>n \<ge> M. P i n" 
      using assms by blast
    hence obs: "\<forall> m \<ge> ?bound i. P i m"
      using LeastI[of "\<lambda>N. \<forall>n \<ge> N. P i n"] by blast
    assume "n \<ge> ?N" 
    have "finite {?bound i |i. i \<in> UNIV}"
      using finite_Atleast_Atmost_nat by fastforce
    hence "?N \<ge> ?bound i"
      using Max_ge by blast
    hence "n \<ge> ?bound i" 
      using \<open>n \<ge> ?N\<close> by linarith
    hence "P i n" 
      using obs by blast}
  thus "\<exists>N. \<forall>i n. N \<le> n \<longrightarrow> P i n" 
    by blast
qed

subsection\<open> Real Numbers \<close>

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis basic_trans_rules(23) monoid_mult_class.power2_eq_square more_arith_simps(6) 
      mult_left_mono real_sqrt_le_iff' zero_le_one)

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  by (metis (full_types) abs_of_nat le_square of_nat_mono of_nat_mult real_sqrt_abs2 real_sqrt_le_iff)

lemma sq_le_cancel:
  shows "(a::real) \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a^2 \<le> b * a \<Longrightarrow> a \<le> b"
  and "(a::real) \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> a^2 \<le> a * b \<Longrightarrow> a \<le> b"
   apply(metis less_eq_real_def mult.commute mult_le_cancel_left semiring_normalization_rules(29))
  by(metis less_eq_real_def mult_le_cancel_left semiring_normalization_rules(29))

named_theorems trig_simps "simplification rules for trigonometric identities"

lemmas trig_identities = sin_squared_eq[THEN sym] cos_squared_eq[symmetric] cos_diff[symmetric] cos_double

declare sin_minus [trig_simps]
    and cos_minus [trig_simps]
    and trig_identities(1,2) [trig_simps]
    and sin_cos_squared_add [trig_simps]
    and sin_cos_squared_add2 [trig_simps]
    and sin_cos_squared_add3 [trig_simps]
    and trig_identities(3) [trig_simps]

lemma sin_cos_squared_add4 [trig_simps]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "x * (sin t)\<^sup>2 + x * (cos t)\<^sup>2 = x"
  by (metis mult.right_neutral semiring_normalization_rules(34) sin_cos_squared_add)

lemma [trig_simps, simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"  
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq) 
qed

thm trig_simps

section\<open> Calculus \<close>

subsection \<open> Single variable Derivatives \<close>

notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
notation has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)
notation norm ("(1\<parallel>_\<parallel>)" [65] 61)

lemma closed_segment_mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "(\<And>r. r\<in>{a--b} \<Longrightarrow> (D f \<mapsto> (f' r) (at r within {a--b})))" and "a \<le> b"
  shows "\<exists>r\<in>{a--b}. f b - f a = f' r (b - a)"
  using assms closed_segment_eq_real_ivl mvt_very_simple by auto

lemma exp_scaleR_has_derivative_right[derivative_intros]: (* by Fabian Immler *)
  fixes f::"real \<Rightarrow> real"
  assumes "D f \<mapsto> f' at x within s" and "(\<lambda>h. f' h *\<^sub>R (exp (f x *\<^sub>R A) * A)) = g'"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) \<mapsto> g' at x within s"
proof -
  from assms have "bounded_linear f'" by auto
  with real_bounded_linear obtain m where f': "f' = (\<lambda>h. h * m)" by blast
  show ?thesis
    using vector_diff_chain_within[OF _ exp_scaleR_has_vector_derivative_right, of f m x s A] assms f'
    by (auto simp: has_vector_derivative_def o_def)
qed

named_theorems poly_derivatives "compilation of derivatives for kinematics and polynomials."

declare has_vderiv_on_const [poly_derivatives]

lemma has_vector_derivative_mult_const: "((*) a has_vector_derivative a) (at x within T)"
  by (auto intro: derivative_eq_intros)

lemma has_derivative_mult_const: "D (*) a \<mapsto> (\<lambda>x. x *\<^sub>R a) at x within T"
  using has_vector_derivative_mult_const unfolding has_vector_derivative_def by simp

lemma has_derivative_quadratic_monomial:
  fixes a :: real
  shows "D (\<lambda>t. a * t\<^sup>2) \<mapsto> (\<lambda>t. a * (2 * x * t)) at x within T"
  apply(rule_tac g'1="\<lambda> t. 2 * x * t" in derivative_eq_intros(6))
   apply(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15))
  by (auto intro: derivative_eq_intros) 

lemma has_derivative_quadratic_monomial_halfed: 
  fixes a :: real
  shows "D (\<lambda>t. a * t\<^sup>2 / 2) \<mapsto> (*) (a * x) at x within T"
  apply(rule_tac f'1="\<lambda>t. a * (2 * x * t)" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
  using has_derivative_quadratic_monomial by auto

lemma [poly_derivatives]: "D (\<lambda>t. a * t\<^sup>2 / 2) = (*) a on T"
  apply(simp add: has_vderiv_on_def has_vector_derivative_def, clarify)
  using has_derivative_quadratic_monomial_halfed by (simp add: mult_commute_abs)

lemma [poly_derivatives]: "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  apply(rule_tac f'="\<lambda> x. a * x + v" and g'1="\<lambda> x. 0" in derivative_intros(191))
    apply(rule_tac f'1="\<lambda> x. a * x" and g'1="\<lambda> x. v" in derivative_intros(191))
  using poly_derivatives(2) by(auto intro: derivative_intros)

lemma [poly_derivatives]: "D (\<lambda>r. a * r + v) = (\<lambda>t. a) on T"
  apply(rule_tac f'1="\<lambda> x. a" and g'1="\<lambda> x. 0" in derivative_intros(191))
  unfolding has_vderiv_on_def by(auto intro: derivative_eq_intros)

lemma [poly_derivatives]: "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  apply(subgoal_tac "D (\<lambda>t. - a * t\<^sup>2 / 2 + v * t  +x) = (\<lambda>x. - a * x + v) on T", simp)
  by(rule poly_derivatives)

lemma [poly_derivatives]: "D (\<lambda>t. v - a * t) = (\<lambda>x. - a) on T"
  apply(subgoal_tac "D (\<lambda>t. - a * t + v) = (\<lambda>x. - a) on T", simp)
  by(rule poly_derivatives)

declare has_derivative_mult_const [poly_derivatives]
    and has_derivative_quadratic_monomial [poly_derivatives]
    and has_derivative_quadratic_monomial_halfed [poly_derivatives]

lemma [poly_derivatives]: 
  assumes "t \<in> T"
  shows "D (\<lambda>\<tau>. a * \<tau>\<^sup>2 / 2 + v * \<tau> + x) \<mapsto> (\<lambda>x. x *\<^sub>R (a * t + v)) at t within T"
  using assms poly_derivatives unfolding has_vderiv_on_def has_vector_derivative_def by simp

thm poly_derivatives

subsection\<open> Multivariable Derivatives \<close>

lemma eventually_all_finite2:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h:"\<forall>i. eventually (P i) F"
  shows "eventually (\<lambda>x. \<forall>i. P i x) F"
proof(unfold eventually_def)
  let ?F = "Rep_filter F"
  have obs: "\<forall>i. ?F (P i)" 
    using h by auto
  have "?F (\<lambda>x. \<forall>i \<in> UNIV. P i x)"
    apply(rule finite_induct) 
    by(auto intro: eventually_conj simp: obs h)
  thus "?F (\<lambda>x. \<forall>i. P i x)"
    by simp
qed

lemma eventually_all_finite_mono:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h1: "\<forall>i. eventually (P i) F"
      and h2: "\<forall>x. (\<forall>i. (P i x)) \<longrightarrow> Q x"
  shows "eventually Q F"
proof-
  have "eventually (\<lambda>x. \<forall>i. P i x) F"
    using h1 eventually_all_finite2 by blast
  thus "eventually Q F"
    unfolding eventually_def 
    using h2 eventually_mono by auto
qed

lemma frechet_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)" and x::real and T::"real set" 
  defines "x\<^sub>0 \<equiv> netlimit (at x within T)" and "m \<equiv> real CARD('m)"
  assumes "\<forall>i. ((\<lambda>y. (f y $ i - f x\<^sub>0 $ i - (y - x\<^sub>0) *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  shows "((\<lambda>y. (f y - f x\<^sub>0 - (y - x\<^sub>0) *\<^sub>R f' x) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
proof(simp add: tendsto_iff, clarify)
  fix \<epsilon>::real assume "0 < \<epsilon>" 
  let "?\<Delta>" = "\<lambda>y. y - x\<^sub>0" and "?\<Delta>f" = "\<lambda>y. f y - f x\<^sub>0"
  let "?P" = "\<lambda>i e y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>f y $ i - f x\<^sub>0 $ i - ?\<Delta> y *\<^sub>R f' x $ i\<parallel>) < e" 
    and "?Q" = "\<lambda>y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>) < \<epsilon>"
  have "0 < \<epsilon> / sqrt m" 
    using \<open>0 < \<epsilon>\<close> by (auto simp: assms)
  hence "\<forall>i. eventually (\<lambda>y. ?P i (\<epsilon> / sqrt m) y) (at x within T)"
    using assms unfolding tendsto_iff by simp
  thus "eventually ?Q (at x within T)"
  proof(rule eventually_all_finite_mono, simp add: norm_vec_def L2_set_def, clarify)
    fix t::real
    let ?c = "inverse \<bar>t - x\<^sub>0\<bar>" and "?u t" = "\<lambda>i. f t $ i - f x\<^sub>0 $ i - ?\<Delta> t *\<^sub>R f' x $ i"
    assume hyp:"\<forall>i. ?c * (\<parallel>?u t i\<parallel>) < \<epsilon> / sqrt m"
    hence "\<forall>i. (?c *\<^sub>R (\<parallel>?u t i\<parallel>))\<^sup>2 < (\<epsilon> / sqrt m)\<^sup>2" 
      by (simp add: power_strict_mono)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m" 
      by (simp add: power_mult_distrib power_divide assms)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m" 
      by (auto simp: assms)
    also have "({}::'m set) \<noteq> UNIV \<and> finite (UNIV :: 'm set)" 
      by simp
    ultimately have "(\<Sum>i\<in>UNIV. ?c\<^sup>2 * ((\<parallel>?u t i\<parallel>))\<^sup>2) < (\<Sum>(i::'m)\<in>UNIV. \<epsilon>\<^sup>2 / m)"
      by (metis (lifting) sum_strict_mono)
    moreover have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) = (\<Sum>i\<in>UNIV. ?c\<^sup>2 *  (\<parallel>?u t i\<parallel>)\<^sup>2)"
      using sum_distrib_left by blast
    ultimately have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) < \<epsilon>\<^sup>2" 
      by (simp add: assms)
    hence "sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2)) < sqrt (\<epsilon>\<^sup>2)"
      using real_sqrt_less_iff by blast
    also have "... = \<epsilon>" 
      using \<open>0 < \<epsilon>\<close> by auto 
    moreover have "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) = sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2))"
      by (simp add: real_sqrt_mult)   
    ultimately show "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u t i\<parallel>)\<^sup>2) < \<epsilon>" 
      by simp
  qed
qed

lemma has_derivative_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)"
  assumes "\<forall>i. D (\<lambda>t. f t $ i) \<mapsto> (\<lambda> h. h *\<^sub>R f' x $ i) (at x within T)"
  shows "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using assms frechet_vec_lambda[of x T ] unfolding has_derivative_def by auto

lemma has_vderiv_on_vec_lambda:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)"
  assumes "\<forall>i. D (\<lambda>t. x t $ i) = (\<lambda>t. f (x t) $ i) on T"
  shows "D x = (\<lambda>t. f (x t)) on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  by(rule has_derivative_vec_lambda, simp)

lemma frechet_vec_nth:
  fixes f::"real \<Rightarrow> ('a::real_normed_vector)^'m" and x::real and T::"real set" 
  defines "x\<^sub>0 \<equiv> netlimit (at x within T)"
  assumes "((\<lambda>y. (f y - f x\<^sub>0 - (y - x\<^sub>0) *\<^sub>R f' x) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
  shows "((\<lambda>y. (f y $ i - f x\<^sub>0 $ i - (y - x\<^sub>0) *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>y - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at x within T)"
proof(unfold tendsto_iff dist_norm, clarify)
  let "?\<Delta>" = "\<lambda>y. y - x\<^sub>0" and "?\<Delta>f" = "\<lambda>y. f y - f x\<^sub>0"
  fix \<epsilon>::real assume "0 < \<epsilon>"
  let "?P" = "\<lambda>y. \<parallel>(?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x) /\<^sub>R (\<parallel>?\<Delta> y\<parallel>) - 0\<parallel> < \<epsilon>"
  and "?Q" = "\<lambda>y. \<parallel>(f y $ i - f x\<^sub>0 $ i - ?\<Delta> y *\<^sub>R f' x $ i) /\<^sub>R (\<parallel>?\<Delta> y\<parallel>) - 0\<parallel> < \<epsilon>"
  have "eventually ?P (at x within T)" 
    using \<open>0 < \<epsilon>\<close> assms unfolding tendsto_iff by auto
  thus "eventually ?Q (at x within T)"
  proof(rule_tac P="?P" in eventually_mono, simp_all)
    let "?u y i" = "f y $ i - f x\<^sub>0 $ i - ?\<Delta> y *\<^sub>R f' x $ i"
    fix y assume hyp:"inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>) < \<epsilon>"
    have "\<parallel>(?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x) $ i\<parallel> \<le> \<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>"
      using Finite_Cartesian_Product.norm_nth_le by blast
    also have "\<parallel>?u y i\<parallel> = \<parallel>(?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x) $ i\<parallel>" 
      by simp
    ultimately have "\<parallel>?u y i\<parallel> \<le> \<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>" 
      by linarith
    hence "inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?u y i\<parallel>) \<le> inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>f y - ?\<Delta> y *\<^sub>R f' x\<parallel>)"
      by (simp add: mult_left_mono)
    thus "inverse \<bar>?\<Delta> y\<bar> * (\<parallel>f y $ i - f x\<^sub>0 $ i - ?\<Delta> y *\<^sub>R f' x $ i\<parallel>) < \<epsilon>"
      using hyp by linarith
  qed
qed

lemma has_derivative_vec_nth:
  assumes "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' x) at x within T"
  shows "D (\<lambda>t. f t $ i) \<mapsto> (\<lambda>h. h *\<^sub>R f' x $ i) at x within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using frechet_vec_nth[of x T f] assms unfolding has_derivative_def by auto

lemma has_vderiv_on_vec_nth:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)"
  assumes "D x = (\<lambda>t. f (x t)) on T"
  shows "D (\<lambda>t. x t $ i) = (\<lambda>t. f (x t) $ i) on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  by(rule has_derivative_vec_nth, simp)

section\<open> Ordinary Differential Equations \<close>

subsection\<open> Picard-Lindeloef \<close>

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

text\<open> The next locale makes explicit the conditions for applying the Picard-Lindeloef theorem. This
guarantees a unique solution for every initial value problem represented with a vector field 
@{term f} and an initial time @{term t\<^sub>0}. It is mostly a simplified reformulation of the approach 
taken by the people who created the Ordinary Differential Equations entry in the AFP. \<close>

locale picard_lindeloef =
  fixes f::"real \<Rightarrow> ('a::banach) \<Rightarrow> 'a" and T::"real set" and L t\<^sub>0::real
  assumes init_time: "t\<^sub>0 \<in> T"
    and cont_vec_field: "continuous_on (T \<times> UNIV) (\<lambda>(t, x). f t x)"
    and lipschitz_vec_field: "\<And>t. t \<in> T \<Longrightarrow> L-lipschitz_on UNIV (\<lambda>x. f t x)"
    and nonempty_time: "T \<noteq> {}"
    and interval_time: "is_interval T"
    and compact_time: "compact T"
    and lipschitz_bound: "\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> abs (s - t) * L < 1"
begin

sublocale continuous_rhs T UNIV
  using cont_vec_field unfolding continuous_rhs_def by simp

sublocale global_lipschitz T UNIV
  using lipschitz_vec_field unfolding global_lipschitz_def by simp

sublocale closed_domain UNIV
  unfolding closed_domain_def by simp

sublocale compact_interval
  using interval_time nonempty_time compact_time by(unfold_locales, auto)

lemma is_ubc:
  shows "unique_on_bounded_closed t\<^sub>0 T s f UNIV L"
  using nonempty_time unfolding ubc_definitions apply safe
  by(auto simp: compact_time interval_time init_time 
      lipschitz_vec_field lipschitz_bound cont_vec_field)

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

lemma unique_solution:
  assumes "D x = (\<lambda>t. f t (x t)) on T" and "x t\<^sub>0 = s"
    and "D y = (\<lambda>t. f t (y t)) on T" and "y t\<^sub>0 = s" and "t \<in> T" 
  shows "x t = y t"
  apply(rule unique_on_bounded_closed.unique_solution)
  using is_ubc[of s] apply blast
  using assms unfolding solves_ode_def by auto

abbreviation "phi t s \<equiv> (apply_bcontfun (unique_on_bounded_closed.fixed_point t\<^sub>0 T s f UNIV)) t"

lemma fixpoint_solves_ivp:
  shows "D (\<lambda>t. phi t s) = (\<lambda>t. f t (phi t s)) on T" and "phi t\<^sub>0 s = s"
  using is_ubc[of s] unique_on_bounded_closed.fixed_point_solution[of t\<^sub>0 T s f UNIV L] 
    unique_on_bounded_closed.fixed_point_iv[of t\<^sub>0 T s f UNIV L] 
  unfolding solves_ode_def by auto

lemma fixpoint_usolves_ivp:
  assumes "D x = (\<lambda>t. f t (x t)) on T" and "x t\<^sub>0 = s" and "t \<in> T"
  shows "x t = phi t s"
  using unique_solution[OF assms(1,2)] fixpoint_solves_ivp assms by blast

end

subsection\<open> Flows for ODEs \<close>

text\<open> This locale is a particular case of the previous one. It makes the unique solution for initial 
value problems explicit, it restricts the vector field to reflect autonomous systems (those that do 
not depend explicitly on time), and it sets the initial time equal to 0. This is the first step 
towards formalizing the flow of a differential equation, i.e. the function that maps every point to 
the unique trajectory tangent to the vector field. \<close>

locale local_flow = picard_lindeloef "(\<lambda> t. f)" T L 0 for f::"('a::banach) \<Rightarrow> 'a" and T L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp: "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T" "\<phi> 0 s = s "
begin

lemma is_fixpoint:
  assumes "t \<in> T"
  shows "\<phi> t s = phi t s"
  apply(rule fixpoint_usolves_ivp)
  using ivp assms init_time by simp_all

lemma solves_ode:
  shows "((\<lambda> t. \<phi> t s) solves_ode (\<lambda> t. f))T UNIV"
  unfolding solves_ode_def using ivp(1) by auto

lemma usolves_ivp:
  assumes "D x = (\<lambda>t. f (x t)) on T" and "x 0 = s" and "t \<in> T"
  shows "x t = \<phi> t s"
proof-
  have "x t = phi t s" 
    using assms fixpoint_usolves_ivp by blast
  also have "... = \<phi> t s" 
    using assms is_fixpoint by force 
  finally show ?thesis .
qed

lemma usolves_on_compact_subset:
  assumes "T' \<subseteq> T" and "compact_interval T'" and "0 \<in> T'" and "t \<in> T'"
      and x_solves: "(x solves_ode (\<lambda>t. f)) T' UNIV"
  shows "\<phi> t (x 0) = x t"
proof-
  have obs:"((\<lambda> \<tau>. \<phi> \<tau> (x 0)) solves_ode (\<lambda> \<tau>. f))T' UNIV" 
    using \<open>T' \<subseteq> T\<close> solves_ode_on_subset solves_ode by (metis subset_eq) 
  have "unique_on_bounded_closed 0 T (x 0) (\<lambda> \<tau>. f) UNIV L"
    using is_ubc by blast
  hence "unique_on_bounded_closed 0 T' (x 0) (\<lambda> \<tau>. f) UNIV L" 
    using unique_on_bounded_closed.unique_on_bounded_closed_on_compact_subset
    \<open>0 \<in> T'\<close> \<open>T' \<subseteq> T\<close> and \<open>compact_interval T'\<close> by blast
  moreover have "\<phi> 0 (x 0) = x 0" 
    using ivp by blast
  ultimately show "\<phi> t (x 0) = x t" 
    using unique_on_bounded_closed.unique_solution obs x_solves \<open>t \<in> T'\<close> by blast 
qed

end

lemma flow_on_compact_subset:
  assumes flow_on_big: "local_flow f T' L \<phi>" and "T \<subseteq> T'" 
    and "compact_interval T" and "0 \<in> T"
  shows "local_flow f T L \<phi>"
proof(unfold local_flow_def local_flow_axioms_def, safe)
  fix s show "\<phi> 0 s = s"
    using local_flow.ivp(2) flow_on_big by blast
  show "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T"
    using assms solves_ode_on_subset[where T=T and S=T' and x="\<lambda>t. \<phi> t s" and X=UNIV]
    unfolding local_flow_def local_flow_axioms_def solves_ode_def by force
next
  show "picard_lindeloef (\<lambda>t. f) T L 0"
    using assms apply(unfold local_flow_def local_flow_axioms_def)
    apply(unfold picard_lindeloef_def ubc_definitions)
    apply(meson Sigma_mono continuous_on_subset subsetI)
    by(simp_all add: subset_eq)
qed

text\<open> Finally, the flow exists when the unique solution from the last locale is defined in all of 
@{text "\<real>"}. Here we prove that it is a dyanmical system, i.e. a group action on the additive group 
of the real numbers.\<close>

locale global_flow = local_flow f UNIV L \<phi> for f L \<phi>
begin 

lemma add_flow_solves: "D (\<lambda>\<tau>. \<phi> (\<tau> + t) s) = (\<lambda>\<tau>. f (\<phi> (\<tau> + t) s)) on UNIV"
  apply(subgoal_tac "D ((\<lambda>\<tau>. \<phi> \<tau> s) \<circ> (\<lambda>\<tau>. \<tau> + t)) = 
    (\<lambda>x. (\<lambda>\<tau>. 1) x *\<^sub>R (\<lambda>t. f (\<phi> t s)) ((\<lambda>\<tau>. \<tau> + t) x)) on UNIV", simp add: comp_def)
  apply(rule has_vderiv_on_compose) 
  using solves_ode min_max_interval unfolding solves_ode_def apply force
  apply(rule_tac f'1="\<lambda> x. 1 " and g'1="\<lambda> x. 0" in derivative_intros(191))
  by(rule derivative_intros, simp)+ simp_all

lemma is_group_action:
  shows "\<phi> 0 s = s"
    and "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
proof-
  show "\<phi> 0 s = s"
    using ivp by simp
  have "\<phi> (0 + t2) s = \<phi> t2 s" 
    by simp
  moreover have "D (\<lambda>\<tau>. \<phi> (\<tau> + t2) s) = (\<lambda>\<tau>. f (\<phi> (\<tau> + t2) s)) on UNIV" 
    using add_flow_solves by simp
  moreover have "\<phi> 0 (\<phi> t2 s) = \<phi> t2 s" 
    using ivp by simp
  ultimately have "\<And> t. \<phi> (t + t2) s = \<phi> t (\<phi> t2 s)"
    using usolves_ivp by blast
  thus "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)" 
    by simp
qed

end

lemma localize_global_flow:
  assumes "global_flow f L \<phi>" and "compact_interval T"
  shows "local_flow f T L \<phi>"
  using assms unfolding global_flow_def local_flow_def picard_lindeloef_def by simp

subsubsection\<open> Example \<close>

text\<open> Below there is an example showing the general methodology to introduce pairs of vector fields 
and their respective flows using the previous locales. \<close>

lemma picard_lindeloef_constant: "0 \<le> t \<Longrightarrow> picard_lindeloef (\<lambda>t s. c) {0..t} (1 / (t + 1)) 0"
  unfolding picard_lindeloef_def by(simp add: nonempty_set_def lipschitz_on_def, clarsimp, simp)

lemma line_vderiv_constant: "D (\<lambda>\<tau>. x + \<tau> *\<^sub>R c) = (\<lambda>t. c) on {0..t}"
  apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(191))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma line_is_local_flow:
  fixes c::"'a::banach"
  assumes "0 \<le> t"
  shows "local_flow (\<lambda> s. c) {0..t} (1/(t + 1)) (\<lambda> t x. x + t *\<^sub>R c)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using assms picard_lindeloef_constant apply blast
  using line_vderiv_constant by auto

end