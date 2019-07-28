theory hs_prelims
  imports "Ordinary_Differential_Equations.Picard_Lindeloef_Qualitative"

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

lemma abs_le_eq: 
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
  by linarith linarith

lemma real_ivl_eqs:
  assumes "0 < r"
  shows "ball x r = {x-r<--< x+r}"         and "{x-r<--< x+r} = {x-r<..< x+r}"
    and "ball (r / 2) (r / 2) = {0<--<r}"  and "{0<--<r} = {0<..<r}"
    and "ball 0 r = {-r<--<r}"             and "{-r<--<r} = {-r<..<r}"
    and "cball x r = {x-r--x+r}"           and "{x-r--x+r} = {x-r..x+r}"
    and "cball (r / 2) (r / 2) = {0--r}"   and "{0--r} = {0..r}"
    and "cball 0 r = {-r--r}"              and "{-r--r} = {-r..r}"
  unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
  using assms apply(auto simp: cball_def ball_def dist_norm)
  by(simp_all add: field_simps)

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
    and has_vderiv_on_id [poly_derivatives]
    and derivative_intros(191) [poly_derivatives]
    and derivative_intros(192) [poly_derivatives]
    and derivative_intros(194) [poly_derivatives]

lemma has_vector_derivative_mult_const [derivative_intros]: 
  "((*) a has_vector_derivative a) F"
  by (auto intro: derivative_eq_intros)

lemma has_derivative_mult_const [derivative_intros]: "D (*) a \<mapsto> (\<lambda>x. x *\<^sub>R a) F"
  using has_vector_derivative_mult_const unfolding has_vector_derivative_def by simp

lemma has_vderiv_on_mult_const [derivative_intros]: "D (*) a = (\<lambda>x. a) on T"
  using has_vector_derivative_mult_const unfolding has_vderiv_on_def by auto

lemma has_vderiv_on_power2 [derivative_intros]: "D power2 = (*) 2 on T"
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15)) auto

lemma has_vderiv_on_divide_cnst [derivative_intros]: "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  apply(rule_tac f'1="\<lambda>t. t" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
  by(auto intro: derivative_eq_intros)

lemma [poly_derivatives]: "g = (*) 2 \<Longrightarrow> D power2 = g on T"
  using has_vderiv_on_power2 by auto

lemma [poly_derivatives]: "D f = f' on T \<Longrightarrow> g = (\<lambda>t. - f' t) \<Longrightarrow> D (\<lambda>t. - f t) = g on T"
  using has_vderiv_on_uminus by auto

lemma [poly_derivatives]: "a \<noteq> 0 \<Longrightarrow> g = (\<lambda>t. 1/a) \<Longrightarrow> D (\<lambda>t. t/a) = g on T"
  using has_vderiv_on_divide_cnst by auto

lemma has_vderiv_on_compose_eq: 
  assumes "D f = f' on g ` T" 
    and " D g = g' on T"
    and "h = (\<lambda>x. g' x *\<^sub>R f' (g x))"
  shows "D (\<lambda>t. f (g t)) = h on T"
  apply(subst ssubst[of h], simp)
  using assms has_vderiv_on_compose by auto

lemma [poly_derivatives]:
  assumes "(a::real) \<noteq> 0" and "D f = f' on T" and "g = (\<lambda>t. (f' t)/a)"
  shows "D (\<lambda>t. (f t)/a) = g on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. t/a" "\<lambda>t. 1/a"])
  using assms by(auto intro: poly_derivatives)

lemma [poly_derivatives]:
  fixes f::"real \<Rightarrow> real"
  assumes "D f = f' on T" and "g = (\<lambda>t. 2 *\<^sub>R (f t) * (f' t))"
  shows "D (\<lambda>t. (f t)^2) = g on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. t^2"])
  using assms by(auto intro!: poly_derivatives)

lemma has_vderiv_on_cos: "D f = f' on T \<Longrightarrow> D (\<lambda>t. cos (f t)) = (\<lambda>t. - sin (f t) *\<^sub>R (f' t)) on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. cos t"])
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma has_vderiv_on_sin: "D f = f' on T \<Longrightarrow> D (\<lambda>t. sin (f t)) = (\<lambda>t. cos (f t) *\<^sub>R (f' t)) on T"
  apply(rule has_vderiv_on_compose_eq[of "\<lambda>t. sin t"])
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma [poly_derivatives]:
  assumes "D f = f' on T" and "g = (\<lambda>t. - sin (f t) *\<^sub>R (f' t))"
  shows "D (\<lambda>t. cos (f t)) = g on T"
  using assms and has_vderiv_on_cos by auto

lemma [poly_derivatives]:
  assumes "D f = f' on T" and "g = (\<lambda>t. cos (f t) *\<^sub>R (f' t))"
  shows "D (\<lambda>t. sin (f t)) = g on T"
  using assms and has_vderiv_on_sin by auto

lemma "D (\<lambda>t. a * t\<^sup>2 / 2) = (*) a on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>r. a * r + v) = (\<lambda>t. a) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v - a * t) = (\<lambda>x. - a) on T"
  by(auto intro!: poly_derivatives)

thm poly_derivatives


subsection\<open> Multivariable Derivatives \<close>

lemma add_solves:
  assumes "D x = x' on (\<lambda>\<tau>. \<tau> + t) ` T"
  shows "D (\<lambda>\<tau>. x (\<tau> + t)) = (\<lambda>\<tau>. x' (\<tau> + t)) on T"
  apply(subgoal_tac "D (x \<circ> (\<lambda>\<tau>. \<tau> + t)) = (\<lambda>\<tau>. 1 *\<^sub>R x' (\<tau> + t)) on T")
  apply(simp add: comp_def, rule has_vderiv_on_compose) 
  using assms apply blast
  apply(rule_tac f'1="\<lambda> x. 1 " and g'1="\<lambda> x. 0" in derivative_intros(191))
  by(rule derivative_intros, simp)+ simp_all

lemma eventually_at_within_mono:
  assumes "t \<in> interior T" and "T \<subseteq> S" 
    and "eventually P (at t within T)"
  shows "eventually P (at t within S)"
  by (meson assms eventually_within_interior interior_mono subsetD)

lemma netlimit_at_within_mono: 
  fixes t::"'a::{perfect_space,t2_space}"
  assumes "t \<in> interior T" and "T \<subseteq> S"
  shows "netlimit (at t within S) = t"
  using assms(1) interior_mono[OF \<open>T \<subseteq> S\<close>] netlimit_within_interior by auto
  
lemma has_derivative_at_within_mono:
  assumes "(t::real) \<in> interior T" and "T \<subseteq> S"
    and "D f \<mapsto> f' at t within T"
  shows "D f \<mapsto> f' at t within S"
  using assms(3) apply(unfold has_derivative_def tendsto_iff, safe)
  unfolding netlimit_at_within_mono[OF assms(1,2)] netlimit_within_interior[OF assms(1)]
  by (rule eventually_at_within_mono[OF assms(1,2)]) simp

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

text\<open> The next locale makes explicit the conditions for applying the Picard-Lindeloef theorem. This
guarantees a unique solution for every initial value problem represented with a vector field 
@{term f} and an initial time @{term t\<^sub>0}. It is mostly a simplified reformulation of the approach 
taken by the people who created the Ordinary Differential Equations entry in the AFP. \<close>

definition "ivp_sols f T S t\<^sub>0 s = 
  {x |x. (D x = (\<lambda>t. f t (x t)) on T) \<and> x t\<^sub>0 = s \<and> x \<in> T \<rightarrow> S}"

lemma ivp_solsI: 
  assumes "D x = (\<lambda>t. f t (x t)) on T" "x t\<^sub>0 = s" "x \<in> T \<rightarrow> S"
  shows "x \<in> ivp_sols f T S t\<^sub>0 s"
  using assms unfolding ivp_sols_def by blast

lemma ivp_solsD:
  assumes "x \<in> ivp_sols f T S t\<^sub>0 s"
  shows "D x = (\<lambda>t. f t (x t)) on T"
    and "x t\<^sub>0 = s" and "x \<in> T \<rightarrow> S"
  using assms unfolding ivp_sols_def by auto

locale picard_lindeloef =
  fixes f::"real \<Rightarrow> ('a::{heine_borel,banach}) \<Rightarrow> 'a" and T::"real set" and S::"'a set" and t\<^sub>0::real
  assumes init_time: "t\<^sub>0 \<in> T"
    and cont_vec_field: "\<forall>s \<in> S. continuous_on T (\<lambda>t. f t s)"
    and lipschitz_vec_field: "local_lipschitz T S f"
    and interval_time: "is_interval T"
    and open_domain: "open T" "open S"
begin

sublocale ll_on_open_it T f S t\<^sub>0
  by (unfold_locales) (auto simp: cont_vec_field lipschitz_vec_field interval_time open_domain) 

lemmas subintervalI = closed_segment_subset_domain

lemma subintervalD:
  assumes "{t\<^sub>1--t\<^sub>2} \<subseteq> T"
  shows "t\<^sub>1 \<in> T" and "t\<^sub>2 \<in> T"
  using assms by auto

lemma csols_eq: "csols t\<^sub>0 s = {(x, t). t \<in> T \<and>  x \<in> ivp_sols f {t\<^sub>0--t} S t\<^sub>0 s}"
  unfolding ivp_sols_def csols_def solves_ode_def using subintervalI[OF init_time] by auto

abbreviation "ex_ivl s \<equiv> existence_ivl t\<^sub>0 s"

lemma unique_solution:
  assumes xivp: "D x = (\<lambda>t. f t (x t)) on {t\<^sub>0--t}" "x t\<^sub>0 = s" "x \<in> {t\<^sub>0--t} \<rightarrow> S" and "t \<in> T"
    and yivp: "D y = (\<lambda>t. f t (y t)) on {t\<^sub>0--t}" "y t\<^sub>0 = s" "y \<in> {t\<^sub>0--t} \<rightarrow> S" and "s \<in> S" 
  shows "x t = y t"
proof-
  have "(x, t) \<in> csols t\<^sub>0 s"
    using xivp \<open>t \<in> T\<close> unfolding csols_eq ivp_sols_def by auto
  hence ivl_fact: "{t\<^sub>0--t} \<subseteq> ex_ivl s"
    unfolding existence_ivl_def by auto
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>{t\<^sub>0--t}. x \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" x] xivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  also have "\<forall>\<tau>\<in>{t\<^sub>0--t}. y \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" y] yivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  ultimately show "x t = y t"
    by auto
qed

lemma solution_eq_flow:
  assumes xivp: "D x = (\<lambda>t. f t (x t)) on ex_ivl s" "x t\<^sub>0 = s" "x \<in> ex_ivl s \<rightarrow> S" 
    and "t \<in> ex_ivl s" and "s \<in> S" 
  shows "x t = flow t\<^sub>0 s t"
proof-
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>ex_ivl s. x \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "ex_ivl s" x] existence_ivl_initial_time[OF init_time \<open>s \<in> S\<close>]
      xivp flow_initial_time[OF init_time \<open>s \<in> S\<close>] unfolding solves_ode_def by simp
  thus "x t = flow t\<^sub>0 s t"
    by (auto simp: \<open>t \<in> ex_ivl s\<close>)
qed

end

subsection\<open> Flows for ODEs \<close>

text\<open> This locale is a particular case of the previous one. It makes the unique solution for initial 
value problems explicit, it restricts the vector field to reflect autonomous systems (those that do 
not depend explicitly on time), and it sets the initial time equal to 0. This is the first step 
towards formalizing the flow of a differential equation, i.e. the function that maps every point to 
the unique trajectory tangent to the vector field. \<close>

locale local_flow = picard_lindeloef "(\<lambda> t. f)" T S 0 
  for f::"('a::{heine_borel,banach}) \<Rightarrow> 'a" and T S L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp:"\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--t})"
              "\<And> s. s \<in> S \<Longrightarrow> \<phi> 0 s = s"
              "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (\<lambda>t. \<phi> t s) \<in> {0--t} \<rightarrow> S"
begin

lemma in_ivp_sols_ivl: 
  assumes "t \<in> T" "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> ivp_sols (\<lambda>t. f) {0--t} S 0 s"
  apply(rule ivp_solsI)
  using ivp assms by auto

lemma ex_ivl_eq:
  assumes "s \<in> S"
  shows "ex_ivl s = T"
  using existence_ivl_subset[of s] apply safe
  unfolding existence_ivl_def csols_eq 
  using in_ivp_sols_ivl[OF _ assms] by blast

lemma in_domain:
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> T \<rightarrow> S"
  unfolding ex_ivl_eq[symmetric] existence_ivl_def
  using local.mem_existence_ivl_subset ivp(3)[OF _ assms] by blast

lemma has_derivative_on_open1: 
  assumes  "t > 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t + r/2 > 0"
    using \<open>r > 0\<close> \<open>t > 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t + r/2} \<subseteq> T"
    unfolding abs_le_eq abs_le_eq real_ivl_eqs[OF \<open>t > 0\<close>] real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] 
    by clarify (case_tac "t < x", simp_all add: cball_def ball_def dist_norm subset_eq field_simps)
  have "t + r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs[OF rHyp(1)] by (simp add: subset_eq)
  hence "{0--t + r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t + r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t + r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by auto
  have "t \<in> {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] using rHyp \<open>t > 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t + r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open2: 
  assumes "t < 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t - r/2 < 0"
    using \<open>r > 0\<close> \<open>t < 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t - r/2} \<subseteq> T"
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
      real_ivl_eqs[OF rHyp(1)] by(auto simp: subset_eq)
  have "t - r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs by (simp add: subset_eq)
  hence "{0--t - r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t - r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t - r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  have "t \<in> {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl using rHyp \<open>t < 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t - r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open3: 
  assumes "s \<in> S"
  obtains B where "0 \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) at 0 within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball 0 r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) init_time by blast
  hence "r/2 \<in> T" "-r/2 \<in> T" "r/2 > 0"
    unfolding real_ivl_eqs by auto
  hence subs: "{0--r/2} \<subseteq> T" "{0--(-r/2)} \<subseteq> T"
    using subintervalI[OF init_time] by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  also have "{0--r/2} = {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    "{0--(-r/2)} = {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  ultimately have vderivs:
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  have obs: "0 \<in> {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl using \<open>r/2 > 0\<close> by auto
  have union: "{-r/2--r/2} = {0--r/2} \<union> {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2--r/2})"
    using has_vderiv_on_union[OF vderivs] by simp
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2<--<r/2})"
    using has_vderiv_on_subset[OF _ segment_open_subset_closed[of "-r/2" "r/2"]] by auto
  hence "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) (at 0 within {-r/2<--<r/2})"
    unfolding has_vderiv_on_def has_vector_derivative_def using obs by blast
  moreover have "open {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl by simp
  moreover have "{-r/2<--<r/2} \<subseteq> T"
    using subs union segment_open_subset_closed by blast 
  ultimately show ?thesis
    using obs that by blast
qed

lemma has_derivative_on_open: 
  assumes "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
  apply(subgoal_tac "t < 0 \<or> t = 0 \<or> t > 0")
  using has_derivative_on_open1[OF _ assms] has_derivative_on_open2[OF _ assms]
    has_derivative_on_open3[OF \<open>s \<in> S\<close>] by blast force

lemma has_vderiv_on_domain:
  assumes "s \<in> S"
  shows "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T"
proof(unfold has_vderiv_on_def has_vector_derivative_def, clarsimp)
  fix t assume "t \<in> T"
  then obtain B where "t \<in> B" and "open B" and "B \<subseteq> T" 
    and Dhyp: "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>xa. xa *\<^sub>R f (\<phi> t s)) at t within B"
    using assms has_derivative_on_open[OF \<open>t \<in> T\<close>] by blast
  hence "t \<in> interior B"
    using interior_eq by auto
  thus "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>xa. xa *\<^sub>R f (\<phi> t s)) at t within T"
    using has_derivative_at_within_mono[OF _ \<open>B \<subseteq> T\<close> Dhyp] by blast
qed

lemma eq_solution:
  assumes "x \<in> (ivp_sols (\<lambda>t. f) T S 0 s)" and "t \<in> T" and "s \<in> S"
  shows "x t = \<phi> t s"
proof-
  have "D x = (\<lambda>t. f (x t)) on (ex_ivl s)" and "x 0 = s" and "x \<in> (ex_ivl s) \<rightarrow> S"
    using ivp_solsD[OF assms(1)] unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by auto
  note solution_eq_flow[OF this]
  hence "x t = flow 0 s t"
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] using assms by blast
  also have "\<phi> t s = flow 0 s t"
    apply(rule solution_eq_flow ivp)
        apply(simp_all add: assms(2,3) ivp(2)[OF \<open>s \<in> S\<close>])
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by (auto simp: has_vderiv_on_domain assms in_domain)
  ultimately show "x t = \<phi> t s"
    by simp
qed

lemma in_ivp_sols: 
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> ivp_sols (\<lambda>t. f) T S 0 s"
  using has_vderiv_on_domain ivp(2) in_domain apply(rule ivp_solsI)
  using assms by auto

lemma eq_solution_ivl:
  assumes xivp: "D x = (\<lambda>t. f (x t)) on {0--t}" "x 0 = s" "x \<in> {0--t} \<rightarrow> S" 
    and indom: "t \<in> T" "s \<in> S"
  shows "x t = \<phi> t s"
  apply(rule unique_solution[OF xivp \<open>t \<in> T\<close>])
  using \<open>s \<in> S\<close> ivp indom by auto

lemma is_monoid_action:
  assumes "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on (\<lambda>\<tau>. \<tau> + t\<^sub>2) ` {0--t\<^sub>1}" 
    and "(\<lambda>t. \<phi> (t + t\<^sub>2) s) \<in> {0--t\<^sub>1} \<rightarrow> S"
    and indom: "t\<^sub>1 \<in> T" "s \<in> S" "t\<^sub>2 \<in> {0--t\<^sub>1}"
  shows "\<phi> 0 s = s"
    and "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
proof-
  show "\<phi> 0 s = s"
    using ivp indom(1,2) by simp
  have "\<phi> (0 + t\<^sub>2) s = \<phi> t\<^sub>2 s" 
    by simp
  also have "\<phi> t\<^sub>2 s \<in> S"
    using \<open>t\<^sub>2 \<in> {0--t\<^sub>1}\<close> ivp(3)[OF \<open>t\<^sub>1 \<in> T\<close> \<open>s \<in> S\<close>] by auto
  finally show "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
    using eq_solution_ivl[OF add_solves[OF assms(1)]] assms by auto 
qed

end

subsubsection\<open> Example \<close>

text\<open> Below there is an example showing the general methodolog to introduce pairs of vector fields 
and their respective flows using the previous locales. \<close>

lemma line_vderiv_constant: "D (\<lambda>\<tau>. s + \<tau> *\<^sub>R c) = (\<lambda>t. c) on T"
  apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(191))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma line_is_local_flow: "local_flow (\<lambda> s. c) UNIV UNIV (\<lambda> t s. s + t *\<^sub>R c)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)
  using line_vderiv_constant by auto

end