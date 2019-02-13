theory hs_prelims
  imports "Ordinary_Differential_Equations.Initial_Value_Problem"

begin

section {* Hybrid Systems Preliminaries *}

text{* This file presents a miscellaneous collection of preliminary lemmas for verification of 
Hybrid Systems in Isabelle.*}

subsection{* Real Numbers *}

lemma case_of_fst[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> fst) x)"
  by auto

lemma case_of_snd[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f x) = (\<lambda> x. (f \<circ> snd) x)"
  by auto

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis basic_trans_rules(23) monoid_mult_class.power2_eq_square more_arith_simps(6) 
      mult_left_mono real_sqrt_le_iff' zero_le_one)

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  by (metis (full_types) abs_of_nat le_square of_nat_mono of_nat_mult real_sqrt_abs2 real_sqrt_le_iff)

lemma semiring_factor_left:"a * b + a * c = a * ((b::('a::semiring)) + c)"
  by(subst Groups.algebra_simps(18), simp)

lemma sin_cos_squared_add3:"(x::('a:: {banach,real_normed_field})) * (sin t)\<^sup>2 + x * (cos t)\<^sup>2 = x"
  by(subst semiring_factor_left, subst sin_cos_squared_add, simp)

lemma sin_cos_squared_add4:"(x::('a:: {banach,real_normed_field})) * (cos t)\<^sup>2 + x * (sin t)\<^sup>2 = x"
  by(subst semiring_factor_left, subst sin_cos_squared_add2, simp)

lemma [simp]:"((x::real) * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"  
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq) 
qed

subsection{* Unit vectors and vector norm *}

lemma norm_scalar_mult: "norm ((c::real) *s x) = \<bar>c\<bar> * norm x"
  unfolding norm_vec_def L2_set_def real_norm_def vector_scalar_mult_def apply simp
  apply(subgoal_tac "(\<Sum>i\<in>UNIV. (c * x $ i)\<^sup>2) = \<bar>c\<bar>\<^sup>2 * (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2) ")
   apply(simp add: real_sqrt_mult)
  apply(simp add: sum_distrib_left)
  by (meson power_mult_distrib)

lemma squared_norm_vec:"(norm x)\<^sup>2 = (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
  unfolding norm_vec_def L2_set_def by (simp add: sum_nonneg)

lemma sgn_is_unit_vec:"sgn x = 1 / norm x *s x"
  unfolding sgn_vec_def scaleR_vec_def by(simp add: vector_scalar_mult_def divide_inverse_commute)

lemma norm_sgn_unit:"(x::real^'n) \<noteq> 0 \<Longrightarrow> norm (sgn x) = 1"
  by(simp add: sgn_vec_def)

lemma norm_matrix_sgn:"norm (A *v (x::real^'n)) = norm (A *v (sgn x)) * norm x"
  unfolding sgn_is_unit_vec vector_scalar_commute norm_scalar_mult by simp 

lemma vector_norm_distr_minus:
  fixes A::"('a::{real_normed_vector, ring_1})^'n^'m"
  shows "norm (A *v x - A *v y) = norm (A *v (x - y))"
  by(subst matrix_vector_mult_diff_distrib, simp)

subsection{* Matrix norm *}

abbreviation "norm\<^sub>S (A::real^'n^'m) \<equiv> Sup {norm (A *v x) | x. norm x = 1}"

lemma unit_norms_bound:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "norm x = 1 \<Longrightarrow> norm (A *v x) \<le> norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)"
proof-
  assume "norm x = 1"
  from this have "\<And> j. \<bar>x $ j\<bar> \<le> 1"
    by (metis component_le_norm_cart)
  then have "\<And>i j. \<bar>A $ i $ j\<bar> * \<bar>x $ j\<bar> \<le> \<bar>A $ i $ j\<bar> * 1"
    using mult_left_mono by (simp add: mult_left_le) 
  from this have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * \<bar>x $ j\<bar>)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    by (simp add: power_mono sum_mono sum_nonneg)
  also have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j * x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j * x $ j\<bar>)\<^sup>2"
    using abs_le_square_iff by force 
  moreover have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j * x $ j\<bar>)\<^sup>2 = (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * \<bar>x $ j\<bar>)\<^sup>2"
    by (simp add: abs_mult)
  ultimately have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j * x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    using order_trans by fastforce
  hence "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j * x $ j)\<^sup>2) \<le> (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2)"
    by(simp add: sum_mono)
  then have "(sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j * x $ j)\<^sup>2)) \<le> (sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2))"
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
  shows "norm\<^sub>S A \<le> real CARD('n) * real CARD('m) *(maxAbs A)" (is "norm\<^sub>S A \<le>?n * ?m * (maxAbs A)")
proof-
  {fix x::"(real, 'n) vec" assume "norm x = 1"
    hence comp_le_1:"\<forall> i::'n. \<bar>x $ i\<bar> \<le> 1"
      by (simp add: norm_bound_component_le_cart)
    have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)"
      using matrix_mult_sum by blast
    hence "norm (A *v x) \<le> (\<Sum>(i::'n)\<in>UNIV. norm ( x $ i *s column i A))"
      by (simp add: sum_norm_le)
    also have "... = (\<Sum>(i::'n)\<in>UNIV. \<bar>x $ i\<bar> * norm (column i A))"
      by (simp add: norm_scalar_mult) 
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. norm (column i A))"
      by (metis (no_types, lifting) Groups.mult_ac(2) comp_le_1 mult_left_le norm_ge_zero sum_mono)
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. ?m * maxAbs A)"
    proof(unfold norm_vec_def L2_set_def real_norm_def)
      have "\<And>i j. \<bar>column i A $ j\<bar> \<le> maxAbs A"
        using finite_matrix_abs Max_ge unfolding column_def maxAbs_def by(simp, blast)
      hence "\<And>i j. \<bar>column i A $ j\<bar>\<^sup>2 \<le> (maxAbs A)\<^sup>2"
        by (metis (no_types, lifting) One_nat_def abs_ge_zero numerals(2) order_trans_rules(23) 
            power2_abs power2_le_iff_abs_le)
      then have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> (\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2)"
        by (meson sum_mono)
      also have "(\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2) = ?m * (maxAbs A)\<^sup>2" by simp
      ultimately have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> ?m * (maxAbs A)\<^sup>2" by force
      hence "\<And>i. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> sqrt (?m * (maxAbs A)\<^sup>2)"
        by(simp add: real_sqrt_le_mono)
      also have "sqrt (?m * (maxAbs A)\<^sup>2) \<le> sqrt ?m * maxAbs A"
        using maxAbs_ge_0 real_sqrt_mult by auto
      also have "... \<le> ?m * maxAbs A"
        using sqrt_real_nat_le maxAbs_ge_0 mult_right_mono by blast  
      finally show "(\<Sum>i\<in>UNIV. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2)) \<le> (\<Sum>(i::'n)\<in>UNIV. ?m * maxAbs A)"
        by (meson sum_mono)
    qed
    also have "(\<Sum>(i::'n)\<in>UNIV. (maxAbs A)) = ?n * (maxAbs A)"
      using sum_constant_scale by auto
    ultimately have "norm (A *v x) \<le> ?n * ?m * (maxAbs A)" by simp}
  from this show ?thesis 
    using unit_norms_exists[of A] Connected.bounded_has_Sup(2) by blast
qed

subsection{* Derivatives *}

lemma closed_segment_mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "(\<And>r. r\<in>{a--b} \<Longrightarrow> (f has_derivative f' r) (at r within {a--b}))" and "a \<le> b"
  shows "\<exists>r\<in>{a--b}. f b - f a = f' r (b - a)"
  using assms closed_segment_eq_real_ivl and mvt_very_simple by auto

lemma convergences_solves_vec_nth:
  assumes "((\<lambda>y. (\<phi> y - \<phi> (netlimit (at x within {0..t})) - (y - netlimit (at x within {0..t})) *\<^sub>R f (\<phi> x)) /\<^sub>R
\<bar>y - netlimit (at x within {0..t})\<bar>) \<longlongrightarrow> 0) (at x within {0..t})" (is "((\<lambda>y. ?f y) \<longlongrightarrow> 0) ?net")
  shows "((\<lambda>y. (\<phi> y $ i - \<phi> (netlimit (at x within {0..t})) $ i - (y - netlimit (at x within {0..t})) *\<^sub>R f (\<phi> x) $ i) /\<^sub>R
\<bar>y - netlimit (at x within {0..t})\<bar>) \<longlongrightarrow> 0) (at x within {0..t})" (is "((\<lambda>y. ?g y i) \<longlongrightarrow> 0) ?net")
proof-
  from assms have  "((\<lambda>y. ?f y $ i) \<longlongrightarrow> 0 $ i) ?net" by(rule tendsto_vec_nth)
  also have "(\<lambda>y. ?f y $ i) = (\<lambda>y. ?g y i)" by auto
  ultimately show "((\<lambda>y. ?g y i) \<longlongrightarrow> 0) ?net" by auto
qed

lemma solves_vec_nth:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)"
  assumes "(\<phi> solves_ode (\<lambda> t. f)) {0..t} UNIV"
  shows "((\<lambda> t. (\<phi> t) $ i) solves_ode (\<lambda> t s. (f (\<phi> t)) $ i)) {0..t} UNIV"
  using assms unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def has_derivative_def 
  apply safe apply(auto simp: bounded_linear_def bounded_linear_axioms_def)[1]
   apply(erule_tac x="x" in ballE, clarsimp)
  apply(rule convergences_solves_vec_nth)
  by(simp_all add: Pi_def)

lemma solves_vec_lambda:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)" and \<phi>::"real \<Rightarrow> ('a^'n)"
  assumes "\<forall> i::'n. ((\<lambda> t. (\<phi> t) $ i) solves_ode (\<lambda> t s. (f (\<phi> t)) $ i)) {0..t} UNIV"
  shows "(\<phi> solves_ode (\<lambda> t. f)) {0..t} UNIV"
  using assms unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def has_derivative_def 
  apply safe apply(auto simp: bounded_linear_def bounded_linear_axioms_def)[1]
  by(rule Finite_Cartesian_Product.vec_tendstoI, simp_all)

named_theorems poly_derivatives "compilation of derivatives for kinematics and polynomials."

declare has_vderiv_on_const [poly_derivatives]

lemma origin_line_vector_derivative:"(( * ) a has_vector_derivative a) (at x within T)"
  by (auto intro: derivative_eq_intros)

lemma origin_line_derivative:"(( * ) a has_derivative (\<lambda>x. x *\<^sub>R a)) (at x within T)"
  using origin_line_vector_derivative unfolding has_vector_derivative_def by simp

lemma quadratic_monomial_derivative:
"((\<lambda>t::real. a * t\<^sup>2) has_derivative (\<lambda>t. a * (2 * x * t))) (at x within T)"
  apply(rule_tac g'1="\<lambda> t. 2 * x * t" in derivative_eq_intros(6))
   apply(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15))
  by (auto intro: derivative_eq_intros) 

lemma quadratic_monomial_derivative_div:
"((\<lambda>t::real. a * t\<^sup>2 / 2) has_derivative (\<lambda>t. a * x * t)) (at x within T)"
  apply(rule_tac f'1="\<lambda>t. a * (2 * x * t)" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
  using quadratic_monomial_derivative by auto

lemma quadratic_monomial_vderiv[poly_derivatives]:"((\<lambda>t. a * t\<^sup>2 / 2) has_vderiv_on ( * ) a) T"
  apply(simp add: has_vderiv_on_def has_vector_derivative_def, clarify)
  using quadratic_monomial_derivative_div by (simp add: mult_commute_abs)

lemma pos_vderiv[poly_derivatives]:
"((\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) has_vderiv_on (\<lambda>t. a * t + v)) T"
  apply(rule_tac f'="\<lambda> x. a * x + v" and g'1="\<lambda> x. 0" in derivative_intros(190))
    apply(rule_tac f'1="\<lambda> x. a * x" and g'1="\<lambda> x. v" in derivative_intros(190))
  using poly_derivatives(2) by(auto intro: derivative_intros)

lemma pos_derivative:
"t \<in> T \<Longrightarrow> ((\<lambda>\<tau>. a * \<tau>\<^sup>2 / 2 + v * \<tau> + x) has_derivative (\<lambda>x. x *\<^sub>R (a * t + v))) (at t within T)"
  using pos_vderiv unfolding has_vderiv_on_def has_vector_derivative_def by simp

lemma vel_vderiv[poly_derivatives]:"((\<lambda>r. a * r + v) has_vderiv_on (\<lambda>t. a)) T"
  apply(rule_tac f'1="\<lambda> x. a" and g'1="\<lambda> x. 0" in derivative_intros(190))
  unfolding has_vderiv_on_def by(auto intro: derivative_eq_intros)

lemma pos_vderiv_minus[poly_derivatives]:
"((\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) has_vderiv_on (\<lambda>x. v - a * x)) {0..t}"
  apply(subgoal_tac "((\<lambda>t. - a * t\<^sup>2 / 2 + v * t  +x) has_vderiv_on (\<lambda>x. - a * x + v)) {0..t}", simp)
  by(rule poly_derivatives)

lemma vel_vderiv_minus[poly_derivatives]:
"((\<lambda>t. v - a * t) has_vderiv_on (\<lambda>x. - a)) {0..t}"
  apply(subgoal_tac "((\<lambda>t. - a * t + v) has_vderiv_on (\<lambda>x. - a)) {0..t}", simp)
  by(rule poly_derivatives)

subsection{* Picard-Lindeloef *}

declare origin_line_vector_derivative [poly_derivatives]
    and origin_line_derivative [poly_derivatives]
    and quadratic_monomial_derivative [poly_derivatives]
    and quadratic_monomial_derivative_div [poly_derivatives]
    and pos_derivative [poly_derivatives]

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

locale picard_ivp =
  fixes f::"real \<Rightarrow> ('a::banach) \<Rightarrow> 'a" and T::"real set" and S::"'a set" and L t0::real
  assumes init_time:"t0 \<in> T"
    and cont_vec_field: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
    and lipschitz_vec_field: "\<And>t. t \<in> T \<Longrightarrow> L-lipschitz_on X (\<lambda>x. f t x)"
    and nonempty_time: "T \<noteq> {}"
    and interval_time: "is_interval T"
    and compact_time: "compact T"
    and lipschitz_bound: "\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> abs (s - t) * L < 1"
    and closed_domain: "closed S"
    and solution_in_domain:"\<And>x s t. t \<in> T \<Longrightarrow> x t0 = s \<Longrightarrow> x \<in> {t0--t} \<rightarrow> S \<Longrightarrow> 
      continuous_on {t0--t} x \<Longrightarrow> x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> S"
begin

sublocale continuous_rhs
  using cont_vec_field unfolding continuous_rhs_def by simp

sublocale global_lipschitz
  using lipschitz_vec_field unfolding global_lipschitz_def by simp

sublocale closed_domain S
  using closed_domain unfolding closed_domain_def by simp

sublocale compact_interval
  using interval_time nonempty_time compact_time by(unfold_locales, auto)

lemma is_ubc:
  assumes "s \<in> S"
  shows "unique_on_bounded_closed t0 T s f S L"
  using assms unfolding ubc_definitions apply safe
  prefer 6 using solution_in_domain apply simp
  prefer 2 using nonempty_time apply fastforce
  by(auto simp: compact_time interval_time init_time
      closed_domain lipschitz_vec_field lipschitz_bound cont_vec_field)

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
locale local_flow = picard_ivp "(\<lambda> t. f)" T S L 0 for f::"('a::banach) \<Rightarrow> 'a" and T S L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode (\<lambda> t. f))T S \<and> \<phi> 0 s = s"
begin

lemma is_fixed_point:
  assumes "s \<in> S" and "t \<in> T"
  shows "\<phi> t s = phi t s"
  apply(rule fixed_point_usolves)
  using ivp assms init_time by simp_all

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

lemma usolves:
  assumes "(x solves_ode (\<lambda>t. f))T S" and "x 0 = s" and "t \<in> T"
  shows "x t = \<phi> t s"
proof-
  from assms and fixed_point_usolves 
  have "x t = phi t s" by blast
  also have "... = \<phi> t s" using assms is_fixed_point
      init_time solves_ode_domainD by force 
  finally show ?thesis .
qed

lemma usolves_on_compact_subset:
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
  assumes flow_on_big:"local_flow f T' S L \<phi>" and "T \<subseteq> T'" and "compact_interval T" and "0 \<in> T"
  shows "local_flow f T S L \<phi>"
  unfolding local_flow_def local_flow_axioms_def proof(safe)
  fix s show "s \<in> S \<Longrightarrow> ((\<lambda>t. \<phi> t s) solves_ode (\<lambda>t. f)) T S" "s \<in> S \<Longrightarrow> \<phi> 0 s = s"
    using assms solves_ode_on_subset unfolding local_flow_def local_flow_axioms_def by fastforce+
next
  show "picard_ivp (\<lambda>t. f) T S L 0"
    using assms unfolding local_flow_def local_flow_axioms_def 
      picard_ivp_def ubc_definitions apply safe
       apply(meson Sigma_mono continuous_on_subset subsetI)
      apply(simp_all add: subset_eq)
    by fastforce
qed

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

theorem is_group_action:
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
  using assms unfolding global_flow_def local_flow_def picard_ivp_def by simp

subsubsection{* Example *}

text{* Finally, we exemplify a procedure for introducing pairs of vector fields and their respective 
flows using the previous locales. *}

lemma constant_is_picard_ivp:"0 \<le> t \<Longrightarrow> picard_ivp (\<lambda>t s. c) {0..t} UNIV (1 / (t + 1)) 0"
  unfolding picard_ivp_def by(simp add: nonempty_set_def lipschitz_on_def, clarsimp, simp)

lemma line_solves_constant:"((\<lambda> \<tau>. x + \<tau> *\<^sub>R c) solves_ode (\<lambda>t s. c)) {0..t} UNIV"
  unfolding solves_ode_def apply simp
  apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(190))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma line_is_local_flow:
"0 \<le> t \<Longrightarrow> local_flow (\<lambda> s. (c::'a::banach)) {0..t} UNIV (1/(t + 1)) (\<lambda> t x. x + t *\<^sub>R c)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using constant_is_picard_ivp apply blast
  using line_solves_constant by auto

end