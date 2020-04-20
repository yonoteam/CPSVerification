(*  Title:       Preliminaries for hybrid systems verification
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Hybrid Systems Preliminaries \<close>

text \<open>Hybrid systems combine continuous dynamics with discrete control. This section contains 
auxiliary lemmas for verification of hybrid systems.\<close>

theory hs_prelims
  imports "Ordinary_Differential_Equations.Picard_Lindeloef_Qualitative"
begin

no_notation has_vderiv_on (infix "(has'_vderiv'_on)" 50)

notation has_derivative ("(1(D _ \<mapsto> (_))/ _)" [65,65] 61)
     and has_vderiv_on ("(1 D _ = (_)/ on _)" [65,65] 61)
     and norm ("(1\<parallel>_\<parallel>)" [65] 61)

subsection\<open> Functions \<close>

lemma nemptyE: "T \<noteq> {} \<Longrightarrow> \<exists>t. t \<in> T"
  by blast

lemma funcset_UNIV: "f \<in> A \<rightarrow> UNIV"
  by auto

lemma case_of_fst[simp]: "(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> fst) x)"
  by auto

lemma case_of_snd[simp]: "(\<lambda>x. case x of (t, x) \<Rightarrow> f x) = (\<lambda> x. (f \<circ> snd) x)"
  by auto


subsection\<open> Orders \<close>

lemma finite_image_of_finite[simp]:
  fixes f::"'a::finite \<Rightarrow> 'b"
  shows "finite {x. \<exists>i. x = f i}"
  using finite_Atleast_Atmost_nat by force

lemma cSup_eq_linorder:
  fixes c::"'a::conditionally_complete_linorder"
  assumes "X \<noteq> {}" and "\<forall>x \<in> X. x \<le> c" 
    and "bdd_above X" and "\<forall>y<c. \<exists>x\<in>X. y < x"
  shows "Sup X = c"
  by (meson assms cSup_least less_cSup_iff less_le)


subsection\<open> Real numbers \<close>

lemma ge_one_sqrt_le: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis basic_trans_rules(23) monoid_mult_class.power2_eq_square more_arith_simps(6) 
      mult_left_mono real_sqrt_le_iff' zero_le_one)

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  by (metis (full_types) abs_of_nat le_square of_nat_mono of_nat_mult real_sqrt_abs2 real_sqrt_le_iff)

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

lemma in_real_ivl_eqs:
  "(t \<in> cball t0 r) = (\<bar>t - t0\<bar> \<le> r)" 
  "(t \<in> ball t0 r) = (\<bar>t - t0\<bar> < r)"
  using dist_real_def by auto

lemma open_cballE: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>e>0. cball t\<^sub>0 e \<subseteq> T"
  using open_contains_cball by blast

lemma open_ballE: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>e>0. ball t\<^sub>0 e \<subseteq> T"
  using open_contains_ball by blast

lemma norm_rotate_simps[simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"  
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq) 
  thus "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: add.commute add.left_commute power2_diff power2_sum)
qed


subsection \<open> Single variable derivatives \<close>

\<comment> \<open>Theorems in the list below are shaped like those on ``derivative\_eq\_intros''. \<close>

named_theorems poly_derivatives "compilation of optimised miscellaneous derivative rules."

declare has_vderiv_on_const [poly_derivatives]
    and has_vderiv_on_id [poly_derivatives]
    and derivative_intros(189) [poly_derivatives]
    and derivative_intros(190) [poly_derivatives]
    and derivative_intros(192) [poly_derivatives]

text \<open>Below, we consistently name lemmas showing that @{term "f'"} is the derivative of @{term "f"} 
by starting with ``has\dots''. Moreover, if they use the predicate ``has\_derivative\_at'',  we add 
them to the list ``derivative\_intros''. Otherwise, if lemmas have an implicit @{term "g"} where 
@{term "g = f'"}, we start their names with ``vderiv'' and end them with ``intro''.\<close>

lemma has_derivative_exp_scaleRl[derivative_intros]:
  fixes f::"real \<Rightarrow> real" (* by Fabian Immler and Johannes Hölzl *)
  assumes "D f \<mapsto> f' at t within T"
  shows "D (\<lambda>t. exp (f t *\<^sub>R A)) \<mapsto> (\<lambda>h. f' h *\<^sub>R (exp (f t *\<^sub>R A) * A)) at t within T"
proof -
  from assms have "bounded_linear f'" by auto
  with real_bounded_linear obtain m where f': "f' = (\<lambda>h. h * m)" by blast
  show ?thesis
    using vector_diff_chain_within[OF _ exp_scaleR_has_vector_derivative_right, of f m t T A] 
      assms f' by (auto simp: has_vector_derivative_def o_def)
qed

lemma has_vector_derivative_mult_const[derivative_intros]:
  "((*) a has_vector_derivative a) F"
  by (auto intro: derivative_eq_intros)

lemma has_derivative_mult_const[derivative_intros]: "D (*) a \<mapsto> (\<lambda>t. t *\<^sub>R a) F"
  using has_vector_derivative_mult_const unfolding has_vector_derivative_def by simp

lemma has_vderiv_on_composeI: 
  assumes "D f = f' on g ` T" 
    and " D g = g' on T"
    and "h = (\<lambda>t. g' t *\<^sub>R f' (g t))"
  shows "D (\<lambda>t. f (g t)) = h on T"
  apply(subst ssubst[of h], simp)
  using assms has_vderiv_on_compose by auto

lemma has_vderiv_on_mult_const: "D (*) a = (\<lambda>t. a) on T"
  using has_vector_derivative_mult_const unfolding has_vderiv_on_def by auto

lemma has_vderiv_on_divide_cnst: "a \<noteq> 0 \<Longrightarrow> D (\<lambda>t. t/a) = (\<lambda>t. 1/a) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  apply(rule_tac f'1="\<lambda>t. t" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
  by(auto intro: derivative_eq_intros)

lemma has_vderiv_on_power: "n \<ge> 1 \<Longrightarrow> D (\<lambda>t. t ^ n) = (\<lambda>t. n * (t ^ (n - 1))) on T" 
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(16)) auto

lemma has_vderiv_on_exp: "D (\<lambda>t. exp t) = (\<lambda>t. exp t) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def by (auto intro: derivative_intros)

lemma has_vderiv_on_cos_comp: 
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. cos (f t)) = (\<lambda>t. - (f' t) * sin (f t)) on T"
  apply(rule has_vderiv_on_composeI[of "\<lambda>t. cos t"])
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma has_vderiv_on_sin_comp: 
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. sin (f t)) = (\<lambda>t. (f' t) * cos (f t)) on T"
  apply(rule has_vderiv_on_composeI[of "\<lambda>t. sin t"])
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarify
  by(auto intro!: derivative_eq_intros simp: fun_eq_iff)

lemma has_vderiv_on_exp_comp: 
  "D (f::real \<Rightarrow> real) = f' on T \<Longrightarrow> D (\<lambda>t. exp (f t)) = (\<lambda>t. (f' t) * exp (f t)) on T"
  apply(rule has_vderiv_on_composeI[of "\<lambda>t. exp t"])
  by (rule has_vderiv_on_exp, simp_all add: mult.commute)

lemma has_vderiv_on_exp_scaleRl:
  assumes "D f = f' on T"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) = (\<lambda>x. f' x *\<^sub>R exp (f x *\<^sub>R A) * A) on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  by (rule has_derivative_exp_scaleRl, auto simp: fun_eq_iff)

lemma vderiv_uminusI[poly_derivatives]: 
  "D f = f' on T \<Longrightarrow> g = (\<lambda>t. - f' t) \<Longrightarrow> D (\<lambda>t. - f t) = g on T"
  using has_vderiv_on_uminus by auto

lemma vderiv_div_cnstI[poly_derivatives]:
  assumes "(a::real) \<noteq> 0" and "D f = f' on T" and "g = (\<lambda>t. (f' t)/a)"
  shows "D (\<lambda>t. (f t)/a) = g on T"
  apply(rule has_vderiv_on_composeI[of "\<lambda>t. t/a" "\<lambda>t. 1/a"])
  using assms by(auto intro: has_vderiv_on_divide_cnst)

lemma vderiv_npowI[poly_derivatives]:
  fixes f::"real \<Rightarrow> real"
  assumes "n \<ge> 1" and "D f = f' on T" and "g = (\<lambda>t. n * (f' t) * (f t)^(n-1))"
  shows "D (\<lambda>t. (f t)^n) = g on T"
  apply(rule has_vderiv_on_composeI[of "\<lambda>t. t^n"])
  using assms(1) apply(rule has_vderiv_on_power)
  using assms by auto

lemma vderiv_cosI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. - (f' t) * sin (f t))"
  shows "D (\<lambda>t. cos (f t)) = g on T"
  using assms and has_vderiv_on_cos_comp by auto

lemma vderiv_sinI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * cos (f t))"
  shows "D (\<lambda>t. sin (f t)) = g on T"
  using assms and has_vderiv_on_sin_comp by auto

lemma vderiv_expI[poly_derivatives]:
  assumes "D (f::real \<Rightarrow> real) = f' on T" and "g = (\<lambda>t. (f' t) * exp (f t))"
  shows "D (\<lambda>t. exp (f t)) = g on T"
  using assms and has_vderiv_on_exp_comp by auto

lemma vderiv_on_exp_scaleRlI[poly_derivatives]:
  assumes "D f = f' on T" and "g' = (\<lambda>x. f' x *\<^sub>R exp (f x *\<^sub>R A) * A)"
  shows "D (\<lambda>x. exp (f x *\<^sub>R A)) = g' on T"
  using has_vderiv_on_exp_scaleRl assms by simp

\<comment> \<open>Automatically generated derivative rules from this subsection: \<close>

thm derivative_eq_intros(140,141,142)

\<comment> \<open>Examples for checking derivatives\<close>

lemma "D (\<lambda>t. a * t\<^sup>2 / 2 + v * t + x) = (\<lambda>t. a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "D (\<lambda>t. v * t - a * t\<^sup>2 / 2 + x) = (\<lambda>x. v - a * x) on T"
  by(auto intro!: poly_derivatives)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. a5 * t^5 + a3 * (t^3 / c) - a2 * exp (t^2) + a1 * cos t + a0) = 
  (\<lambda>t. 5 * a5 * t^4 + 3 * a3 * (t^2 / c) - 2 * a2 * t * exp (t^2) - a1 * sin t) on T"
  by(auto intro!: poly_derivatives)

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. - a3 * exp (t^3 / c) + a1 * sin t + a2 * t^2) = 
  (\<lambda>t. a1 * cos t + 2 * a2 * t - 3 * a3 * t^2 / c * exp (t^3 / c)) on T"
  apply(intro poly_derivatives)
  using poly_derivatives(1,2) by force+

lemma "c \<noteq> 0 \<Longrightarrow> D (\<lambda>t. exp (a * sin (cos (t^4) / c))) = 
(\<lambda>t. - 4 * a * t^3 * sin (t^4) / c * cos (cos (t^4) / c) * exp (a * sin (cos (t^4) / c))) on T"
  apply(intro poly_derivatives)
  using poly_derivatives(1,2) by force+


subsection\<open> Filters \<close>

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
  shows "eventually (\<lambda>t. \<forall>i. P i t) F"
proof(unfold eventually_def)
  let ?F = "Rep_filter F"
  have obs: "\<forall>i. ?F (P i)" 
    using h by auto
  have "?F (\<lambda>t. \<forall>i \<in> UNIV. P i t)"
    apply(rule finite_induct) 
    by(auto intro: eventually_conj simp: obs h)
  thus "?F (\<lambda>t. \<forall>i. P i t)"
    by simp
qed

lemma eventually_all_finite_mono:
  fixes P :: "('a::finite) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes h1: "\<forall>i. eventually (P i) F"
      and h2: "\<forall>t. (\<forall>i. (P i t)) \<longrightarrow> Q t"
  shows "eventually Q F"
proof-
  have "eventually (\<lambda>t. \<forall>i. P i t) F"
    using h1 eventually_all_finite2 by blast
  thus "eventually Q F"
    unfolding eventually_def 
    using h2 eventually_mono by auto
qed


subsection\<open> Multivariable derivatives \<close>

lemma frechet_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('m::finite)"
  defines "m \<equiv> real CARD('m)"
  assumes "\<forall>i. ((\<lambda>x. (f x $ i - f x\<^sub>0 $ i - (x - x\<^sub>0) *\<^sub>R f' t $ i) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  shows "((\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
proof(simp add: tendsto_iff, clarify)
  fix \<epsilon>::real assume "0 < \<epsilon>" 
  let "?\<Delta>" = "\<lambda>x. x - x\<^sub>0" and "?\<Delta>f" = "\<lambda>x. f x - f x\<^sub>0"
  let "?P" = "\<lambda>i e x. inverse \<bar>?\<Delta> x\<bar> * (\<parallel>f x $ i - f x\<^sub>0 $ i - ?\<Delta> x *\<^sub>R f' t $ i\<parallel>) < e" 
    and "?Q" = "\<lambda>x. inverse \<bar>?\<Delta> x\<bar> * (\<parallel>?\<Delta>f x - ?\<Delta> x *\<^sub>R f' t\<parallel>) < \<epsilon>"
  have "0 < \<epsilon> / sqrt m" 
    using \<open>0 < \<epsilon>\<close> by (auto simp: assms)
  hence "\<forall>i. eventually (\<lambda>x. ?P i (\<epsilon> / sqrt m) x) (at t within T)"
    using assms unfolding tendsto_iff by simp
  thus "eventually ?Q (at t within T)"
  proof(rule eventually_all_finite_mono, simp add: norm_vec_def L2_set_def, clarify)
    fix x::real
    let ?c = "inverse \<bar>x - x\<^sub>0\<bar>" and "?u x" = "\<lambda>i. f x $ i - f x\<^sub>0 $ i - ?\<Delta> x *\<^sub>R f' t $ i"
    assume hyp:"\<forall>i. ?c * (\<parallel>?u x i\<parallel>) < \<epsilon> / sqrt m"
    hence "\<forall>i. (?c *\<^sub>R (\<parallel>?u x i\<parallel>))\<^sup>2 < (\<epsilon> / sqrt m)\<^sup>2" 
      by (simp add: power_strict_mono)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u x i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m" 
      by (simp add: power_mult_distrib power_divide assms)
    hence "\<forall>i. ?c\<^sup>2 * ((\<parallel>?u x i\<parallel>))\<^sup>2 < \<epsilon>\<^sup>2 / m" 
      by (auto simp: assms)
    also have "({}::'m set) \<noteq> UNIV \<and> finite (UNIV :: 'm set)" 
      by simp
    ultimately have "(\<Sum>i\<in>UNIV. ?c\<^sup>2 * ((\<parallel>?u x i\<parallel>))\<^sup>2) < (\<Sum>(i::'m)\<in>UNIV. \<epsilon>\<^sup>2 / m)"
      by (metis (lifting) sum_strict_mono)
    moreover have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2) = (\<Sum>i\<in>UNIV. ?c\<^sup>2 *  (\<parallel>?u x i\<parallel>)\<^sup>2)"
      using sum_distrib_left by blast
    ultimately have "?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2) < \<epsilon>\<^sup>2" 
      by (simp add: assms)
    hence "sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2)) < sqrt (\<epsilon>\<^sup>2)"
      using real_sqrt_less_iff by blast
    also have "... = \<epsilon>" 
      using \<open>0 < \<epsilon>\<close> by auto 
    moreover have "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2) = sqrt (?c\<^sup>2 * (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2))"
      by (simp add: real_sqrt_mult)   
    ultimately show "?c * sqrt (\<Sum>i\<in>UNIV. (\<parallel>?u x i\<parallel>)\<^sup>2) < \<epsilon>" 
      by simp
  qed
qed

lemma tendsto_norm_bound:
  "\<forall>x. \<parallel>G x - L\<parallel> \<le> \<parallel>F x - L\<parallel> \<Longrightarrow> (F \<longlongrightarrow> L) net \<Longrightarrow> (G \<longlongrightarrow> L) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x - L\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma tendsto_zero_norm_bound:
  "\<forall>x. \<parallel>G x\<parallel> \<le> \<parallel>F x\<parallel> \<Longrightarrow> (F \<longlongrightarrow> 0) net \<Longrightarrow> (G \<longlongrightarrow> 0) net"
  apply(unfold tendsto_iff dist_norm, clarsimp)
  apply(rule_tac P="\<lambda>x. \<parallel>F x\<parallel> < e" in eventually_mono, simp)
  by (rename_tac e z) (erule_tac x=z in allE, simp)

lemma frechet_vec_nth:
  fixes f::"real \<Rightarrow> ('a::real_normed_vector)^'m"
  assumes "((\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  shows "((\<lambda>x. (f x $ i - f x\<^sub>0 $ i - (x - x\<^sub>0) *\<^sub>R f' t $ i) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>)) \<longlongrightarrow> 0) (at t within T)"
  apply(rule_tac F="(\<lambda>x. (f x - f x\<^sub>0 - (x - x\<^sub>0) *\<^sub>R f' t) /\<^sub>R (\<parallel>x - x\<^sub>0\<parallel>))" in tendsto_zero_norm_bound)
   apply(clarsimp, rule mult_left_mono)
    apply (metis Finite_Cartesian_Product.norm_nth_le vector_minus_component vector_scaleR_component)
  using assms by simp_all

lemma has_derivative_vec_lambda:
  fixes f::"real \<Rightarrow> ('a::banach)^('n::finite)"
  assumes "\<forall>i. D (\<lambda>t. f t $ i) \<mapsto> (\<lambda> h. h *\<^sub>R f' t $ i) (at t within T)"
  shows "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' t) at t within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using assms frechet_vec_lambda[of _ f] unfolding has_derivative_def by auto

lemma has_derivative_vec_nth:
  assumes "D f \<mapsto> (\<lambda>h. h *\<^sub>R f' t) at t within T"
  shows "D (\<lambda>t. f t $ i) \<mapsto> (\<lambda>h. h *\<^sub>R f' t $ i) at t within T"
  apply(unfold has_derivative_def, safe)
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  using frechet_vec_nth assms unfolding has_derivative_def by auto

lemma has_vderiv_on_vec_eq[simp]:
  fixes X::"real \<Rightarrow> ('a::banach)^('n::finite)"
  shows "(D X = X' on T) = (\<forall>i. D (\<lambda>t. X t $ i) = (\<lambda>t. X' t $ i) on T)"
  unfolding has_vderiv_on_def has_vector_derivative_def apply safe
  using has_derivative_vec_nth has_derivative_vec_lambda by blast+

end