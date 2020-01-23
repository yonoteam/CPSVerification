(*  Title:       Linear algebra for hybrid systems verification
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Linear algebra for hybrid systems \<close>

text \<open>Linear systems of ordinary differential equations (ODEs) are those whose vector 
fields are linear operators. Broadly speaking, if there is a matrix $A$ such that the 
system $x'\, t = f\, (x\, t)$ can be rewritten as $x'\, t = (A\, t)\cdot (x\, t)+(B\, t)$,
then the system is called linear. The end goal of this section is to prove that every 
linear system of ODEs has a unique solution, and to obtain a characterization of said solution. 
We start by formalising various properties of vector spaces.\<close>

theory hs_prelims_matrices
  imports 
    hs_prelims_dyn_sys
    Affine_Arithmetic.Executable_Euclidean_Space

begin


subsection\<open> Properties of some vector operations \<close>

abbreviation "\<e> k \<equiv> axis k 1"

notation matrix_inv ("_\<^sup>-\<^sup>1" [90])

abbreviation "entries (A::'a^'n^'m) \<equiv> {A $ i $ j | i j. i \<in> UNIV \<and> j \<in> UNIV}"

lemma finite_sum_univ_singleton: "(sum g UNIV) = sum g {i} + sum g (UNIV - {i})" for i :: "'a::finite"
  by (metis add.commute finite_class.finite_UNIV sum.subset_diff top_greatest)

lemma kronecker_delta_simps[simp]:
  fixes q :: "('a::semiring_0)" and i :: "'n::finite"
  shows "(\<Sum>j\<in>UNIV. f j * (if j = i then q else 0)) = f i * q"
    and "(\<Sum>j\<in>UNIV. f j * (if i = j then q else 0)) = f i * q"
    and "(\<Sum>j\<in>UNIV. (if i = j then q else 0) * f j) = q * f i"
    and "(\<Sum>j\<in>UNIV. (if j = i then q else 0) * f j) = q * f i"
  by (auto simp: finite_sum_univ_singleton[of _ i])

lemma sum_axis[simp]:
  fixes q :: "('a::semiring_0)"
  shows "(\<Sum>j\<in>UNIV. f j * axis i q $ j) = f i * q"
    and "(\<Sum>j\<in>UNIV. axis i q $ j * f j) = q * f i"
  unfolding axis_def by(auto simp: vec_eq_iff)

lemma sum_scalar_nth_axis: "sum (\<lambda>i. (x $ i) *s \<e> i) UNIV = x" for x :: "('a::semiring_1)^'n"
  unfolding vec_eq_iff axis_def by simp

lemma scalar_eq_scaleR[simp]: "c *s x = c *\<^sub>R x"
  unfolding vec_eq_iff by simp

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma vec_mult_inner: "(A *v v) \<bullet> w = v \<bullet> (transpose A *v w)" for A :: "real ^'n^'n"
  unfolding matrix_vector_mult_def transpose_def inner_vec_def
  apply(simp add: sum_distrib_right sum_distrib_left)
  apply(subst sum.swap)
  apply(subgoal_tac "\<forall>i j. A $ i $ j * v $ j * w $ i = v $ j * (A $ i $ j * w $ i)")
  by presburger simp

lemma uminus_axis_eq[simp]: "- axis i k = axis i (-k)" for k :: "'a::ring"
  unfolding axis_def by(simp add: vec_eq_iff)

lemma norm_axis_eq[simp]: "\<parallel>axis i k\<parallel> = \<parallel>k\<parallel>"
proof(simp add: axis_def norm_vec_def L2_set_def)
  let "?\<delta>\<^sub>K" = "\<lambda>i j k. if i = j then k else 0" 
  have "(\<Sum>j\<in>UNIV. (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) = (\<Sum>j\<in>{i}. (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) + (\<Sum>j\<in>(UNIV-{i}). (\<parallel>(?\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2)"
    using finite_sum_univ_singleton by blast 
  also have "... = (\<parallel>k\<parallel>)\<^sup>2" by simp
  finally show "sqrt (\<Sum>j\<in>UNIV. (norm (if j = i then k else 0))\<^sup>2) = norm k" by simp
qed

lemma matrix_axis_0: 
  fixes A :: "('a::idom)^'n^'m"
  assumes "k \<noteq> 0 " and h:"\<forall>i. (A *v (axis i k)) = 0"
  shows "A = 0"  
proof-
  {fix i::'n
    have "0 = (\<Sum>j\<in>UNIV. (axis i k) $ j *s column j A)" 
      using h matrix_mult_sum[of A "axis i k"] by simp
    also have "... = k *s column i A" 
      by(simp add: axis_def vector_scalar_mult_def column_def vec_eq_iff mult.commute)
    finally have "k *s column i A = 0"
      unfolding axis_def by simp
    hence "column i A = 0" 
      using vector_mul_eq_0 \<open>k \<noteq> 0\<close> by blast}
  thus "A = 0" 
    unfolding column_def vec_eq_iff by simp
qed

lemma scaleR_norm_sgn_eq: "(\<parallel>x\<parallel>) *\<^sub>R sgn x = x"
  by (metis divideR_right norm_eq_zero scale_eq_0_iff sgn_div_norm)

lemma vector_scaleR_commute: "A *v c *\<^sub>R x = c *\<^sub>R (A *v x)" for x :: "('a::real_normed_algebra_1)^'n"
  unfolding scaleR_vec_def matrix_vector_mult_def by(auto simp: vec_eq_iff scaleR_right.sum)

lemma scaleR_vector_assoc: "c *\<^sub>R (A *v x) = (c *\<^sub>R A) *v x" for x :: "('a::real_normed_algebra_1)^'n"
  unfolding matrix_vector_mult_def by(auto simp: vec_eq_iff scaleR_right.sum)

lemma mult_norm_matrix_sgn_eq:
  fixes x :: "('a::real_normed_algebra_1)^'n"
  shows "(\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>) = \<parallel>A *v x\<parallel>"
proof-
  have "\<parallel>A *v x\<parallel> = \<parallel>A *v ((\<parallel>x\<parallel>) *\<^sub>R sgn x)\<parallel>"
    by(simp add: scaleR_norm_sgn_eq)
  also have "... = (\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>)"
    by(simp add: vector_scaleR_commute)
  finally show ?thesis ..
qed


subsection\<open> Matrix norms \<close>

text\<open> Here we develop the foundations for obtaining the Lipschitz constant for every system of ODEs 
of the form  @{term "x' t = A *v (x t)"}. We derive some properties of two matrix norms.\<close>


subsubsection\<open> Matrix operator norm \<close>

abbreviation op_norm :: "('a::real_normed_algebra_1)^'n^'m \<Rightarrow> real" ("(1\<parallel>_\<parallel>\<^sub>o\<^sub>p)" [65] 61)
  where "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<equiv> onorm (\<lambda>x. A *v x)"

lemma norm_matrix_bound:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
proof-
  fix x :: "('a, 'n) vec" assume "\<parallel>x\<parallel> = 1"
  hence xi_le1:"\<And>i. \<parallel>x $ i\<parallel> \<le> 1" 
    by (metis Finite_Cartesian_Product.norm_nth_le) 
  {fix j::'m 
    have "\<parallel>(\<Sum>i\<in>UNIV. A $ j $ i * x $ i)\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>A $ j $ i * x $ i\<parallel>)"
      using norm_sum by blast
    also have "... \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * (\<parallel>x $ i\<parallel>))"
      by (simp add: norm_mult_ineq sum_mono)
    also have "... \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * 1)"
      using xi_le1 by (simp add: sum_mono mult_left_le)
    finally have "\<parallel>(\<Sum>i\<in>UNIV. A $ j $ i * x $ i)\<parallel> \<le> (\<Sum>i\<in>UNIV. (\<parallel>A $ j $ i\<parallel>) * 1)" by simp}
  hence "\<And>j. \<parallel>(A *v x) $ j\<parallel> \<le> ((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j"
    unfolding matrix_vector_mult_def by simp
  hence "(\<Sum>j\<in>UNIV. (\<parallel>(A *v x) $ j\<parallel>)\<^sup>2) \<le> (\<Sum>j\<in>UNIV. (\<parallel>((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j\<parallel>)\<^sup>2)"
    by (metis (mono_tags, lifting) norm_ge_zero power2_abs power_mono real_norm_def sum_mono) 
  thus "\<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
    unfolding norm_vec_def L2_set_def by simp
qed

lemma onorm_set_proptys:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "bounded (range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>)))"
    and "bdd_above (range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>)))"
    and "(range (\<lambda>x. (\<parallel>A *v x\<parallel>) / (\<parallel>x\<parallel>))) \<noteq> {}"
  unfolding bounded_def bdd_above_def image_def dist_real_def apply(rule_tac x=0 in exI)
  by (rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI, clarsimp,
      subst mult_norm_matrix_sgn_eq[symmetric], clarsimp,
      rule_tac x="sgn _" in norm_matrix_bound, simp add: norm_sgn)+ force

lemma op_norm_set_proptys:
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "bounded {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "bdd_above {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "{\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<noteq> {}"
  unfolding bounded_def bdd_above_def apply safe
    apply(rule_tac x=0 in exI, rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI)
    apply(force simp: norm_matrix_bound dist_real_def)
   apply(rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI, force simp: norm_matrix_bound)
  using ex_norm_eq_1 by blast

lemma op_norm_def: 
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>A\<parallel>\<^sub>o\<^sub>p = Sup {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
  apply(rule antisym[OF onorm_le cSup_least[OF op_norm_set_proptys(3)]])
   apply(case_tac "x = 0", simp)
   apply(subst mult_norm_matrix_sgn_eq[symmetric], simp)
   apply(rule cSup_upper[OF _ op_norm_set_proptys(2)])
   apply(force simp: norm_sgn)
  unfolding onorm_def apply(rule cSup_upper[OF _ onorm_set_proptys(2)])
  by (simp add: image_def, clarsimp) (metis div_by_1)

lemma norm_matrix_le_op_norm: "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  apply(unfold onorm_def, rule cSup_upper[OF _ onorm_set_proptys(2)])
  unfolding image_def by (clarsimp, rule_tac x=x in exI) simp

lemma op_norm_ge_0: "0 \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  using ex_norm_eq_1 norm_ge_zero norm_matrix_le_op_norm basic_trans_rules(23) by blast

lemma norm_sgn_le_op_norm: "\<parallel>A *v sgn x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  by(cases "x=0", simp_all add: norm_sgn norm_matrix_le_op_norm op_norm_ge_0)

lemma norm_matrix_le_mult_op_norm: "\<parallel>A *v x\<parallel> \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)"
proof-
  have "\<parallel>A *v x\<parallel> = (\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>)"
    by(simp add: mult_norm_matrix_sgn_eq)
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)"
    using norm_sgn_le_op_norm[of A] by (simp add: mult_mono')
  finally show ?thesis by simp
qed

lemma blin_matrix_vector_mult: "bounded_linear ((*v) A)" for A :: "('a::real_normed_algebra_1)^'n^'m"
  by (unfold_locales) (auto intro: norm_matrix_le_mult_op_norm simp: 
      mult.commute matrix_vector_right_distrib vector_scaleR_commute)

lemma op_norm_eq_0: "(\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0) = (A = 0)" for A :: "('a::real_normed_field)^'n^'m"
  unfolding onorm_eq_0[OF blin_matrix_vector_mult] using matrix_axis_0[of 1 A] by fastforce

lemma op_norm0: "\<parallel>(0::('a::real_normed_field)^'n^'m)\<parallel>\<^sub>o\<^sub>p = 0"
  using op_norm_eq_0[of 0] by simp
                  
lemma op_norm_triangle: "\<parallel>A + B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) + (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
  using onorm_triangle[OF blin_matrix_vector_mult[of A] blin_matrix_vector_mult[of B]]
    matrix_vector_mult_add_rdistrib[symmetric, of A _ B] by simp

lemma op_norm_scaleR: "\<parallel>c *\<^sub>R A\<parallel>\<^sub>o\<^sub>p = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
  unfolding onorm_scaleR[OF blin_matrix_vector_mult, symmetric] scaleR_vector_assoc ..

lemma op_norm_matrix_matrix_mult_le: 
  fixes A :: "('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>A ** B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
proof(rule onorm_le)
  have "0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
    by(rule onorm_pos_le[OF blin_matrix_vector_mult])
  fix x have "\<parallel>A ** B *v x\<parallel> = \<parallel>A *v (B *v x)\<parallel>"
    by (simp add: matrix_vector_mul_assoc)
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B *v x\<parallel>)"
    by (simp add: norm_matrix_le_mult_op_norm[of _ "B *v x"])
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * ((\<parallel>B\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>))"
    using norm_matrix_le_mult_op_norm[of B x] \<open>0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)\<close> mult_left_mono by blast
  finally show "\<parallel>A ** B *v x\<parallel> \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" 
    by simp
qed

lemma norm_matrix_vec_mult_le_transpose:
  "\<parallel>x\<parallel> = 1 \<Longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" for A :: "real^'n^'n"
proof-
  assume "\<parallel>x\<parallel> = 1"
  have "(\<parallel>A *v x\<parallel>)\<^sup>2 = (A *v x) \<bullet> (A *v x)"
    using dot_square_norm[of "(A *v x)"] by simp
  also have "... = x \<bullet> (transpose A *v (A *v x))"
    using vec_mult_inner by blast
  also have "... \<le> (\<parallel>x\<parallel>) * (\<parallel>transpose A *v (A *v x)\<parallel>)"
    using norm_cauchy_schwarz by blast
  also have "... \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    apply(subst matrix_vector_mul_assoc) 
    using norm_matrix_le_mult_op_norm[of "transpose A ** A" x]
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close>) 
  finally have "((\<parallel>A *v x\<parallel>))^2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    by linarith
  thus "(\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close> real_le_rsqrt)
qed

lemma op_norm_le_sum_column: "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)" for A :: "real^'n^'m"  
proof(unfold op_norm_def, rule cSup_least[OF op_norm_set_proptys(3)], clarsimp)
  fix x :: "real^'n" assume x_def:"\<parallel>x\<parallel> = 1" 
  hence x_hyp:"\<And>i. \<parallel>x $ i\<parallel> \<le> 1"
    by (simp add: norm_bound_component_le_cart)
  have "(\<parallel>A *v x\<parallel>) = \<parallel>(\<Sum>i\<in>UNIV. x $ i *s column i A)\<parallel>"
    by(subst matrix_mult_sum[of A], simp)
  also have "... \<le> (\<Sum>i\<in>UNIV. \<parallel>x $ i *s column i A\<parallel>)"
    by (simp add: sum_norm_le)
  also have "... = (\<Sum>i\<in>UNIV. (\<parallel>x $ i\<parallel>) * (\<parallel>column i A\<parallel>))"
    by (simp add: mult_norm_matrix_sgn_eq)
  also have "... \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)"
    using x_hyp by (simp add: mult_left_le_one_le sum_mono) 
  finally show "\<parallel>A *v x\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)" .
qed

lemma op_norm_le_transpose: "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> \<parallel>transpose A\<parallel>\<^sub>o\<^sub>p" for A :: "real^'n^'n"  
proof-
  have obs:"\<forall>x. \<parallel>x\<parallel> = 1 \<longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    using norm_matrix_vec_mult_le_transpose by blast
  have "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p))"
    using obs apply(unfold op_norm_def)
    by (rule cSup_least[OF op_norm_set_proptys(3)]) clarsimp
  hence "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)"
    using power_mono[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)" _ 2] op_norm_ge_0 by force
  also have "... \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
    using op_norm_matrix_matrix_mult_le by blast
  finally have "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"  by linarith
  thus "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p)"
    using sq_le_cancel[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)"] op_norm_ge_0 by metis
qed


subsubsection\<open> Matrix maximum norm \<close>

abbreviation max_norm :: "real^'n^'m \<Rightarrow> real" ("(1\<parallel>_\<parallel>\<^sub>m\<^sub>a\<^sub>x)" [65] 61)
  where "\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x \<equiv> Max (\<P> abs (entries A))"

lemma max_norm_def: "\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x = Max {\<bar>A $ i $ j\<bar>|i j. i\<in>UNIV \<and> j\<in>UNIV}"
  by (simp add: image_def, rule arg_cong[of _ _ Max], blast)

lemma max_norm_set_proptys: "finite {\<bar>A $ i $ j\<bar> |i j. i \<in> UNIV \<and> j \<in> UNIV}" (is "finite ?X")
proof-
  have "\<And>i. finite {\<bar>A $ i $ j\<bar> | j. j \<in> UNIV}"
    using finite_Atleast_Atmost_nat by fastforce
  hence "finite (\<Union>i\<in>UNIV. {\<bar>A $ i $ j\<bar> | j. j \<in> UNIV})" (is "finite ?Y")
    using finite_class.finite_UNIV by blast
  also have "?X \<subseteq> ?Y" by auto
  ultimately show ?thesis 
    using finite_subset by blast
qed

lemma max_norm_ge_0: "0 \<le> \<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x"
  unfolding max_norm_def apply(rule order.trans[OF abs_ge_zero[of "A $ _ $ _"] Max_ge])
  using max_norm_set_proptys by auto

lemma op_norm_le_max_norm:
  fixes A :: "real^('n::finite)^('m::finite)"
  shows "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> real CARD('m) * real CARD('n) * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
  apply(rule onorm_le_matrix_component)
  unfolding max_norm_def by(rule Max_ge[OF max_norm_set_proptys]) force


subsection\<open> Picard Lindeloef for linear systems \<close>

text\<open> Now we prove our first objective. First we obtain the Lipschitz constant for linear systems
of ODEs, and then we prove that IVPs arising from these satisfy the conditions for Picard-Lindeloef 
theorem (hence, they have a unique solution). \<close>

lemma continuous_on_matrix_vector_multl:
  fixes A :: "real \<Rightarrow> real^'n^'m"
  assumes "\<forall>t \<in> T. \<forall>\<epsilon> > 0. \<exists> \<delta> > 0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p \<le> \<epsilon>"
  shows "continuous_on T (\<lambda>t. A t *v s)"
proof(rule continuous_onI, simp add: dist_norm)
  fix e t::real assume "0 < e" and "t \<in> T"
  let ?\<epsilon> = "e/(\<parallel>(if s = 0 then 1 else s)\<parallel>)"
  have "?\<epsilon> > 0"
    using \<open>0 < e\<close> by simp 
  then obtain \<delta> where dHyp: "\<delta> > 0 \<and> (\<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p \<le> ?\<epsilon>)"
    using assms \<open>t \<in> T\<close> unfolding dist_norm by fastforce
  {fix \<tau> assume "\<tau> \<in> T" and "\<bar>\<tau> - t\<bar> < \<delta>"
    have obs: "?\<epsilon> * (\<parallel>s\<parallel>) = (if s = 0 then 0 else e)"
      by auto
    have "\<parallel>A \<tau> *v s - A t *v s\<parallel> = \<parallel>(A \<tau> - A t) *v s\<parallel>"
      by (simp add: matrix_vector_mult_diff_rdistrib)      
    also have "... \<le> (\<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p) * (\<parallel>s\<parallel>)"
      using norm_matrix_le_mult_op_norm by blast
    also have "... \<le> ?\<epsilon> * (\<parallel>s\<parallel>)"
      using dHyp \<open>\<tau> \<in> T\<close> \<open>\<bar>\<tau> - t\<bar> < \<delta>\<close> mult_right_mono norm_ge_zero by blast 
    finally have "\<parallel>A \<tau> *v s - A t *v s\<parallel> \<le> e"
      by (subst (asm) obs) (metis (mono_tags, hide_lams) \<open>0 < e\<close> less_eq_real_def order_trans)}
  thus "\<exists>d>0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < d \<longrightarrow> \<parallel>A \<tau> *v s - A t *v s\<parallel> \<le> e"
    using dHyp by blast
qed

lemma lipschitz_cond_affine:
  fixes A :: "real \<Rightarrow> real^'n^'m" and T::"real set"
  defines "L \<equiv> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
  assumes "t \<in> T" and "bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
  shows "\<parallel>A t *v x - A t *v y\<parallel> \<le> L * (\<parallel>x - y\<parallel>)"
proof-
  have obs: "\<parallel>A t\<parallel>\<^sub>o\<^sub>p \<le> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T}"
    apply(rule cSup_upper)
    using continuous_on_subset assms by (auto simp: dist_norm)
  have "\<parallel>A t *v x - A t *v y\<parallel> = \<parallel>A t *v (x - y)\<parallel>"
    by (simp add: matrix_vector_mult_diff_distrib)
  also have "... \<le> (\<parallel>A t\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x - y\<parallel>)"
    using norm_matrix_le_mult_op_norm by blast
  also have "... \<le> Sup {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> T} * (\<parallel>x - y\<parallel>)"
    using obs mult_right_mono norm_ge_zero by blast 
  finally show "\<parallel>A t *v x - A t *v y\<parallel> \<le> L * (\<parallel>x - y\<parallel>)"
    unfolding assms .
qed

lemma local_lipschitz_affine:
  fixes A :: "real \<Rightarrow> real^'n^'n"
  assumes "open T" and "open S" 
    and Ahyp: "\<And>\<tau> \<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. t \<in> cball \<tau> \<epsilon>}"
  shows "local_lipschitz T S (\<lambda>t s. A t *v s + B t)"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp)
  fix s t assume "s \<in> S" and "t \<in> T"
  then obtain e1 e2 where "cball t e1 \<subseteq> T" and "cball s e2 \<subseteq> S" and "min e1 e2 > 0"
    using open_cballE[OF _ \<open>open T\<close>] open_cballE[OF _ \<open>open S\<close>] by force
  hence obs: "cball t (min e1 e2) \<subseteq> T"
    by auto
  let ?L = "Sup {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
  have "\<parallel>A t\<parallel>\<^sub>o\<^sub>p \<in> {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
    using \<open>min e1 e2 > 0\<close> by auto
  moreover have bdd: "bdd_above {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)}"
    by (rule Ahyp, simp only: \<open>min e1 e2 > 0\<close>, simp_all add: \<open>t \<in> T\<close> obs)
  moreover have "Sup {\<parallel>A \<tau>\<parallel>\<^sub>o\<^sub>p |\<tau>. \<tau> \<in> cball t (min e1 e2)} \<ge> 0"
    apply(rule order.trans[OF op_norm_ge_0[of "A t"]])
    by (rule cSup_upper[OF calculation])
  moreover have "\<forall>x\<in>cball s (min e1 e2) \<inter> S. \<forall>y\<in>cball s (min e1 e2) \<inter> S. 
    \<forall>\<tau>\<in>cball t (min e1 e2) \<inter> T. dist (A \<tau> *v x) (A \<tau> *v y) \<le> ?L * dist x y"
    apply(clarify, simp only: dist_norm, rule lipschitz_cond_affine)
    using \<open>min e1 e2 > 0\<close> bdd by auto
  ultimately show "\<exists>e>0. \<exists>L. \<forall>t\<in>cball t e \<inter> T. 0 \<le> L \<and> 
    (\<forall>x\<in>cball s e \<inter> S. \<forall>y\<in>cball s e \<inter> S. dist (A t *v x) (A t *v y) \<le> L * dist x y)"
    using \<open>min e1 e2 > 0\<close> by blast
qed

lemma picard_lindeloef_affine:
  fixes A :: "real \<Rightarrow> real^'n^'n"
  assumes Ahyp: "\<forall>t \<in> T. \<forall>\<epsilon> > 0. \<exists> \<delta> > 0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>A \<tau> - A t\<parallel>\<^sub>o\<^sub>p \<le> \<epsilon>"
      and "\<And>\<tau> \<epsilon>. \<tau> \<in> T \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> bdd_above {\<parallel>A t\<parallel>\<^sub>o\<^sub>p |t. dist \<tau> t \<le> \<epsilon>}"
      and Bhyp: "continuous_on T B" and "open S" 
      and "t\<^sub>0 \<in> T" and Thyp: "open T" "is_interval T" 
    shows "picard_lindeloef (\<lambda> t s. A t *v s + B t) T S t\<^sub>0"
  apply(unfold_locales, simp_all add: assms, clarsimp)
  apply(rule continuous_on_add[OF continuous_on_matrix_vector_multl[OF Ahyp] Bhyp])
  by (rule local_lipschitz_affine) (simp_all add: assms)

lemma picard_lindeloef_affine_constant:
  fixes A :: "real^'n^'n"
  shows "picard_lindeloef (\<lambda> t s. A *v s + B) UNIV UNIV 0"
  using picard_lindeloef_affine[of _ "\<lambda>t. A" "\<lambda>t. B"]
  by (simp only: diff_self op_norm0, auto)

lemma picard_lindeloef_linear_constant:
  fixes A :: "real^'n^'n"
  shows "picard_lindeloef (\<lambda> t. (*v) A) UNIV UNIV 0"
  using picard_lindeloef_affine_constant[of A 0] by force


subsection\<open> Diagonalization \<close>

lemma invertibleI:
  assumes "A ** B = mat 1" and "B ** A = mat 1"
  shows "invertible A"
  using assms unfolding invertible_def by auto

lemma invertibleD[simp]:
  assumes "invertible A" 
  shows "A\<^sup>-\<^sup>1 ** A = mat 1" and "A ** A\<^sup>-\<^sup>1 = mat 1"
  using assms unfolding matrix_inv_def invertible_def
  by  (simp_all add: verit_sko_ex')

lemma matrix_inv_unique:
  assumes "A ** B = mat 1" and "B ** A = mat 1"
  shows "A\<^sup>-\<^sup>1 = B"
  by (metis assms invertibleD(2) invertibleI matrix_mul_assoc matrix_mul_lid)

lemma invertible_matrix_inv: "invertible A \<Longrightarrow> invertible (A\<^sup>-\<^sup>1)"
  using invertibleD(1) invertibleD(2) invertibleI by blast

lemma matrix_inv_idempotent[simp]: "invertible A \<Longrightarrow> A\<^sup>-\<^sup>1\<^sup>-\<^sup>1 = A"
  using invertibleD matrix_inv_unique by blast
  
lemma matrix_inv_matrix_mul:
  assumes "invertible A" and "invertible B"
  shows "(A ** B)\<^sup>-\<^sup>1 = B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1"
proof(rule matrix_inv_unique)
  have "A ** B ** (B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1) = A ** (B ** B\<^sup>-\<^sup>1) ** A\<^sup>-\<^sup>1"
    by (simp add: matrix_mul_assoc)
  also have "... = mat 1"
    using assms by simp
  finally show "A ** B ** (B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1) = mat 1" .
next
  have "B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1 ** (A ** B) = B\<^sup>-\<^sup>1 ** (A\<^sup>-\<^sup>1 ** A) ** B"
    by (simp add: matrix_mul_assoc)
  also have "... = mat 1"
    using assms by simp
  finally show "B\<^sup>-\<^sup>1 ** A\<^sup>-\<^sup>1 ** (A ** B) = mat 1" .
qed

lemma mat_inverse_simps[simp]:
  fixes c :: "'a::division_ring"
  assumes "c \<noteq> 0"
  shows "mat (inverse c) ** mat c = mat 1" 
    and "mat c ** mat (inverse c) = mat 1"
  unfolding matrix_matrix_mult_def mat_def by (auto simp: vec_eq_iff assms)

lemma matrix_inv_mat[simp]: "c \<noteq> 0 \<Longrightarrow> (mat c)\<^sup>-\<^sup>1 = mat (inverse c)" for c :: "'a::division_ring"
  by (simp add: matrix_inv_unique)

lemma invertible_mat[simp]: "c \<noteq> 0 \<Longrightarrow> invertible (mat c)" for c :: "'a::division_ring"
  using invertibleI mat_inverse_simps(1) mat_inverse_simps(2) by blast

lemma matrix_inv_mat_1: "(mat (1::'a::division_ring))\<^sup>-\<^sup>1 = mat 1"
  by simp

lemma invertible_mat_1: "invertible (mat (1::'a::division_ring))"
  by simp

definition similar_matrix :: "('a::semiring_1)^'m^'m \<Rightarrow> ('a::semiring_1)^'n^'n \<Rightarrow> bool" (infixr "\<sim>" 25)
  where "similar_matrix A B \<longleftrightarrow> (\<exists> P. invertible P \<and> A = P\<^sup>-\<^sup>1 ** B ** P)"

lemma similar_matrix_refl[simp]: "A \<sim> A" for A :: "'a::division_ring^'n^'n"
  by (unfold similar_matrix_def, rule_tac x="mat 1" in exI, simp)

lemma similar_matrix_simm: "A \<sim> B \<Longrightarrow> B \<sim> A" for A B :: "('a::semiring_1)^'n^'n"
  apply(unfold similar_matrix_def, clarsimp)
  apply(rule_tac x="P\<^sup>-\<^sup>1" in exI, simp add: invertible_matrix_inv)
  by (metis invertible_def matrix_inv_unique matrix_mul_assoc matrix_mul_lid matrix_mul_rid)

lemma similar_matrix_trans: "A \<sim> B \<Longrightarrow> B \<sim> C \<Longrightarrow> A \<sim> C" for A B C :: "('a::semiring_1)^'n^'n"
proof(unfold similar_matrix_def, clarsimp)
  fix P Q
  assume "A = P\<^sup>-\<^sup>1 ** (Q\<^sup>-\<^sup>1 ** C ** Q) ** P" and "B = Q\<^sup>-\<^sup>1 ** C ** Q"
  let ?R = "Q ** P"
  assume inverts: "invertible Q" "invertible P"
  hence "?R\<^sup>-\<^sup>1 = P\<^sup>-\<^sup>1 ** Q\<^sup>-\<^sup>1"
    by (rule matrix_inv_matrix_mul)
  also have "invertible ?R"
    using inverts invertible_mult by blast 
  ultimately show "\<exists>R. invertible R \<and> P\<^sup>-\<^sup>1 ** (Q\<^sup>-\<^sup>1 ** C ** Q) ** P = R\<^sup>-\<^sup>1 ** C ** R"
    by (metis matrix_mul_assoc)
qed

lemma mat_vec_nth_simps[simp]:
  "i = j \<Longrightarrow> mat c $ i $ j = c" 
  "i \<noteq> j \<Longrightarrow> mat c $ i $ j = 0"
  by (simp_all add: mat_def)

definition "diag_mat f = (\<chi> i j. if i = j then f i else 0)"

lemma diag_mat_vec_nth_simps[simp]:
  "i = j \<Longrightarrow> diag_mat f $ i $ j = f i"
  "i \<noteq> j \<Longrightarrow> diag_mat f $ i $ j = 0"
  unfolding diag_mat_def by simp_all

lemma diag_mat_const_eq[simp]: "diag_mat (\<lambda>i. c) = mat c"
  unfolding mat_def diag_mat_def by simp

lemma matrix_vector_mul_diag_mat: "diag_mat f *v s = (\<chi> i. f i * s$i)"
  unfolding diag_mat_def matrix_vector_mult_def by simp

lemma matrix_vector_mul_diag_axis[simp]: "diag_mat f *v (axis i k) = axis i (f i * k)"
  by (simp add: matrix_vector_mul_diag_mat axis_def fun_eq_iff)

lemma matrix_mul_diag_matl: "diag_mat f ** A = (\<chi> i j. f i * A$i$j)"
  unfolding diag_mat_def matrix_matrix_mult_def by simp

lemma matrix_matrix_mul_diag_matr: "A ** diag_mat f = (\<chi> i j. A$i$j * f j)"
  unfolding diag_mat_def matrix_matrix_mult_def apply(clarsimp simp: fun_eq_iff)
  subgoal for i j by (auto simp: finite_sum_univ_singleton[of _ j])
  done

lemma matrix_mul_diag_diag: "diag_mat f ** diag_mat g = diag_mat (\<lambda>i. f i * g i)"
  unfolding diag_mat_def matrix_matrix_mult_def vec_eq_iff by simp

lemma compow_matrix_mul_diag_mat_eq: "((**) (diag_mat f) ^^ n) (mat 1) = diag_mat (\<lambda>i. f i^n)"
  apply(induct n, simp_all add: matrix_mul_diag_matl)
  by (auto simp: vec_eq_iff diag_mat_def)

lemma compow_similar_diag_mat_eq:
  assumes "invertible P" 
      and "A = P\<^sup>-\<^sup>1 ** (diag_mat f) ** P"
    shows "((**) A ^^ n) (mat 1) = P\<^sup>-\<^sup>1 ** (diag_mat (\<lambda>i. f i^n)) ** P"
proof(induct n, simp_all add: assms)
  fix n::nat
  have "P\<^sup>-\<^sup>1 ** diag_mat f ** P ** (P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i ^ n) ** P) = 
  P\<^sup>-\<^sup>1 ** diag_mat f ** diag_mat (\<lambda>i. f i ^ n) ** P" (is "?lhs = _")
    by (metis (no_types, lifting) assms(1) invertibleD(2) matrix_mul_rid matrix_mul_assoc) 
  also have "... = P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i * f i ^ n) ** P" (is "_ = ?rhs")
    by (metis (full_types) matrix_mul_assoc matrix_mul_diag_diag)
  finally show "?lhs = ?rhs" .
qed

lemma compow_similar_diag_mat:
  assumes "A \<sim> (diag_mat f)"
  shows "((**) A ^^ n) (mat 1) \<sim> diag_mat (\<lambda>i. f i^n)"
proof(unfold similar_matrix_def)
  obtain P where "invertible P" and "A = P\<^sup>-\<^sup>1 ** (diag_mat f) ** P"
    using assms unfolding similar_matrix_def by blast
  thus "\<exists>P. invertible P \<and> ((**) A ^^ n) (mat 1) = P\<^sup>-\<^sup>1 ** diag_mat (\<lambda>i. f i ^ n) ** P"
    using compow_similar_diag_mat_eq by blast
qed

(* eigen vector/value needed? *)
definition eigen :: "('a::semiring_1)^'n^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigen A v c = (v \<noteq> 0 \<and> A *v v = c *s v)"

lemma "f i \<noteq> 0 \<Longrightarrow> eigen (diag_mat f) (\<e> i) (f i)"
  unfolding eigen_def apply(simp add: matrix_vector_mul_diag_mat)
  by (simp add: axis_def vector_scalar_mult_def fun_eq_iff)

lemma sqrt_Max_power2_eq_max_abs:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> sqrt (Max {(f i)\<^sup>2|i. i \<in> A}) = Max {\<bar>f i\<bar> |i. i \<in> A}"
proof(rule sym, subst cSup_eq_Max[symmetric], simp_all, subst cSup_eq_Max[symmetric], simp_all)
  assume assms: "finite A" "A \<noteq> {}"
  then obtain i where i_def: "i \<in> A \<and> Sup {(f i)\<^sup>2|i. i \<in> A} = (f i)^2"
    using cSup_finite_ex[of "{(f i)\<^sup>2|i. i \<in> A}"] by auto
  hence lhs: "sqrt (Sup {(f i)\<^sup>2 |i. i \<in> A}) = \<bar>f i\<bar>"
    by simp
  have "finite {(f i)\<^sup>2|i. i \<in> A}"
    using assms by simp
  hence "\<forall>j\<in>A. (f j)\<^sup>2 \<le> (f i)\<^sup>2"
    using i_def cSup_upper[of _ "{(f i)\<^sup>2 |i. i \<in> A}"] by force
  hence "\<forall>j\<in>A. \<bar>f j\<bar> \<le> \<bar>f i\<bar>"
    using abs_le_square_iff by blast
  also have "\<bar>f i\<bar> \<in> {\<bar>f i\<bar> |i. i \<in> A}"
    using i_def by auto
  ultimately show "Sup {\<bar>f i\<bar> |i. i \<in> A} = sqrt (Sup {(f i)\<^sup>2 |i. i \<in> A})"
    using cSup_mem_eq[of "\<bar>f i\<bar>" "{\<bar>f i\<bar> |i. i \<in> A}"] lhs by auto
qed

lemma op_norm_diag_mat_eq: "\<parallel>diag_mat f\<parallel>\<^sub>o\<^sub>p = Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
proof(unfold op_norm_def)
  have obs: "\<And>x i. (f i)\<^sup>2 * (x $ i)\<^sup>2 \<le> Max {(f i)\<^sup>2|i. i \<in> UNIV} * (x $ i)\<^sup>2"
    apply(rule mult_right_mono[OF _ zero_le_power2])
    using le_max_image_of_finite[of "\<lambda>i. (f i)^2"] by auto
  {fix r assume "r \<in> {\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}"
    then obtain x where x_def: "\<parallel>diag_mat f *v x\<parallel> = r \<and> \<parallel>x\<parallel> = 1"
      by blast
    hence "r\<^sup>2 = (\<Sum>i\<in>UNIV. (f i)\<^sup>2 * (x $ i)\<^sup>2)"
      unfolding norm_vec_def L2_set_def matrix_vector_mul_diag_mat apply (simp add: power_mult_distrib)
      by (metis (no_types, lifting) x_def norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
    also have "... \<le> (Max {(f i)\<^sup>2|i. i \<in> UNIV}) * (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
      using obs[of _ x] by (simp add: sum_mono sum_distrib_left)
    also have "... = Max {(f i)\<^sup>2|i. i \<in> UNIV}"
      using x_def by (simp add: norm_vec_def L2_set_def)
    finally have "r \<le> sqrt (Max {(f i)\<^sup>2|i. i \<in> UNIV})"
      using x_def real_le_rsqrt by blast 
    hence "r \<le> Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
      by (subst (asm) sqrt_Max_power2_eq_max_abs[of UNIV f], simp_all)}
  hence 1: "\<forall>x\<in>{\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}. x \<le> Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
    unfolding diag_mat_def by blast
  obtain i where i_def: "Max {\<bar>f i\<bar> |i. i \<in> UNIV} = \<parallel>diag_mat f *v \<e> i\<parallel>"
    using cMax_finite_ex[of "{\<bar>f i\<bar> |i. i \<in> UNIV}"] by force
  hence 2: "\<exists>x\<in>{\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1}. Max {\<bar>f i\<bar> |i. i \<in> UNIV} \<le> x"
    by (metis (mono_tags, lifting) abs_1 mem_Collect_eq norm_axis_eq order_refl real_norm_def)
  show "Sup {\<parallel>diag_mat f *v x\<parallel> |x. \<parallel>x\<parallel> = 1} = Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
    by (rule cSup_eq[OF 1 2])
qed

lemma "CARD('a) \<ge> 2 \<Longrightarrow> \<parallel>diag_mat f\<parallel>\<^sub>m\<^sub>a\<^sub>x = Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
  apply(unfold max_norm_def, simp)
  apply(rule Max_eq_if)
     apply auto
  oops

no_notation matrix_inv ("_\<^sup>-\<^sup>1" [90])
        and similar_matrix (infixr "\<sim>" 25)

subsection\<open> Squared matrices \<close>

text\<open> The general solution for linear systems of ODEs involves the an exponential function. 
Unfortunately, this operation is only available in Isabelle for the type class ``banach''. 
Hence, we define a type of squared matrices and prove that it is an instance of this class.\<close>

typedef 'm sq_mtx = "UNIV::(real^'m^'m) set"
  morphisms to_vec sq_mtx_chi by simp

declare sq_mtx_chi_inverse [simp]
    and to_vec_inverse [simp]

setup_lifting type_definition_sq_mtx

lift_definition sq_mtx_ith :: "'m sq_mtx \<Rightarrow> 'm \<Rightarrow> (real^'m)" (infixl "$$" 90) is vec_nth .

lift_definition sq_mtx_vec_mult :: "'m sq_mtx \<Rightarrow> (real^'m) \<Rightarrow> (real^'m)" (infixl "*\<^sub>V" 90) 
  is matrix_vector_mult .

lift_definition vec_sq_mtx_prod :: "(real^'m) \<Rightarrow> 'm sq_mtx \<Rightarrow> (real^'m)" is vector_matrix_mult .

lift_definition sq_mtx_diag :: "(('m::finite) \<Rightarrow> real) \<Rightarrow> ('m::finite) sq_mtx" (binder "\<d>\<i>\<a>\<g> " 10) is diag_mat .

lift_definition sq_mtx_transpose :: "('m::finite) sq_mtx \<Rightarrow> 'm sq_mtx" ("_\<^sup>\<dagger>") is transpose .

lift_definition sq_mtx_inv :: "('m::finite) sq_mtx \<Rightarrow> 'm sq_mtx" ("_\<^sup>-\<^sup>1" [90]) is matrix_inv .

lift_definition sq_mtx_row :: "'m \<Rightarrow> ('m::finite) sq_mtx \<Rightarrow> real^'m" ("\<r>\<o>\<w>") is row .

lift_definition sq_mtx_col :: "'m \<Rightarrow> ('m::finite) sq_mtx \<Rightarrow> real^'m" ("\<c>\<o>\<l>")  is column .

lemma to_vec_eq_ith: "(to_vec A) $ i = A $$ i"
  by transfer simp

lemma sq_mtx_chi_ith[simp]: "(sq_mtx_chi A) $$ i1 $ i2 = A $ i1 $ i2"
  by transfer simp

lemma sq_mtx_chi_vec_lambda_ith[simp]: "sq_mtx_chi (\<chi> i j. x i j) $$ i1 $ i2 = x i1 i2"
  by(simp add: sq_mtx_ith_def)

lemma sq_mtx_eq_iff:
  shows "(\<And>i. A $$ i = B $$ i) \<Longrightarrow> A = B"
    and "(\<And>i j. A $$ i $ j = B $$ i $ j) \<Longrightarrow> A = B"
  by(transfer, simp add: vec_eq_iff)+

lemma sq_mtx_diag_simps[simp]:
  "i = j \<Longrightarrow> sq_mtx_diag f $$ i $ j = f i"
  "i \<noteq> j \<Longrightarrow> sq_mtx_diag f $$ i $ j = 0"
  "sq_mtx_diag f $$ i = axis i (f i)"
  unfolding sq_mtx_diag_def by (simp_all add: axis_def vec_eq_iff)

lemma sq_mtx_vec_mult_eq: "m *\<^sub>V x = (\<chi> i. sum (\<lambda>j. (m $$ i $ j) * (x $ j)) UNIV)"
  by(transfer, simp add: matrix_vector_mult_def)

lemma sq_mtx_transpose_transpose[simp]:"(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
  by(transfer, simp)

lemma transpose_mult_vec_canon_row[simp]:"(A\<^sup>\<dagger>) *\<^sub>V (\<e> i) = \<r>\<o>\<w> i A"
  by transfer (simp add: row_def transpose_def axis_def matrix_vector_mult_def)

lemma row_ith[simp]:"\<r>\<o>\<w> i A = A $$ i"
  by transfer (simp add: row_def)

lemma mtx_vec_mult_canon:"A *\<^sub>V (\<e> i) = \<c>\<o>\<l> i A" 
  by (transfer, simp add: matrix_vector_mult_basis)

subsubsection\<open> Squared matrices form a real normed vector space \<close>

instantiation sq_mtx :: (finite) ring 
begin

lift_definition plus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(+)" .

lift_definition zero_sq_mtx :: "'a sq_mtx" is "0" .

lift_definition uminus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx" is "uminus" .

lift_definition minus_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(-)" .

lift_definition times_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is "(**)" .

declare plus_sq_mtx.rep_eq [simp]
    and minus_sq_mtx.rep_eq [simp]

instance apply intro_classes
  by(transfer, simp add: algebra_simps matrix_mul_assoc matrix_add_rdistrib matrix_add_ldistrib)+

end

lemma sq_mtx_zero_ith[simp]: "0 $$ i = 0"
  by (transfer, simp)

lemma sq_mtx_zero_nth[simp]: "0 $$ i $ j = 0"
  by transfer simp

lemma sq_mtx_plus_ith[simp]:"(A + B) $$ i = A $$ i + B $$ i"
  by(unfold plus_sq_mtx_def, transfer, simp)

lemma sq_mtx_minus_ith[simp]:"(A - B) $$ i = A $$ i - B $$ i"
  by(unfold minus_sq_mtx_def, transfer, simp)

lemma sq_mtx_plus_diag_diag[simp]: "sq_mtx_diag f + sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i + g i)"
  by (rule sq_mtx_eq_iff(2)) (simp add: axis_def)

lemma sq_mtx_minus_diag_diag[simp]: "sq_mtx_diag f - sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i - g i)"
  by (rule sq_mtx_eq_iff(2)) (simp add: axis_def)

lemma sum_sq_mtx_diag[simp]: "(\<Sum>n<m. sq_mtx_diag (g n)) = (\<d>\<i>\<a>\<g> i. \<Sum>n<m. (g n i))" for m::nat
  by (induct m, simp, rule sq_mtx_eq_iff, simp_all)

lemma sq_mtx_mult_diag_diag[simp]: "sq_mtx_diag f * sq_mtx_diag g = (\<d>\<i>\<a>\<g> i. f i * g i)"
  by (simp add: matrix_mul_diag_diag sq_mtx_diag.abs_eq times_sq_mtx.abs_eq)

lemma sq_mtx_diag_vec_mult: "sq_mtx_diag f *\<^sub>V s = (\<chi> i. f i * s$i)"
  by (simp add: matrix_vector_mul_diag_mat sq_mtx_diag.abs_eq sq_mtx_vec_mult.abs_eq)

lemma sq_mtx_mult_diagl: "sq_mtx_diag f * A = sq_mtx_chi (\<chi> i j. f i * A $$ i $ j)"
  by transfer (simp add: matrix_mul_diag_matl)

lemma sq_mtx_mult_diagr: "A * sq_mtx_diag f = sq_mtx_chi (\<chi> i j. A $$ i $ j * f j)"
  by transfer (simp add: matrix_matrix_mul_diag_matr)

lemma mtx_vec_mult_0l[simp]: "0 *\<^sub>V x = 0"
  by (simp add: sq_mtx_vec_mult.abs_eq zero_sq_mtx_def)

lemma mtx_vec_mult_0r[simp]: "A *\<^sub>V 0 = 0"
  by (transfer, simp)

lemma mtx_vec_mult_add_rdistr:"(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  unfolding plus_sq_mtx_def apply(transfer)
  by (simp add: matrix_vector_mult_add_rdistrib)

lemma mtx_vec_mult_add_rdistl:"A *\<^sub>V (x + y) = A *\<^sub>V x + A *\<^sub>V y"
  unfolding plus_sq_mtx_def apply transfer
  by (simp add: matrix_vector_right_distrib)

lemma mtx_vec_mult_minus_rdistrib:"(A - B) *\<^sub>V x = A *\<^sub>V x - B *\<^sub>V x"
  unfolding minus_sq_mtx_def by(transfer, simp add: matrix_vector_mult_diff_rdistrib)

lemma mtx_vec_mult_minus_ldistrib: "A *\<^sub>V (x - y) =  A *\<^sub>V x -  A *\<^sub>V y"
  by (metis (no_types, lifting) add_diff_cancel diff_add_cancel 
      matrix_vector_right_distrib sq_mtx_vec_mult.rep_eq)

lemma sq_mtx_times_vec_assoc: "(A * B) *\<^sub>V x = A *\<^sub>V (B *\<^sub>V x)"
  by (transfer, simp add: matrix_vector_mul_assoc)

lemma sq_mtx_vec_mult_sum_cols:"A *\<^sub>V x = sum (\<lambda>i. x $ i *\<^sub>R \<c>\<o>\<l> i A) UNIV"
  by(transfer) (simp add: matrix_mult_sum scalar_mult_eq_scaleR)


instantiation sq_mtx :: (finite) real_normed_vector 
begin

definition norm_sq_mtx :: "'a sq_mtx \<Rightarrow> real" where "\<parallel>A\<parallel> = \<parallel>to_vec A\<parallel>\<^sub>o\<^sub>p"

lift_definition scaleR_sq_mtx :: "real \<Rightarrow> 'a sq_mtx \<Rightarrow> 'a sq_mtx" is scaleR .

definition sgn_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx" 
  where "sgn_sq_mtx A = (inverse (\<parallel>A\<parallel>)) *\<^sub>R A"

definition dist_sq_mtx :: "'a sq_mtx \<Rightarrow> 'a sq_mtx \<Rightarrow> real" 
  where "dist_sq_mtx A B = \<parallel>A - B\<parallel>" 

definition uniformity_sq_mtx :: "('a sq_mtx \<times> 'a sq_mtx) filter" 
  where "uniformity_sq_mtx = (INF e:{0<..}. principal {(x, y). dist x y < e})"

definition open_sq_mtx :: "'a sq_mtx set \<Rightarrow> bool" 
  where "open_sq_mtx U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"

instance apply intro_classes 
  unfolding sgn_sq_mtx_def open_sq_mtx_def dist_sq_mtx_def uniformity_sq_mtx_def
  prefer 10 apply(transfer, simp add: norm_sq_mtx_def op_norm_triangle)
  prefer 9 apply(simp_all add: norm_sq_mtx_def zero_sq_mtx_def op_norm_eq_0)
  by(transfer, simp add: norm_sq_mtx_def op_norm_scaleR algebra_simps)+

end

lemma sq_mtx_scaleR_ith[simp]: "(c *\<^sub>R A) $$ i = (c  *\<^sub>R (A $$ i))"
  by (unfold scaleR_sq_mtx_def, transfer, simp)

lemma scaleR_sq_mtx_diag: "c *\<^sub>R sq_mtx_diag f = (\<d>\<i>\<a>\<g> i. c * f i)"
  by (rule sq_mtx_eq_iff(2), simp add: axis_def)

lemma scaleR_mtx_vec_assoc: "(c *\<^sub>R A) *\<^sub>V x = c *\<^sub>R (A *\<^sub>V x)"
  unfolding scaleR_sq_mtx_def sq_mtx_vec_mult_def apply simp
  by (simp add: scaleR_matrix_vector_assoc)

lemma mtrx_vec_scaleR_commute: "A *\<^sub>V (c *\<^sub>R x) = c *\<^sub>R (A *\<^sub>V x)"
  unfolding scaleR_sq_mtx_def sq_mtx_vec_mult_def apply(simp, transfer)
  by (simp add: vector_scaleR_commute)

lemma le_mtx_norm: "m \<in> {\<parallel>A *\<^sub>V x\<parallel> |x. \<parallel>x\<parallel> = 1} \<Longrightarrow> m \<le> \<parallel>A\<parallel>"
  using cSup_upper[of _ "{\<parallel>(to_vec A) *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"]
  by (simp add: op_norm_set_proptys(2) op_norm_def norm_sq_mtx_def sq_mtx_vec_mult.rep_eq)

lemma norm_vec_mult_le: "\<parallel>A *\<^sub>V x\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>x\<parallel>)"
  by (simp add: norm_matrix_le_mult_op_norm norm_sq_mtx_def sq_mtx_vec_mult.rep_eq)

lemma bounded_bilinear_sq_mtx_vec_mult: "bounded_bilinear (\<lambda>A s. A *\<^sub>V s)"
  apply (rule bounded_bilinear.intro, simp_all add: mtx_vec_mult_add_rdistr 
      mtx_vec_mult_add_rdistl scaleR_mtx_vec_assoc mtrx_vec_scaleR_commute)
  by (rule_tac x=1 in exI, auto intro!: norm_vec_mult_le)

lemma norm_sq_mtx_def2: "\<parallel>A\<parallel> = Sup {\<parallel>A *\<^sub>V x\<parallel> |x. \<parallel>x\<parallel> = 1}"
  unfolding norm_sq_mtx_def op_norm_def sq_mtx_vec_mult_def by simp

lemma norm_sq_mtx_def3: "\<parallel>A\<parallel> = SUPREMUM UNIV (\<lambda>x. (\<parallel>A *\<^sub>V x\<parallel>) / (\<parallel>x\<parallel>))"
  unfolding norm_sq_mtx_def onorm_def sq_mtx_vec_mult_def by simp

lemma norm_sq_mtx_diag: "\<parallel>sq_mtx_diag f\<parallel> = Max {\<bar>f i\<bar> |i. i \<in> UNIV}"
  unfolding norm_sq_mtx_def apply transfer
  by (rule op_norm_diag_mat_eq)

lemma sq_mtx_norm_le_sum_col: "\<parallel>A\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i A\<parallel>)"
  using op_norm_le_sum_column[of "to_vec A"] apply(simp add: norm_sq_mtx_def)
  by(transfer, simp add: op_norm_le_sum_column)

lemma norm_le_transpose: "\<parallel>A\<parallel> \<le> \<parallel>A\<^sup>\<dagger>\<parallel>"
  unfolding norm_sq_mtx_def by transfer (rule op_norm_le_transpose)

lemma norm_eq_norm_transpose[simp]: "\<parallel>A\<^sup>\<dagger>\<parallel> = \<parallel>A\<parallel>"
  using norm_le_transpose[of A] and norm_le_transpose[of "A\<^sup>\<dagger>"] by simp

lemma norm_column_le_norm: "\<parallel>A $$ i\<parallel> \<le> \<parallel>A\<parallel>"
  using norm_vec_mult_le[of "A\<^sup>\<dagger>" "\<e> i"] by simp


subsubsection\<open> Squared matrices form a Banach space \<close>

instantiation sq_mtx :: (finite) real_normed_algebra_1
begin

lift_definition one_sq_mtx :: "'a sq_mtx" is "sq_mtx_chi (mat 1)" .

lemma sq_mtx_one_idty: "1 * A = A" "A * 1 = A" for A :: "'a sq_mtx"
  by(transfer, transfer, unfold mat_def matrix_matrix_mult_def, simp add: vec_eq_iff)+

lemma sq_mtx_norm_1: "\<parallel>(1::'a sq_mtx)\<parallel> = 1"
  unfolding one_sq_mtx_def norm_sq_mtx_def apply(simp add: op_norm_def)
  apply(subst cSup_eq[of _ 1])
  using ex_norm_eq_1 by auto

lemma sq_mtx_norm_times: "\<parallel>A * B\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>B\<parallel>)" for A :: "'a sq_mtx"
  unfolding norm_sq_mtx_def times_sq_mtx_def by(simp add: op_norm_matrix_matrix_mult_le)

instance apply intro_classes 
  apply(simp_all add: sq_mtx_one_idty sq_mtx_norm_1 sq_mtx_norm_times)
  apply(simp_all add: sq_mtx_chi_inject vec_eq_iff one_sq_mtx_def zero_sq_mtx_def mat_def)
  by(transfer, simp add: scalar_matrix_assoc matrix_scalar_ac)+

end

lemma sq_mtx_one_ith_simps[simp]: "1 $$ i $ i = 1" "i \<noteq> j \<Longrightarrow> 1 $$ i $ j = 0"
  unfolding one_sq_mtx_def mat_def by simp_all

lemma of_nat_eq_sq_mtx_diag[simp]: "of_nat m = (\<d>\<i>\<a>\<g> i. m)"
  by (induct m) (simp, rule sq_mtx_eq_iff(2), simp add: axis_def)+

lemma mtx_vec_mult_1[simp]: "1 *\<^sub>V s = s"
  by (auto simp: sq_mtx_vec_mult_def one_sq_mtx_def 
      mat_def vec_eq_iff matrix_vector_mult_def)

lemma sq_mtx_diag_one[simp]: "(\<d>\<i>\<a>\<g> i. 1) = 1"
  by (rule sq_mtx_eq_iff(2), simp add: one_sq_mtx_def mat_def axis_def)

abbreviation "mtx_invertible A \<equiv> invertible (to_vec A)"

lemma mtx_invertible_def: "mtx_invertible A \<longleftrightarrow> (\<exists>A'. A' * A = 1 \<and> A * A' = 1)"
  apply (unfold sq_mtx_inv_def times_sq_mtx_def one_sq_mtx_def invertible_def, clarsimp, safe)
   apply(rule_tac x="sq_mtx_chi A'" in exI, simp)
  by (rule_tac x="to_vec A'" in exI, simp add: sq_mtx_chi_inject)

lemma mtx_invertibleI:
  assumes "A * B = 1" and "B * A = 1"
  shows "mtx_invertible A"
  using assms unfolding mtx_invertible_def by auto

lemma mtx_invertibleD[simp]:
  assumes "mtx_invertible A" 
  shows "A\<^sup>-\<^sup>1 * A = 1" and "A * A\<^sup>-\<^sup>1 = 1"
  apply (unfold sq_mtx_inv_def times_sq_mtx_def one_sq_mtx_def)
  using assms by simp_all

lemma mtx_invertible_inv[simp]: "mtx_invertible A \<Longrightarrow> mtx_invertible (A\<^sup>-\<^sup>1)"
  using mtx_invertibleD mtx_invertibleI by blast

lemma mtx_invertible_one[simp]: "mtx_invertible 1"
  by (simp add: one_sq_mtx.rep_eq)

lemma sq_mtx_inv_unique:
  assumes "A * B = 1" and "B * A = 1"
  shows "A\<^sup>-\<^sup>1 = B"
  by (metis (no_types, lifting) assms mtx_invertibleD(2) 
      mtx_invertibleI mult.assoc sq_mtx_one_idty(1))

lemma sq_mtx_inv_idempotent[simp]: "mtx_invertible A \<Longrightarrow> A\<^sup>-\<^sup>1\<^sup>-\<^sup>1 = A"
  using mtx_invertibleD sq_mtx_inv_unique by blast

lemma sq_mtx_inv_mult:
  assumes "mtx_invertible A" and "mtx_invertible B"
  shows "(A * B)\<^sup>-\<^sup>1 = B\<^sup>-\<^sup>1 * A\<^sup>-\<^sup>1"
  by (simp add: assms matrix_inv_matrix_mul sq_mtx_inv_def times_sq_mtx_def)

lemma sq_mtx_inv_one[simp]: "1\<^sup>-\<^sup>1 = 1"
  by (simp add: sq_mtx_inv_unique)

definition similar_sq_mtx :: "('n::finite) sq_mtx \<Rightarrow> 'n sq_mtx \<Rightarrow> bool" (infixr "\<sim>" 25)
  where "(A \<sim> B) \<longleftrightarrow> (\<exists> P. mtx_invertible P \<and> A = P\<^sup>-\<^sup>1 * B * P)"

lemma similar_sq_mtx_matrix: "(A \<sim> B) = similar_matrix (to_vec A) (to_vec B)"
  apply(unfold similar_matrix_def similar_sq_mtx_def)
  by (smt UNIV_I sq_mtx_chi_inverse sq_mtx_inv.abs_eq times_sq_mtx.abs_eq to_vec_inverse)

lemma similar_sq_mtx_refl[simp]: "A \<sim> A"
  by (unfold similar_sq_mtx_def, rule_tac x="1" in exI, simp)

lemma similar_sq_mtx_simm: "A \<sim> B \<Longrightarrow> B \<sim> A"
  apply(unfold similar_sq_mtx_def, clarsimp)
  apply(rule_tac x="P\<^sup>-\<^sup>1" in exI, simp add: mult.assoc)
  by (metis mtx_invertibleD(2) mult.assoc mult.left_neutral)

lemma similar_sq_mtx_trans: "A \<sim> B \<Longrightarrow> B \<sim> C \<Longrightarrow> A \<sim> C"
  unfolding similar_sq_mtx_matrix using similar_matrix_trans by blast

lemma power_sq_mtx_diag: "(sq_mtx_diag f)^n = (\<d>\<i>\<a>\<g> i. f i^n)"
  by (induct n, simp_all)

lemma power_similiar_sq_mtx_diag_eq:
  assumes "mtx_invertible P"
      and "A = P\<^sup>-\<^sup>1 * (sq_mtx_diag f) * P"
    shows "A^n = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i^n) * P"
proof(induct n, simp_all add: assms)
  fix n::nat
  have "P\<^sup>-\<^sup>1 * sq_mtx_diag f * P * (P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P) = 
  P\<^sup>-\<^sup>1 * sq_mtx_diag f * (\<d>\<i>\<a>\<g> i. f i ^ n) * P"
    by (metis (no_types, lifting) assms(1) sign_simps(4) mtx_invertibleD(2) sq_mtx_one_idty(2))
  also have "... = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i * f i ^ n) * P"
    by (simp add: mult.assoc) 
  finally show "P\<^sup>-\<^sup>1 * sq_mtx_diag f * P * (P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P) = 
  P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i * f i ^ n) * P" .
qed

lemma power_similar_sq_mtx_diag:
  assumes "A \<sim> (sq_mtx_diag f)"
  shows "A^n \<sim> (\<d>\<i>\<a>\<g> i. f i^n)"
  using assms power_similiar_sq_mtx_diag_eq 
  unfolding similar_sq_mtx_def by blast

lemma Cauchy_cols:
  fixes X :: "nat \<Rightarrow> ('a::finite) sq_mtx" 
  assumes "Cauchy X"
  shows "Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))" 
proof(unfold Cauchy_def dist_norm, clarsimp)
  fix \<epsilon>::real assume "\<epsilon> > 0"
  then obtain M where M_def:"\<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>X m - X n\<parallel> < \<epsilon>"
    using \<open>Cauchy X\<close> unfolding Cauchy_def by(simp add: dist_sq_mtx_def) metis
  {fix m n assume "m \<ge> M" and "n \<ge> M"
    hence "\<epsilon> > \<parallel>X m - X n\<parallel>" 
      using M_def by blast
    moreover have "\<parallel>X m - X n\<parallel> \<ge> \<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel>"
      by(rule le_mtx_norm[of _ "X m - X n"], force)
    moreover have "\<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel> = \<parallel>X m *\<^sub>V \<e> i - X n *\<^sub>V \<e> i\<parallel>"
      by (simp add: mtx_vec_mult_minus_rdistrib)
    moreover have "... = \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel>"
      by (simp add: mtx_vec_mult_minus_rdistrib mtx_vec_mult_canon)
    ultimately have "\<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
      by linarith}
  thus "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
    by blast
qed

lemma col_convergence:
  assumes "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
  shows "X \<longlonglongrightarrow> sq_mtx_chi (transpose L)"
proof(unfold LIMSEQ_def dist_norm, clarsimp)
  let ?L = "sq_mtx_chi (transpose L)"
  let ?a = "CARD('a)" fix \<epsilon>::real assume "\<epsilon> > 0"
  hence "\<epsilon> / ?a > 0" by simp
  hence "\<forall>i. \<exists> N. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"
    using assms unfolding LIMSEQ_def dist_norm convergent_def by blast
  then obtain N where "\<forall>i. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"
    using finite_nat_minimal_witness[of "\<lambda> i n. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"] by blast
  also have "\<And>i n. (\<c>\<o>\<l> i (X n) - L $ i) = (\<c>\<o>\<l> i (X n - ?L))"
    unfolding minus_sq_mtx_def by(transfer, simp add: transpose_def vec_eq_iff column_def)
  ultimately have N_def:"\<forall>i. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel> < \<epsilon>/?a" 
    by auto
  have "\<forall>n\<ge>N. \<parallel>X n - ?L\<parallel> < \<epsilon>"
  proof(rule allI, rule impI)
    fix n::nat assume "N \<le> n"
    hence "\<forall> i. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel> < \<epsilon>/?a"
      using N_def by blast
    hence "(\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>) < (\<Sum>(i::'a)\<in>UNIV. \<epsilon>/?a)"
      using sum_strict_mono[of _ "\<lambda>i. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>"] by force
    moreover have "\<parallel>X n - ?L\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i (X n - ?L)\<parallel>)"
      using sq_mtx_norm_le_sum_col by blast
    moreover have "(\<Sum>(i::'a)\<in>UNIV. \<epsilon>/?a) = \<epsilon>" 
      by force
    ultimately show "\<parallel>X n - ?L\<parallel> < \<epsilon>" 
      by linarith
  qed
  thus "\<exists>no. \<forall>n\<ge>no. \<parallel>X n - ?L\<parallel> < \<epsilon>" 
    by blast
qed

instance sq_mtx :: (finite) banach
proof(standard)
  fix X :: "nat \<Rightarrow> 'a sq_mtx"
  assume "Cauchy X"
  hence "\<And>i. Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))"
    using Cauchy_cols by blast
  hence obs: "\<forall>i. \<exists>! L. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L"
    using Cauchy_convergent convergent_def LIMSEQ_unique by fastforce
  define L where "L = (\<chi> i. lim (\<lambda>n. \<c>\<o>\<l> i (X n)))"
  hence "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
    using obs theI_unique[of "\<lambda>L. (\<lambda>n. \<c>\<o>\<l> _ (X n)) \<longlonglongrightarrow> L" "L $ _"] by (simp add: lim_def)
  thus "convergent X"
    using col_convergence unfolding convergent_def by blast
qed

lemma exp_similiar_sq_mtx_diag_eq:
  assumes "mtx_invertible P"
      and "A = P\<^sup>-\<^sup>1 * (sq_mtx_diag f) * P"
    shows "exp A = P\<^sup>-\<^sup>1 * exp (sq_mtx_diag f) * P"
proof(unfold exp_def power_similiar_sq_mtx_diag_eq[OF assms])
  have "(\<Sum>n. P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P /\<^sub>R fact n) = 
  (\<Sum>n. P\<^sup>-\<^sup>1 * ((\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n) * P)"
    by simp
  also have "... = (\<Sum>n. P\<^sup>-\<^sup>1 * ((\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n)) * P"
    apply(subst suminf_multr[OF bounded_linear.summable[OF bounded_linear_mult_right]])
    unfolding power_sq_mtx_diag[symmetric] by (simp_all add: summable_exp_generic)
  also have "... = P\<^sup>-\<^sup>1 * (\<Sum>n. (\<d>\<i>\<a>\<g> i. f i ^ n) /\<^sub>R fact n) * P"
    apply(subst suminf_mult[of _ "P\<^sup>-\<^sup>1"])
    unfolding power_sq_mtx_diag[symmetric] 
    by (simp_all add: summable_exp_generic)
  finally show "(\<Sum>n. P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. f i ^ n) * P /\<^sub>R fact n) = 
  P\<^sup>-\<^sup>1 * (\<Sum>n. sq_mtx_diag f ^ n /\<^sub>R fact n) * P"
    unfolding power_sq_mtx_diag by simp
qed

lemma exp_similiar_sq_mtx_diag:
  assumes "A \<sim> sq_mtx_diag f"
  shows "exp A \<sim> exp (sq_mtx_diag f)"
  using assms exp_similiar_sq_mtx_diag_eq 
  unfolding similar_sq_mtx_def by blast

lemma suminf_sq_mtx_diag:
  assumes "\<forall>i. (\<lambda>n. f n i) sums (suminf (\<lambda>n. f n i))"
  shows "(\<Sum>n. (\<d>\<i>\<a>\<g> i. f n i)) = (\<d>\<i>\<a>\<g> i. \<Sum>n. f n i)"
proof(rule suminfI, unfold sums_def LIMSEQ_iff, clarsimp simp: norm_sq_mtx_diag)
  let ?g = "\<lambda>n i. \<bar>(\<Sum>n<n. f n i) - (\<Sum>n. f n i)\<bar>"
  fix r::real assume "r > 0"
  have "\<forall>i. \<exists>no. \<forall>n\<ge>no. ?g n i < r"
    using assms \<open>r > 0\<close> unfolding sums_def LIMSEQ_iff by clarsimp 
  then obtain N where key: "\<forall>i. \<forall>n\<ge>N. ?g n i < r"
    using finite_nat_minimal_witness[of "\<lambda>i n. ?g n i < r"] by blast
  {fix n::nat
    assume "n \<ge> N"
    obtain i where i_def: "Max {x. \<exists>i. x = ?g n i} = ?g n i"
      using cMax_finite_ex[of "{x. \<exists>i. x = ?g n i}"] by auto
    hence "?g n i < r"
      using key \<open>n \<ge> N\<close> by blast
    hence "Max {x. \<exists>i. x = ?g n i} < r"
      unfolding i_def[symmetric] .}
  thus "\<exists>N. \<forall>n\<ge>N. Max {x. \<exists>i. x = ?g n i} < r"
    by blast
qed

lemma exp_sq_mtx_diag: "exp (sq_mtx_diag f) = (\<d>\<i>\<a>\<g> i. exp (f i))"
  apply(unfold exp_def, simp add: power_sq_mtx_diag scaleR_sq_mtx_diag)
  apply(rule suminf_sq_mtx_diag)
  using exp_converges[of "f _"] 
  unfolding sums_def LIMSEQ_iff exp_def by force

lemma exp_scaleR_similar_sq_mtx_diag_eq:
  assumes "mtx_invertible P" and "A = P\<^sup>-\<^sup>1 * (sq_mtx_diag f) * P"
    shows "exp (t *\<^sub>R A) = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P"
proof-
  have "exp (t *\<^sub>R A) = exp (P\<^sup>-\<^sup>1 * (t *\<^sub>R sq_mtx_diag f) * P)"
    using assms by simp
  also have "... = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P"
    by (metis assms(1) exp_similiar_sq_mtx_diag_eq exp_sq_mtx_diag scaleR_sq_mtx_diag)
  finally show "exp (t *\<^sub>R A) = P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P" .
qed

lemma has_derivative_mtx_ith[derivative_intros]:
  fixes t::real and T :: "real set"
  defines "t\<^sub>0 \<equiv> netlimit (at t within T)"
  assumes "D A \<mapsto> (\<lambda>h. h *\<^sub>R A' t) at t within T"
  shows "D (\<lambda>t. A t $$ i) \<mapsto> (\<lambda>h. h *\<^sub>R A' t $$ i) at t within T"
  using assms unfolding has_derivative_def apply safe
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
  apply(rule_tac F="\<lambda>\<tau>. (A \<tau> - A t\<^sub>0 - (\<tau> - t\<^sub>0) *\<^sub>R A' t) /\<^sub>R (\<parallel>\<tau> - t\<^sub>0\<parallel>)" in tendsto_zero_norm_bound)
  by (clarsimp, rule mult_left_mono, metis (no_types, lifting) norm_column_le_norm 
      sq_mtx_minus_ith sq_mtx_scaleR_ith) simp_all

lemmas has_derivative_mtx_vec_mult[simp, derivative_intros] = 
  bounded_bilinear.FDERIV[OF bounded_bilinear_sq_mtx_vec_mult]

lemma vderiv_mtx_vec_mult_intro[poly_derivatives]: 
  assumes "D u = u' on T" and "D A = A' on T"
      and "g = (\<lambda>t. A t *\<^sub>V u' t + A' t *\<^sub>V u t )"
    shows "D (\<lambda>t. A t *\<^sub>V u t) = g on T"
  using assms unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  apply(erule_tac x=x in ballE, simp_all)+
  apply(rule derivative_eq_intros(146))
  by (auto simp: fun_eq_iff mtrx_vec_scaleR_commute pth_6 scaleR_mtx_vec_assoc)

lemma has_derivative_mtx_vec_multl[derivative_intros]:
  assumes "\<And> i j. D (\<lambda>t. (A t) $$ i $ j) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) $$ i $ j) (at t within T)"
  shows "D (\<lambda>t. A t *\<^sub>V x) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) *\<^sub>V x) at t within T"
  unfolding sq_mtx_vec_mult_sum_cols
  apply(rule_tac f'1="\<lambda>i \<tau>. \<tau> *\<^sub>R  (x $ i *\<^sub>R \<c>\<o>\<l> i (A' t))" in derivative_eq_intros(9))
   apply(simp_all add: scaleR_right.sum)
  apply(rule_tac g'1="\<lambda>\<tau>. \<tau> *\<^sub>R \<c>\<o>\<l> i (A' t)" in derivative_eq_intros(4), simp_all add: mult.commute)
  using assms unfolding sq_mtx_col_def column_def apply(transfer, simp)
  apply(rule has_derivative_vec_lambda)
  by (simp add: scaleR_vec_def)

lemma continuous_on_mtx_vec_multl: "D A = A' on T \<Longrightarrow> continuous_on T (\<lambda>\<tau>. A \<tau> *\<^sub>V b)"
  apply(rule vderiv_on_continuous_on[OF vderiv_mtx_vec_mult_intro])
  by (rule derivative_intros, auto)

lemma continuous_on_mtx_vec_multr: "continuous_on S ((*\<^sub>V) A)"
  by transfer (simp add: matrix_vector_mult_linear_continuous_on)

\<comment> \<open>Automatically generated derivative rules from this subsubsection \<close>

thm derivative_eq_intros(145,146,147)


subsection\<open> Flow for squared matrix systems \<close>

text\<open>Finally, we can use the @{term exp} operation to characterize the general solutions for linear 
systems of ODEs. We show that they satisfy the @{term "local_flow"} locale.\<close>

lemma continuous_on_sq_mtx_vec_multl:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "continuous_on T A"
  shows "continuous_on T (\<lambda>t. A t *\<^sub>V s)"
proof-
  have "\<forall>t\<in>T. \<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<parallel>to_vec (A \<tau>) - to_vec (A t)\<parallel>\<^sub>o\<^sub>p \<le> \<epsilon>"
    using assms unfolding continuous_on_iff dist_norm norm_sq_mtx_def by force
  hence "continuous_on T (\<lambda>t. to_vec (A t) *v s)"
    by (rule continuous_on_matrix_vector_multl)
  thus ?thesis
    by transfer
qed

lemmas continuous_on_affine = continuous_on_add[OF continuous_on_sq_mtx_vec_multl]

lemma lipschitz_cond_sq_mtx_affine:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "t \<in> T" and "bdd_above {\<parallel>A t\<parallel> |t. t \<in> T}"
  shows "\<parallel>A t *\<^sub>V x - A t *\<^sub>V y\<parallel> \<le> Sup {\<parallel>A t\<parallel> |t. t \<in> T} * (\<parallel>x - y\<parallel>)"
  using assms unfolding norm_sq_mtx_def apply transfer
  using lipschitz_cond_affine by force

lemma local_lipschitz_sq_mtx_affine:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "continuous_on T A" "open T" "open S"
  shows "local_lipschitz T S (\<lambda>t s. A t *\<^sub>V s + B t)"
proof-
  have obs: "\<And>\<tau> \<epsilon>. 0 < \<epsilon> \<Longrightarrow>  \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>A t\<parallel> |t. t \<in> cball \<tau> \<epsilon>}"
    by (rule bdd_above_norm_cont_comp, rule continuous_on_subset[OF assms(1)], simp_all)
  hence "\<And>\<tau> \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> cball \<tau> \<epsilon> \<subseteq> T \<Longrightarrow> bdd_above {\<parallel>to_vec (A t)\<parallel>\<^sub>o\<^sub>p |t. t \<in> cball \<tau> \<epsilon>}"
    by (simp add: norm_sq_mtx_def)
  hence "local_lipschitz T S (\<lambda>t s. to_vec (A t) *v s + B t)"
    using local_lipschitz_affine[OF assms(2,3)] by force
  thus ?thesis
    by transfer 
qed

lemma picard_lindeloef_sq_mtx_affine:
  fixes A :: "real \<Rightarrow> ('n::finite) sq_mtx"
  assumes "continuous_on T A" and "continuous_on T B" 
       and "t\<^sub>0 \<in> T" "is_interval T" "open T" and "open S"
    shows "picard_lindeloef (\<lambda>t s. A t *\<^sub>V s + B t) T S t\<^sub>0"
  apply(unfold_locales, simp_all add: assms, clarsimp)
  using continuous_on_affine assms apply blast
  by (rule local_lipschitz_sq_mtx_affine, simp_all add: assms)

lemma local_flow_sq_mtx_linear: "local_flow ((*\<^sub>V) A) UNIV UNIV (\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx_affine[of _ "\<lambda>t. A" "\<lambda>t. 0"] apply force
  apply(rule vderiv_mtx_vec_mult_intro, rule poly_derivatives)
  by (rule has_vderiv_on_exp_scaleRl) (auto simp: fun_eq_iff
      exp_times_scaleR_commute sq_mtx_times_vec_assoc intro: poly_derivatives)

lemma local_flow_sq_mtx_affine: "local_flow (\<lambda>s. A *\<^sub>V s + B) UNIV UNIV 
  (\<lambda>t s. (exp (t *\<^sub>R A)) *\<^sub>V s + (exp (t *\<^sub>R A)) *\<^sub>V ivl_integral 0 t (\<lambda>\<tau>. (exp (- \<tau> *\<^sub>R A)) *\<^sub>V B))"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx_affine[of _ "\<lambda>t. A" "\<lambda>t. B"] apply force
    apply(intro poly_derivatives; (rule ivl_integral_has_vderiv_on[OF continuous_on_mtx_vec_multl])?)
            apply(rule poly_derivatives, (force)?, (force)?)+
    apply(simp_all add: mtx_vec_mult_add_rdistl sq_mtx_times_vec_assoc[symmetric])
  by (auto simp: exp_minus_inverse exp_times_scaleR_commute)

lemma (* name? *)
  assumes "mtx_invertible P" and "A = P\<^sup>-\<^sup>1 * (sq_mtx_diag f) * P"
  shows "local_flow ((*\<^sub>V) A) UNIV UNIV (\<lambda>t s. (P\<^sup>-\<^sup>1 * (\<d>\<i>\<a>\<g> i. exp (t * f i)) * P) *\<^sub>V s)"
  using exp_scaleR_similar_sq_mtx_diag_eq[OF assms] local_flow_sq_mtx_linear[of A] by force

end