theory hs_prelims_matrices
  imports hs_prelims

begin

chapter\<open> Linear Algebra for Hybrid Systems \<close>

text\<open> Linear systems of ordinary differential equations (ODEs) are those whose vector fields are a 
linear operator. That is, there is a matrix @{term A} such that the system @{term "x' t = f (x t)"} 
can be rewritten as @{term "x' t = A *v (x t)"}. The end goal of this section is to prove that every 
linear system of ODEs has a unique solution, and to obtain a characterization of said solution. For 
that we start by formalising various properties of vector spaces.\<close>

section\<open> Vector operations \<close>

abbreviation "\<e> k \<equiv> axis k 1"

abbreviation "entries (A::'a^'n^'m) \<equiv> {A $ i $ j | i j. i \<in> UNIV \<and> j \<in> UNIV}"

abbreviation kronecker_delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('b::zero)" ("\<delta>\<^sub>K _ _ _" [55, 55, 55] 55)
  where "\<delta>\<^sub>K i j q \<equiv> (if i = j then q else 0)"

lemma finite_sum_univ_singleton: "(sum g UNIV) = sum g {i} + sum g (UNIV - {i})" for i::"'a::finite"
  by (metis add.commute finite_class.finite_UNIV sum.subset_diff top_greatest)

lemma kronecker_delta_simps[simp]:
  fixes q::"('a::semiring_0)" and i::"'n::finite"
  shows "(\<Sum>j\<in>UNIV. f j * (\<delta>\<^sub>K j i q)) = f i * q"
    and "(\<Sum>j\<in>UNIV. f j * (\<delta>\<^sub>K i j q)) = f i * q"
    and "(\<Sum>j\<in>UNIV. (\<delta>\<^sub>K i j q) * f j) = q * f i"
    and "(\<Sum>j\<in>UNIV. (\<delta>\<^sub>K j i q) * f j) = q * f i"
  by (auto simp: finite_sum_univ_singleton[of _ i])

lemma sum_axis[simp]:
  fixes q::"('a::semiring_0)"
  shows "(\<Sum>j\<in>UNIV. f j * axis i q $ j) = f i * q"
    and "(\<Sum>j\<in>UNIV. axis i q $ j * f j) = q * f i"
  unfolding axis_def by(auto simp: vec_eq_iff)

lemma sum_scalar_nth_axis: "sum (\<lambda>i. (x $ i) *s \<e> i) UNIV = x" for x :: "('a::semiring_1)^'n"
  unfolding vec_eq_iff axis_def by simp

lemma scalar_eq_scaleR[simp]: "c *s x = c *\<^sub>R x" for c :: real
  unfolding vec_eq_iff by simp

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma vec_mult_inner: "(A *v v) \<bullet> w = v \<bullet> (transpose A *v w)" for A::"real ^'n^'n"
  unfolding matrix_vector_mult_def transpose_def inner_vec_def
  apply(simp add: sum_distrib_right sum_distrib_left)
  apply(subst sum.swap)
  apply(subgoal_tac "\<forall>i j. A $ i $ j * v $ j * w $ i = v $ j * (A $ i $ j * w $ i)")
  by presburger (simp)

lemma uminus_axis_eq[simp]: "- axis i k = axis i (-k)" for k::"'a::ring"
  unfolding axis_def by(simp add: vec_eq_iff)

lemma norm_axis_eq[simp]: "\<parallel>axis i k\<parallel> = \<parallel>k\<parallel>"
proof(simp add: axis_def norm_vec_def L2_set_def)
  have "(\<Sum>j\<in>UNIV. (\<parallel>(\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) = (\<Sum>j\<in>{i}. (\<parallel>(\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2) + (\<Sum>j\<in>(UNIV-{i}). (\<parallel>(\<delta>\<^sub>K j i k)\<parallel>)\<^sup>2)"
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

section\<open> Matrix norms \<close>

text\<open> Here we develop the foundations for obtaining the Lipschitz constant for every linear system
of ODEs @{term "x' t = A *v (x t)"}. For that we derive some properties of two matrix norms.\<close>

subsection\<open> Matrix operator norm \<close>

abbreviation "op_norm (A::('a::real_normed_algebra_1)^'n^'m) \<equiv> Sup {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"

notation op_norm ("(1\<parallel>_\<parallel>\<^sub>o\<^sub>p)" [65] 61)

lemma norm_matrix_bound:
  fixes A::"('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
proof-
  fix x::"('a, 'n) vec" assume "\<parallel>x\<parallel> = 1"
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
  from this have "\<And>j. \<parallel>(A *v x) $ j\<parallel> \<le> ((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j"
    unfolding matrix_vector_mult_def by simp
  hence "(\<Sum>j\<in>UNIV. (\<parallel>(A *v x) $ j\<parallel>)\<^sup>2) \<le> (\<Sum>j\<in>UNIV. (\<parallel>((\<chi> i1 i2. \<parallel>A $ i1 $ i2\<parallel>) *v 1) $ j\<parallel>)\<^sup>2)"
    by (metis (mono_tags, lifting) norm_ge_zero power2_abs power_mono real_norm_def sum_mono) 
  thus "\<parallel>A *v x\<parallel> \<le> \<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>"
    unfolding norm_vec_def L2_set_def by simp
qed

lemma op_norm_set_proptys:
  fixes A::"('a::real_normed_algebra_1)^'n^'m"
  shows "bounded {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "bdd_above {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    and "{\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<noteq> {}"
  unfolding bounded_def bdd_above_def apply safe
    apply(rule_tac x=0 in exI, rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI)
    apply(force simp: norm_matrix_bound dist_real_def)
   apply(rule_tac x="\<parallel>(\<chi> i j. \<parallel>A $ i $ j\<parallel>) *v 1\<parallel>" in exI, force simp: norm_matrix_bound)
  using ex_norm_eq_1 by blast

lemma norm_matrix_le_op_norm: "\<parallel>x\<parallel> = 1 \<Longrightarrow> \<parallel>A *v x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  by(rule cSup_upper, auto simp: op_norm_set_proptys)

lemma norm_matrix_le_op_norm_ge_0: "0 \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  using ex_norm_eq_1 norm_ge_zero norm_matrix_le_op_norm basic_trans_rules(23) by blast

lemma norm_sgn_le_op_norm: "\<parallel>A *v sgn x\<parallel> \<le> \<parallel>A\<parallel>\<^sub>o\<^sub>p"
  by(cases "x=0", simp_all add: norm_sgn norm_matrix_le_op_norm norm_matrix_le_op_norm_ge_0)

lemma norm_matrix_le_mult_op_norm: "\<parallel>A *v x\<parallel> \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" for A :: "real^'n^'m"
proof-
  have "\<parallel>A *v x\<parallel> = (\<parallel>A *v sgn x\<parallel>) * (\<parallel>x\<parallel>)"
    by(simp add: mult_norm_matrix_sgn_eq)
  also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)"
    using norm_sgn_le_op_norm[of A] by (simp add: mult_mono')
  finally show ?thesis by simp
qed

lemma ltimes_op_norm:
  "Sup {\<bar>c\<bar> * (\<parallel>A *v x\<parallel>) |x. \<parallel>x\<parallel> = 1} = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" (is "Sup ?cA = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p) ")
proof(cases "c = 0", simp add: ex_norm_eq_1)
  let ?S = "{(\<parallel>A *v x\<parallel>) |x. \<parallel>x\<parallel> = 1}"
  note op_norm_set_proptys(2)[of A]
  also have "?cA = {\<bar>c\<bar> * x|x. x \<in> ?S}" 
    by force
  ultimately have bdd_cA:"bdd_above ?cA" 
    using bdd_above_ltimes[of "\<bar>c\<bar>" ?S] by simp
  assume "c \<noteq> 0"
  show "Sup ?cA = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
  proof(rule cSup_eq_linorder)
    show nempty_cA:"?cA \<noteq> {}" 
      using op_norm_set_proptys(3)[of A] by blast 
    show "bdd_above ?cA"
      using bdd_cA by blast
    {fix m assume "m \<in> ?cA"
      then obtain x where x_def:"\<parallel>x\<parallel> = 1 \<and> m = \<bar>c\<bar> * (\<parallel>A *v x\<parallel>)"
        by blast
      hence "(\<parallel>A *v x\<parallel>) \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
        using norm_matrix_le_op_norm by force
      hence "m  \<le> \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p) " 
        using x_def by (simp add: mult_left_mono)}
    thus "\<forall>x\<in>?cA. x \<le> \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
      by blast
  next
    show "\<forall>y<\<bar>c\<bar>*(\<parallel>A\<parallel>\<^sub>o\<^sub>p). \<exists>x\<in>?cA. y < x"
    proof(clarify)
      fix m assume "m < \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
      hence "(m / \<bar>c\<bar>) < (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
        using pos_divide_less_eq[of "\<bar>c\<bar>" m "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)"] \<open>c \<noteq> 0\<close>
            semiring_normalization_rules(7)[of "\<bar>c\<bar>"] by auto
      then obtain x where "\<parallel>x\<parallel> = 1 \<and> (m / \<bar>c\<bar>) < (\<parallel>A *v x\<parallel>)"
        using less_cSup_iff[of ?S "m / \<bar>c\<bar>"] op_norm_set_proptys by force
      hence "\<parallel>x\<parallel> = 1 \<and> m < \<bar>c\<bar> * (\<parallel>A *v x\<parallel>)"
        using \<open>c \<noteq> 0\<close> pos_divide_less_eq[of _ m _] by (simp add: mult.commute)
      thus "\<exists>n\<in>?cA. m < n" by blast
    qed
  qed
qed

lemma op_norm_le_sum_column:
  "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)" for A::"real^'n^'m"
  using op_norm_set_proptys(3) proof(rule cSup_least)
  fix m assume "m \<in> {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    then obtain x where x_def:"\<parallel>x\<parallel> = 1 \<and> m = (\<parallel>A *v x\<parallel>)" by blast
    hence x_hyp:"\<And>i. norm (x $ i) \<le> 1"
      by (simp add: norm_bound_component_le_cart)
    have "(\<parallel>A *v x\<parallel>) = norm (\<Sum>i\<in>UNIV. (x $ i *s column i A))"
      by(subst matrix_mult_sum[of A], simp)
    also have "... \<le> (\<Sum>i\<in>UNIV.  norm (x $ i *s column i A))"
      by (simp add: sum_norm_le)
    also have "... = (\<Sum>i\<in>UNIV.  norm (x $ i) * norm (column i A))"
      by (simp add: mult_norm_matrix_sgn_eq)
    also have "... \<le> (\<Sum>i\<in>UNIV. norm (column i A))"
      using x_hyp by (simp add: mult_left_le_one_le sum_mono) 
    finally show "m \<le> (\<Sum>i\<in>UNIV. norm (column i A))"
      using x_def by linarith
qed

lemma op_norm_zero_iff: "(\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0) = (A = 0)" for A::"('a::real_normed_field)^'n^'m"
proof
  assume "A = 0" thus "\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0" 
    by(simp add: ex_norm_eq_1)
next
  assume "\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0"
  note cSup_upper[of _ "{\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"]
  hence "\<And>r. r \<in> {\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<Longrightarrow> r \<le>  (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
    using op_norm_set_proptys(2) by force
  also have "\<And>r. r \<in> ({\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}) \<Longrightarrow> 0 \<le> r" 
    using norm_ge_zero by blast
  ultimately have "\<And>r. r \<in> ({\<parallel>A *v x\<parallel> | x. \<parallel>x\<parallel> = 1}) \<Longrightarrow> r = 0" 
    using \<open>\<parallel>A\<parallel>\<^sub>o\<^sub>p = 0\<close> by fastforce
  hence "\<And>x. \<parallel>x\<parallel> = 1 \<Longrightarrow> x \<noteq> 0 \<and> (\<parallel>A *v x\<parallel>) = 0" 
    by force
  hence "\<And>i. norm (A *v \<e> i) = 0" 
    by simp
  from this show "A = 0" 
    using matrix_axis_0[of 1 A] norm_eq_zero by simp
qed

lemma op_norm_triangle:
  fixes A::"('a::real_normed_algebra_1)^'n^'m"
  shows "\<parallel>A + B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) + (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
  using op_norm_set_proptys(3)[of "A + B"] proof(rule cSup_least)
  fix m assume "m \<in> {\<parallel>(A + B) *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    then obtain x::"'a^'n" where "\<parallel>x\<parallel> = 1" and "m = \<parallel>(A + B) *v x\<parallel>" 
      by blast
    have " \<parallel>(A + B) *v x\<parallel> \<le> (\<parallel>A *v x\<parallel>) + (\<parallel>B *v x\<parallel>)"
      by (simp add: matrix_vector_mult_add_rdistrib norm_triangle_ineq)
    also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) + (\<parallel>B\<parallel>\<^sub>o\<^sub>p)"
      by (simp add: \<open>\<parallel>x\<parallel> = 1\<close> add_mono norm_matrix_le_op_norm)
    finally show "m \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) + (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" 
      using \<open>m = \<parallel>(A + B) *v x\<parallel>\<close> by blast
qed

lemma op_norm_scaleR: "\<parallel>c *\<^sub>R A\<parallel>\<^sub>o\<^sub>p = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
proof-
  let ?N= "{\<bar>c\<bar> * (\<parallel>A *v x\<parallel>) |x. \<parallel>x\<parallel> = 1}"
  have "{\<parallel>(c *\<^sub>R A) *v x\<parallel> | x. \<parallel>x\<parallel> = 1} = ?N" 
    by (metis (no_types, hide_lams) norm_scaleR scaleR_vector_assoc)
  also have "Sup ?N = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
    using ltimes_op_norm[of c A] by blast
  ultimately show " op_norm (c *\<^sub>R A) = \<bar>c\<bar> * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" 
    by auto
qed

lemma op_norm_matrix_matrix_mult_le: "\<parallel>A ** B\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" for A::"real^'n^'m"
using op_norm_set_proptys(3)[of "A ** B"]
proof(rule cSup_least)
  have "0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)" using norm_matrix_le_op_norm_ge_0 by force 
  fix n assume "n \<in> {\<parallel>(A ** B) *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"
    then obtain x where x_def:"n = \<parallel>A ** B *v x\<parallel> \<and> \<parallel>x\<parallel> = 1" by blast
    have "\<parallel>A ** B *v x\<parallel> = \<parallel>A *v (B *v x)\<parallel>"
      by (simp add: matrix_vector_mul_assoc)
    also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B *v x\<parallel>)"
      by (simp add: norm_matrix_le_mult_op_norm[of _ "B *v x"])
    also have "... \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * ((\<parallel>B\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>))"
      using norm_matrix_le_mult_op_norm[of B x] \<open>0 \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p)\<close> mult_left_mono by blast 
    also have "... = (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" using x_def by simp
    finally show "n \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>B\<parallel>\<^sub>o\<^sub>p)" using x_def by blast
qed

lemma norm_matrix_vec_mult_le_transpose:
"\<parallel>x\<parallel> = 1 \<Longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)" for A::"real^'a^'a"
proof-
  assume "\<parallel>x\<parallel> = 1"
  have "(\<parallel>A *v x\<parallel>)\<^sup>2 = (A *v x) \<bullet> (A *v x)"
    using dot_square_norm[of "(A *v x)"] by simp
  also have "... = x \<bullet> (transpose A *v (A *v x))"
    using vec_mult_inner by blast
  also have "... \<le> (\<parallel>x\<parallel>) * (\<parallel>transpose A *v (A *v x)\<parallel>)"
    using norm_cauchy_schwarz by blast
  also have "... \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    apply(subst matrix_vector_mul_assoc) using norm_matrix_le_mult_op_norm[of "transpose A ** A" x]
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close>) 
  finally have "((\<parallel>A *v x\<parallel>))^2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x\<parallel>)^2"
    by linarith
  thus "(\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    by (simp add: \<open>\<parallel>x\<parallel> = 1\<close> real_le_rsqrt)
qed

subsection\<open> Matrix maximum norm \<close>

abbreviation "max_norm (A::real^'n^'m) \<equiv> Max (abs ` (entries A))"

notation max_norm ("(1\<parallel>_\<parallel>\<^sub>m\<^sub>a\<^sub>x)" [65] 61)

lemma max_norm_def: "\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x = Max {\<bar>A $ i $ j\<bar>|i j. i\<in>UNIV \<and> j\<in>UNIV}"
  by(simp add: image_def, rule arg_cong[of _ _ Max], blast)

lemma max_norm_set_proptys:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "finite {\<bar>A $ i $ j\<bar> |i j. i \<in> UNIV \<and> j \<in> UNIV}" (is "finite ?X")
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
proof-
  have "\<And> i j. \<bar>A $ i $ j\<bar> \<ge> 0" by simp
  also have "\<And> i j. \<bar>A $ i $ j\<bar> \<le> \<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x"
    unfolding max_norm_def using max_norm_set_proptys Max_ge max_norm_def by blast
  finally show "0 \<le> \<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x" .
qed

lemma op_norm_le_max_norm:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> real CARD('n) * real CARD('m) * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)" (is "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le>?n * ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)")
proof(rule cSup_least)
  show "{\<parallel>A *v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<noteq> {}"
    using op_norm_set_proptys(3) by blast
  {fix n assume "n \<in> {\<parallel>A *v x\<parallel> |x. \<parallel>x\<parallel> = 1}"
    then obtain x::"(real, 'n) vec" where n_def:"\<parallel>x\<parallel> = 1 \<and> \<parallel>A *v x\<parallel> = n"
      by blast
    hence comp_le_1:"\<forall> i::'n. \<bar>x $ i\<bar> \<le> 1"
      by (simp add: norm_bound_component_le_cart)
    have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)"
      using matrix_mult_sum by blast
    hence "\<parallel>A *v x\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>x $ i *s column i A\<parallel>)"
      by (simp add: sum_norm_le)
    also have "... = (\<Sum>i\<in>UNIV. \<bar>x $ i\<bar> * (\<parallel>column i A\<parallel>))"
      by simp
    also have "... \<le> (\<Sum>i\<in>UNIV. \<parallel>column i A\<parallel>)"
      by (metis (no_types, lifting) Groups.mult_ac(2) comp_le_1 mult_left_le norm_ge_zero sum_mono)
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x))"
    proof(unfold norm_vec_def L2_set_def real_norm_def)
      have "\<And>i j. \<bar>column i A $ j\<bar> \<le> \<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x"
        using max_norm_set_proptys Max_ge unfolding column_def max_norm_def by(simp, blast)
      hence "\<And>i j. \<bar>column i A $ j\<bar>\<^sup>2 \<le> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2"
        by (metis (no_types, lifting) One_nat_def abs_ge_zero numerals(2) order_trans_rules(23) 
            power2_abs power2_le_iff_abs_le)
      then have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> (\<Sum>(j::'m)\<in>UNIV. (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2)"
        by (meson sum_mono)
      also have "(\<Sum>(j::'m)\<in>UNIV. (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2) = ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2" by simp
      ultimately have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2" by force
      hence "\<And>i. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> sqrt (?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2)"
        by(simp add: real_sqrt_le_mono)
      also have "sqrt (?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)\<^sup>2) \<le> sqrt ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
        using max_norm_ge_0 real_sqrt_mult by auto
      also have "... \<le> ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
        using sqrt_real_nat_le max_norm_ge_0 mult_right_mono by blast  
      finally show "(\<Sum>i\<in>UNIV. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2)) \<le> (\<Sum>(i::'n)\<in>UNIV. ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x))"
        by (meson sum_mono)
    qed
    also have "(\<Sum>(i::'n)\<in>UNIV. (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)) = ?n * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
      using sum_constant_scale by auto
    ultimately have "n \<le> ?n * ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)" 
      by (simp add: n_def)}
  thus "\<And>n. n \<in> {\<parallel>A *v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<Longrightarrow> n \<le> ?n * ?m * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)" 
    by blast
qed

section\<open> Picard Lindeloef for linear systems \<close>

text\<open> Now we prove our first objective. First we obtain the Lipschitz constant for linear systems
of ODEs, and then we prove that IVPs arising from these satisfy the conditions for Picard-Lindeloef 
theorem (hence, they have a unique solution). \<close>

lemma matrix_lipschitz_constant:
  fixes A::"real^('n::finite)^'n"
  shows "dist (A *v x) (A *v y) \<le> (real CARD('n))\<^sup>2 * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) * dist x y"
  unfolding dist_norm matrix_vector_mult_diff_distrib[symmetric]
proof(subst mult_norm_matrix_sgn_eq[symmetric])
  have "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) * (real CARD('n) * real CARD('n))"
    by (metis (no_types) Groups.mult_ac(2) op_norm_le_max_norm)
  then have "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x - y\<parallel>) \<le> (real CARD('n))\<^sup>2 * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) * (\<parallel>x - y\<parallel>)"
    by (simp add: cross3_simps(11) mult_left_mono semiring_normalization_rules(29))
  also have "(\<parallel>A *v sgn (x - y)\<parallel>) * (\<parallel>x - y\<parallel>) \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>x - y\<parallel>)"
    by (simp add: norm_sgn_le_op_norm cross3_simps(11) mult_left_mono) 
  ultimately show "(\<parallel>A *v sgn (x - y)\<parallel>) * (\<parallel>x - y\<parallel>) \<le> (real CARD('n))\<^sup>2 * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) * (\<parallel>x - y\<parallel>)"
    using order_trans_rules(23) by blast
qed

lemma picard_lindeloef_linear_system:
  fixes A::"real^'n^'n" 
  assumes "0 < ((real CARD('n))\<^sup>2 * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_lindeloef_closed_ivl (\<lambda> t s. A *v s) {0..t} ?L 0"
  apply unfold_locales apply(simp add: \<open>0 \<le> t\<close>)
  subgoal by(simp, metis continuous_on_compose2 continuous_on_cong continuous_on_id 
        continuous_on_snd matrix_vector_mult_linear_continuous_on top_greatest) 
  subgoal using matrix_lipschitz_constant max_norm_ge_0 zero_compare_simps(4,12) 
    unfolding lipschitz_on_def by blast
  apply(simp_all add: assms)
  subgoal for r s apply(subgoal_tac "\<bar>r - s\<bar> < 1/?L")
     apply(subst (asm) pos_less_divide_eq[of ?L "\<bar>r - s\<bar>" 1])
    using assms by auto
  done

section\<open> Matrix Exponential \<close>

text\<open> The general solution for linear systems of ODEs is an exponential function. Unfortunately, 
this operation is only available in Isabelle for Banach spaces which are formalised as a class. 
Hence we need to prove that a specific type is an instance of this class. We define the type and 
build towards this instantiation in this section.\<close>

subsection\<open> Squared matrices operations \<close>

typedef 'm sqrd_matrix = "UNIV::(real^'m^'m) set"
  morphisms to_vec sq_mtx_chi by simp

declare sq_mtx_chi_inverse [simp]
    and to_vec_inverse [simp]

lemma galois_to_vec_mtx_chi[simp]:"(to_vec A = B) = (A = sq_mtx_chi B)" 
  by auto

setup_lifting type_definition_sqrd_matrix

lift_definition sq_mtx_ith::"'m sqrd_matrix \<Rightarrow> 'm \<Rightarrow> (real^'m)" (infixl "$$" 90) is vec_nth .

lift_definition sq_mtx_vec_prod::"'m sqrd_matrix \<Rightarrow> (real^'m) \<Rightarrow> (real^'m)" (infixl "*\<^sub>V" 90) 
  is matrix_vector_mult .

lift_definition sq_mtx_column::"'m \<Rightarrow> 'm sqrd_matrix \<Rightarrow> (real^'m)"
  is "\<lambda>i X. column i (to_vec X)" .

lift_definition vec_sq_mtx_prod::"(real^'m) \<Rightarrow> 'm sqrd_matrix \<Rightarrow> (real^'m)" is vector_matrix_mult .

lift_definition sq_mtx_diag::"real \<Rightarrow> ('m::finite) sqrd_matrix" ("\<d>\<i>\<a>\<g>") is mat .

lift_definition sq_mtx_transpose::"('m::finite) sqrd_matrix \<Rightarrow> 'm sqrd_matrix" ("_\<^sup>\<dagger>") is transpose .

lift_definition sq_mtx_row::"'m \<Rightarrow> ('m::finite) sqrd_matrix \<Rightarrow> real^'m" ("\<r>\<o>\<w>") is row .

lift_definition sq_mtx_col::"'m \<Rightarrow> ('m::finite) sqrd_matrix \<Rightarrow> real^'m" ("\<c>\<o>\<l>")  is column .

lift_definition sq_mtx_rows::"('m::finite) sqrd_matrix \<Rightarrow> (real^'m) set" is rows .

lift_definition sq_mtx_cols::"('m::finite) sqrd_matrix \<Rightarrow> (real^'m) set" is columns .

lemma sq_mtx_eq_iff:
  shows "(\<And>i. A $$ i = B $$ i) \<Longrightarrow> A = B"
    and "(\<And>i j. A $$ i $ j = B $$ i $ j) \<Longrightarrow> A = B"
  by(transfer, simp add: vec_eq_iff)+

lemma sq_mtx_vec_prod_eq: "m *\<^sub>V x = (\<chi> i. sum (\<lambda>j. ((m$$i)$j) * (x$j)) UNIV)"
  by(transfer, simp add: matrix_vector_mult_def)

lemma sq_mtx_transpose_transpose[simp]:"(A\<^sup>\<dagger>)\<^sup>\<dagger> = A"
  by(transfer, simp)

lemma transpose_mult_vec_canon_row[simp]:"(A\<^sup>\<dagger>) *\<^sub>V (\<e> i) = \<r>\<o>\<w> i A"
  by transfer (simp add: row_def transpose_def axis_def matrix_vector_mult_def)

lemma row_ith[simp]:"\<r>\<o>\<w> i A = A $$ i"
  by transfer (simp add: row_def)

lemma mtx_vec_prod_canon:"A *\<^sub>V (\<e> i) = \<c>\<o>\<l> i A" 
  by (transfer, simp add: matrix_vector_mult_basis)

subsection\<open> Squared matrices form Banach space \<close>

instantiation sqrd_matrix :: (finite) ring 
begin

lift_definition plus_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" is "(+)" .

lift_definition zero_sqrd_matrix :: "'a sqrd_matrix" is "0" .

lift_definition uminus_sqrd_matrix ::"'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" is "uminus" .

lift_definition minus_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" is "(-)" .

lift_definition times_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" is "(**)" .

declare plus_sqrd_matrix.rep_eq [simp]
    and minus_sqrd_matrix.rep_eq [simp]

instance apply intro_classes
  by(transfer, simp add: algebra_simps matrix_mul_assoc matrix_add_rdistrib matrix_add_ldistrib)+

end

lemma sq_mtx_plus_ith[simp]:"(A + B) $$ i = A $$ i + B $$ i"
  by(unfold plus_sqrd_matrix_def, transfer, simp)

lemma sq_mtx_minus_ith[simp]:"(A - B) $$ i = A $$ i - B $$ i"
  by(unfold minus_sqrd_matrix_def, transfer, simp)

lemma mtx_vec_prod_add_rdistr:"(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  unfolding plus_sqrd_matrix_def apply(transfer)
  by (simp add: matrix_vector_mult_add_rdistrib)

lemma mtx_vec_prod_minus_rdistrib:"(A - B) *\<^sub>V x = A *\<^sub>V x - B *\<^sub>V x"
  unfolding minus_sqrd_matrix_def by(transfer, simp add: matrix_vector_mult_diff_rdistrib)

lemma sq_mtx_times_vec_assoc: "(A * B) *\<^sub>V x0 = A *\<^sub>V (B *\<^sub>V x0)"
  by (transfer, simp add: matrix_vector_mul_assoc)

lemma sq_mtx_vec_mult_sum_cols:"A *\<^sub>V x = sum (\<lambda>i. x $ i *\<^sub>R \<c>\<o>\<l> i A) UNIV"
  by(transfer) (simp add: matrix_mult_sum scalar_mult_eq_scaleR)

instantiation sqrd_matrix :: (finite) real_normed_vector 
begin

definition norm_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> real" where "\<parallel>A\<parallel> = \<parallel>to_vec A\<parallel>\<^sub>o\<^sub>p"

lift_definition scaleR_sqrd_matrix::"real \<Rightarrow> 'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" is scaleR .

definition sgn_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix" 
  where "sgn_sqrd_matrix A = (inverse (\<parallel>A\<parallel>)) *\<^sub>R A"

definition dist_sqrd_matrix :: "'a sqrd_matrix \<Rightarrow> 'a sqrd_matrix \<Rightarrow> real" 
  where "dist_sqrd_matrix A B = \<parallel>A - B\<parallel>" 

definition uniformity_sqrd_matrix :: "('a sqrd_matrix \<times> 'a sqrd_matrix) filter" 
  where "uniformity_sqrd_matrix = (INF e:{0<..}. principal {(x, y). dist x y < e})"

definition open_sqrd_matrix :: "'a sqrd_matrix set \<Rightarrow> bool" 
  where "open_sqrd_matrix U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"  

instance apply intro_classes 
  unfolding sgn_sqrd_matrix_def open_sqrd_matrix_def dist_sqrd_matrix_def uniformity_sqrd_matrix_def
  prefer 10 apply(transfer, simp add: norm_sqrd_matrix_def op_norm_triangle)
  prefer 9 apply(simp_all add: norm_sqrd_matrix_def zero_sqrd_matrix_def op_norm_zero_iff)
  by(transfer, simp add: norm_sqrd_matrix_def op_norm_scaleR algebra_simps)+

end

lemma sq_mtx_scaleR_ith[simp]: "(c *\<^sub>R A) $$ i = (c  *\<^sub>R (A $$ i))"
  by(unfold scaleR_sqrd_matrix_def, transfer, simp)

lemma le_mtx_norm: "m \<in> {\<parallel>A *\<^sub>V x\<parallel> |x. \<parallel>x\<parallel> = 1} \<Longrightarrow> m \<le> \<parallel>A\<parallel>"
  using cSup_upper[of _ "{\<parallel>(to_vec A) *v x\<parallel> | x. \<parallel>x\<parallel> = 1}"]
  by (simp add: op_norm_set_proptys(2) norm_sqrd_matrix_def sq_mtx_vec_prod.rep_eq)

lemma norm_vec_mult_le: "\<parallel>A *\<^sub>V x\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>x\<parallel>)"
  by (simp add: norm_matrix_le_mult_op_norm norm_sqrd_matrix_def sq_mtx_vec_prod.rep_eq)

lemma sq_mtx_norm_le_sum_col: "\<parallel>A\<parallel> \<le> (\<Sum>i\<in>UNIV. \<parallel>\<c>\<o>\<l> i A\<parallel>)"
  using op_norm_le_sum_column[of "to_vec A"] apply(simp add: norm_sqrd_matrix_def)
  by(transfer, simp add: op_norm_le_sum_column)

lemma norm_le_transpose: "\<parallel>A\<parallel> \<le> \<parallel>A\<^sup>\<dagger>\<parallel>"
  apply(simp add: norm_sqrd_matrix_def, transfer, simp add: transpose_def)
  using op_norm_set_proptys(3) apply(rule cSup_least)
proof(clarsimp)
  fix A::"real^'a^'a" and x::"real ^ 'a" assume "\<parallel>x\<parallel> = 1"
  have obs:"\<forall>x. \<parallel>x\<parallel> = 1 \<longrightarrow> (\<parallel>A *v x\<parallel>) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)) * (\<parallel>x\<parallel>)"
    using norm_matrix_vec_mult_le_transpose by blast
  have "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> sqrt ((\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p))"
    using op_norm_set_proptys(3) apply(rule cSup_least) using obs by clarsimp
  then have "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A ** A\<parallel>\<^sub>o\<^sub>p)"
    using power_mono[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)" _ 2] norm_matrix_le_op_norm_ge_0 by force
  also have "... \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"
    using op_norm_matrix_matrix_mult_le by blast
  finally have "((\<parallel>A\<parallel>\<^sub>o\<^sub>p))\<^sup>2 \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p) * (\<parallel>A\<parallel>\<^sub>o\<^sub>p)"  by linarith
  hence "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<le> (\<parallel>transpose A\<parallel>\<^sub>o\<^sub>p)"
    using sq_le_cancel[of "(\<parallel>A\<parallel>\<^sub>o\<^sub>p)"] norm_matrix_le_op_norm_ge_0 by blast
  thus "(\<parallel>A *v x\<parallel>) \<le> op_norm (\<chi> i j. A $ j $ i)"
    unfolding transpose_def using \<open>\<parallel>x\<parallel> = 1\<close> order_trans norm_matrix_le_op_norm by blast 
qed

lemma norm_eq_norm_transpose[simp]: "\<parallel>A\<^sup>\<dagger>\<parallel> = \<parallel>A\<parallel>"
  using norm_le_transpose[of A] and norm_le_transpose[of "A\<^sup>\<dagger>"] by simp

lemma norm_column_le_norm: "\<parallel>A $$ i\<parallel> \<le> \<parallel>A\<parallel>"
  using norm_vec_mult_le[of "A\<^sup>\<dagger>" "\<e> i"] by simp


instantiation sqrd_matrix :: (finite) real_normed_algebra_1
begin

lift_definition one_sqrd_matrix :: "'a sqrd_matrix" is "sq_mtx_chi (mat 1)" .

lemma sq_mtx_one_idty: "1 * A = A" "A * 1 = A" for A::"'a sqrd_matrix"
  by(transfer, transfer, unfold mat_def matrix_matrix_mult_def, simp add: vec_eq_iff)+

lemma sq_mtx_norm_1: "\<parallel>(1::'a sqrd_matrix)\<parallel> = 1"
  unfolding one_sqrd_matrix_def norm_sqrd_matrix_def apply simp
  apply(subst cSup_eq[of _ 1])
  using ex_norm_eq_1 by auto

lemma sq_mtx_norm_times: "\<parallel>A * B\<parallel> \<le> (\<parallel>A\<parallel>) * (\<parallel>B\<parallel>)" for A::"'a sqrd_matrix"
  unfolding norm_sqrd_matrix_def times_sqrd_matrix_def by(simp add: op_norm_matrix_matrix_mult_le)

instance apply intro_classes 
  apply(simp_all add: sq_mtx_one_idty sq_mtx_norm_1 sq_mtx_norm_times)
  apply(simp_all add: sq_mtx_chi_inject vec_eq_iff one_sqrd_matrix_def zero_sqrd_matrix_def mat_def)
  by(transfer, simp add: scalar_matrix_assoc matrix_scalar_ac)+

end

lemma sq_mtx_one_vec: "1 *\<^sub>V s = s"
  by (auto simp: sq_mtx_vec_prod_def one_sqrd_matrix_def 
      mat_def vec_eq_iff matrix_vector_mult_def)

lemma Cauchy_cols:
  fixes X :: "nat \<Rightarrow> ('a::finite) sqrd_matrix" 
  assumes "Cauchy X"
  shows "Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))" 
proof(unfold Cauchy_def dist_norm, clarsimp)
  fix \<epsilon>::real assume "\<epsilon> > 0"
  from this obtain M where M_def:"\<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>X m - X n\<parallel> < \<epsilon>"
    using \<open>Cauchy X\<close> unfolding Cauchy_def by(simp add: dist_sqrd_matrix_def) blast
  {fix m n assume "m \<ge> M" and "n \<ge> M"
    hence "\<epsilon> > \<parallel>X m - X n\<parallel>" 
      using M_def by blast
    moreover have "\<parallel>X m - X n\<parallel> \<ge> \<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel>"
      by(rule le_mtx_norm[of _ "X m - X n"], force)
    moreover have "\<parallel>(X m - X n) *\<^sub>V \<e> i\<parallel> = \<parallel>X m *\<^sub>V \<e> i - X n *\<^sub>V \<e> i\<parallel>"
      by (simp add: mtx_vec_prod_minus_rdistrib)
    moreover have "... = \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel>"
      by (simp add: mtx_vec_prod_minus_rdistrib mtx_vec_prod_canon)
    ultimately have "\<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
      by linarith}
  thus "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<parallel>\<c>\<o>\<l> i (X m) - \<c>\<o>\<l> i (X n)\<parallel> < \<epsilon>" 
    by blast
qed

lemma col_convergent:
  assumes "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
  shows "convergent X"
  unfolding convergent_def proof(rule_tac x="sq_mtx_chi (transpose L)" in exI)
  let ?L = "sq_mtx_chi (transpose L)"
  show "X \<longlonglongrightarrow> ?L"
  proof(unfold LIMSEQ_def dist_norm, clarsimp)
    fix \<epsilon>::real assume "\<epsilon> > 0"
    let ?a = "CARD('a)" fix \<epsilon>::real assume "\<epsilon> > 0" 
    hence "\<epsilon> / ?a > 0" 
      by simp
    from this and assms have "\<forall>i. \<exists> N. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a" 
      unfolding LIMSEQ_def dist_norm convergent_def by blast
    then obtain N where "\<forall>i. \<forall>n\<ge>N. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"
      using finite_nat_minimal_witness[of "\<lambda> i n. \<parallel>\<c>\<o>\<l> i (X n) - L $ i\<parallel> < \<epsilon>/?a"] by blast
    also have "\<And>i n. (\<c>\<o>\<l> i (X n) - L $ i) = (\<c>\<o>\<l> i (X n - ?L))"
      unfolding minus_sqrd_matrix_def by(transfer, simp add: transpose_def vec_eq_iff column_def)
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
qed

instance sqrd_matrix :: (finite) banach
proof(standard)
  fix X::"nat \<Rightarrow> 'a sqrd_matrix"
  assume "Cauchy X"
  have "\<And>i. Cauchy (\<lambda>n. \<c>\<o>\<l> i (X n))"
    using \<open>Cauchy X\<close> Cauchy_cols by blast
  hence obs:"\<forall>i. \<exists>! L. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L"
    using Cauchy_convergent convergent_def LIMSEQ_unique by fastforce
  define L where "L = (\<chi> i. lim (\<lambda>n. \<c>\<o>\<l> i (X n)))"
  from this and obs have "\<forall>i. (\<lambda>n. \<c>\<o>\<l> i (X n)) \<longlonglongrightarrow> L $ i" 
    using theI_unique[of "\<lambda>L. (\<lambda>n. \<c>\<o>\<l> _ (X n)) \<longlonglongrightarrow> L" "L $ _"] by (simp add: lim_def)
  thus "convergent X"
    using col_convergent by blast
qed

section\<open> Flow for squared matrix systems \<close>

text\<open>Finally, we can use the @{term exp} operation to characterize the general solutions for linear 
systems of ODEs. After this, we show that IVPs with these systems have a unique solution (using the 
Picard Lindeloef locale) and explicitly write it via the local flow locale.\<close>

lemma mtx_vec_prod_has_derivative_mtx_vec_prod:
  assumes "\<And> i j. D (\<lambda>t. (A t) $$ i $ j) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) $$ i $ j) (at t within s)"
    and "(\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) *\<^sub>V x) = g'"
  shows "D (\<lambda>t. A t *\<^sub>V x) \<mapsto> g' at t within s"
  using assms(2) apply safe apply(rule ssubst[of g' "(\<lambda>\<tau>. \<tau> *\<^sub>R (A' t) *\<^sub>V x)"], simp) 
  unfolding sq_mtx_vec_mult_sum_cols 
  apply(rule_tac f'1="\<lambda>i \<tau>. \<tau> *\<^sub>R  (x $ i *\<^sub>R \<c>\<o>\<l> i (A' t))" in derivative_eq_intros(9))
   apply(simp_all add: scaleR_right.sum)
  apply(rule_tac g'1="\<lambda>\<tau>. \<tau> *\<^sub>R \<c>\<o>\<l> i (A' t)" in derivative_eq_intros(4), simp_all add: mult.commute)
  using assms unfolding sq_mtx_col_def column_def apply(transfer, simp)
  apply(rule has_derivative_vec_lambda)
  by(simp add: scaleR_vec_def)

lemma has_derivative_mtx_ith:
  assumes "D A \<mapsto> (\<lambda>h. h *\<^sub>R A' x) at x within s"
  shows "D (\<lambda>t. A t $$ i) \<mapsto> (\<lambda>h. h *\<^sub>R A' x $$ i) at x within s"
  unfolding has_derivative_def tendsto_iff dist_norm apply safe
   apply(force simp: bounded_linear_def bounded_linear_axioms_def)
proof(clarsimp)
  fix \<epsilon>::real assume "0 < \<epsilon>"
  let ?x = "netlimit (at x within s)" let "?\<Delta> y" = "y - ?x" and "?\<Delta>A y" = "A y - A ?x"
  let "?P e" = "\<lambda>y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x\<parallel>) < e"
  let ?Q = "\<lambda>y. inverse \<bar>?\<Delta> y\<bar> * (\<parallel>A y $$ i - A ?x $$ i - ?\<Delta> y *\<^sub>R A' x $$ i\<parallel>) < \<epsilon>"
  from assms have "\<forall>e>0. eventually (?P e) (at x within s)"
    unfolding has_derivative_def tendsto_iff by auto
  hence "eventually (?P \<epsilon>) (at x within s)" 
    using \<open>0 < \<epsilon>\<close> by blast
  thus "eventually ?Q (at x within s)"
  proof(rule_tac P="?P \<epsilon>" in eventually_mono, simp_all)
    let "?u y i" = "A y $$ i - A ?x $$ i - ?\<Delta> y *\<^sub>R A' x $$ i"
    fix y assume hyp: "inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x\<parallel>) < \<epsilon>"
    have "\<parallel>?u y i\<parallel> = \<parallel>(?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x) $$ i\<parallel>" 
      by simp
    also have "... \<le> (\<parallel>?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x\<parallel>)"
      using norm_column_le_norm by blast
    ultimately have "\<parallel>?u y i\<parallel> \<le> \<parallel>?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x\<parallel>" 
      by linarith
    hence "inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?u y i\<parallel>) \<le> inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?\<Delta>A y - ?\<Delta> y *\<^sub>R A' x\<parallel>)"
      by (simp add: mult_left_mono)
    thus "inverse \<bar>?\<Delta> y\<bar> * (\<parallel>?u y i\<parallel>) < \<epsilon>"
      using hyp by linarith
  qed
qed

lemma exp_has_vderiv_on_linear:
  fixes A::"(('a::finite) sqrd_matrix)"
  shows "D (\<lambda>t. exp ((t - t0) *\<^sub>R A) *\<^sub>V x0) = (\<lambda>t. A *\<^sub>V (exp ((t - t0) *\<^sub>R A) *\<^sub>V x0)) on T"
  unfolding has_vderiv_on_def has_vector_derivative_def apply clarsimp
  apply(rule_tac A'="\<lambda>t. A * exp ((t - t0) *\<^sub>R A)" in mtx_vec_prod_has_derivative_mtx_vec_prod)
   apply(rule has_derivative_vec_nth)
   apply(rule has_derivative_mtx_ith)
   apply(rule_tac f'="id" in exp_scaleR_has_derivative_right)
    apply(rule_tac f'1="id" and g'1="\<lambda>x. 0" in derivative_eq_intros(11))
      apply(rule derivative_eq_intros)
  by(simp_all add: fun_eq_iff exp_times_scaleR_commute sq_mtx_times_vec_assoc)

lemma picard_lindeloef_sq_mtx:
  fixes A::"('n::finite) sqrd_matrix"
  assumes "0 < ((real CARD('n))\<^sup>2 * (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_lindeloef_closed_ivl (\<lambda> t s. A *\<^sub>V s) {0..t} ?L 0"
  apply unfold_locales apply(simp add: \<open>0 \<le> t\<close>)
  subgoal by(transfer, simp, metis continuous_on_compose2 continuous_on_cong continuous_on_id 
        continuous_on_snd matrix_vector_mult_linear_continuous_on top_greatest) 
  subgoal apply transfer using matrix_lipschitz_constant max_norm_ge_0 zero_compare_simps(4,12)
    unfolding lipschitz_on_def by blast
  apply(simp_all add: assms)
  subgoal for r s apply(subgoal_tac "\<bar>r - s\<bar> < 1/?L")
     apply(subst (asm) pos_less_divide_eq[of ?L "\<bar>r - s\<bar>" 1])
    using assms by auto
  done

lemma local_flow_exp:
  fixes A::"('n::finite) sqrd_matrix"
  assumes "0 < ((real CARD('n))\<^sup>2 * (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "local_flow ((*\<^sub>V) A) {0..t} ?L (\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx assms apply blast
  using exp_has_vderiv_on_linear[of 0] apply force
  by(auto simp: sq_mtx_one_vec)

end