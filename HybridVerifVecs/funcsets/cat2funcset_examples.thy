theory cat2funcset_examples
  imports "../hs_prelims_matrices" cat2funcset

begin

subsection\<open> Examples \<close>

lemma picard_lindeloef_linear_system:
  fixes A::"real^'n^'n"
  defines "L \<equiv> (real CARD('n))\<^sup>2 * (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
  shows "picard_lindeloef (\<lambda> t s. A *v s) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x=1 in exI, clarsimp, rule_tac x="L" in exI, safe)
  using max_norm_ge_0[of A] unfolding assms by force (rule matrix_lipschitz_constant)

lemma picard_lindeloef_sq_mtx:
  fixes A::"('n::finite) sqrd_matrix"
  defines "L \<equiv> (real CARD('n))\<^sup>2 * (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x)"
  shows "picard_lindeloef (\<lambda> t s. A *\<^sub>V s) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x=1 in exI, clarsimp, rule_tac x="L" in exI, safe)
  using max_norm_ge_0[of "to_vec A"] unfolding assms apply force
  by transfer (rule matrix_lipschitz_constant)

lemma local_flow_exp:
  fixes A::"('n::finite) sqrd_matrix"
  shows "local_flow ((*\<^sub>V) A) UNIV UNIV (\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx apply blast
  using exp_has_vderiv_on_linear[of 0] apply force
  by(auto simp: sq_mtx_one_vec)

text\<open> The examples in this subsection show different approaches for the verification of hybrid 
systems. however, the general approach can be outlined as follows: First, we select a finite type to
model program variables @{typ 'n}. We use this to define a vector field @{term f} of type
 @{typ "'a^'n \<Rightarrow> 'a^'n"} to model the dynamics of our system. Then we show a partial correctness 
specification involving the evolution command @{term "(x\<acute>=f & S)"} either by finding a flow for 
the vector field or through differential invariants.\<close>


subsubsection\<open> Single constantly accelerated evolution \<close>

text\<open> The main characteristics distinguishing this example from the rest are:
\begin{enumerate}
\item We define the finite type of program variables with 2 Isabelle strings which make the final
verification easier to parse.
\item We define the vector field (named @{term K}) to model a constantly accelerated object.
\item We define a local flow (@{term \<phi>\<^sub>K}) and use it to compute the wlp for this vector field.
\item The verification is only done on a single evolution command (not operated with any other 
hybrid program).
\end{enumerate} \<close>

typedef program_vars = "{''x'',''v''}"
  morphisms to_str to_var
  apply(rule_tac x="''x''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_program_vars: "CARD(program_vars) = 2"
  using type_definition.card type_definition_program_vars by fastforce

instance program_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV "{''x'',''v''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma program_vars_univD: "(UNIV::program_vars set) = {\<restriction>\<^sub>V ''x'', \<restriction>\<^sub>V ''v''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma program_vars_exhaust: "x = \<restriction>\<^sub>V ''x'' \<or> x = \<restriction>\<^sub>V ''v''"
  using program_vars_univD by auto

abbreviation "constant_acceleration_kinematics g s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then s $ (\<restriction>\<^sub>V ''v'') else g)"

notation constant_acceleration_kinematics ("K")

lemma cnst_acc_continuous:
  fixes X::"(real^program_vars) set"
  shows "continuous_on X (K g)"
  apply(rule continuous_on_vec_lambda)
  unfolding continuous_on_def apply clarsimp
  by(intro tendsto_intros)

lemma picard_lindeloef_cnst_acc:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. K g) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univD to_var_inject)

abbreviation "constant_acceleration_kinematics_flow g t s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then g \<cdot> t ^ 2/2 + s $ (\<restriction>\<^sub>V ''v'') \<cdot> t + s $ (\<restriction>\<^sub>V ''x'') 
        else g \<cdot> t + s $ (\<restriction>\<^sub>V ''v''))"

notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

lemma local_flow_cnst_acc: "local_flow (K g) UNIV UNIV (\<phi>\<^sub>K g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V ''x''")
  using program_vars_exhaust by(auto intro!: poly_derivatives simp: to_var_inject vec_eq_iff)

lemma single_evolution_ball:
  fixes h::real assumes "g < 0" and "h \<ge> 0"
  shows "{s. s $ (\<restriction>\<^sub>V ''x'') = h \<and> s $ (\<restriction>\<^sub>V ''v'') = 0} 
  \<le> fb\<^sub>\<F> (x\<acute>=K g & (\<lambda> s. s $ (\<restriction>\<^sub>V ''x'') \<ge> 0))
  {s. 0 \<le> s $ (\<restriction>\<^sub>V ''x'') \<and> s $ (\<restriction>\<^sub>V ''x'') \<le> h}"
  apply(subst local_flow.ffb_g_orbit[OF local_flow_cnst_acc], simp)
  apply(simp add: subset_eq, safe)
  using assms less_eq_real_def mult_nonneg_nonpos2 zero_le_power2 by blast

no_notation to_var ("\<restriction>\<^sub>V")

no_notation constant_acceleration_kinematics ("K")

no_notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")


subsubsection \<open>Single evolution revisited.\<close>

text\<open> We list again the characteristics that distinguish this example:
\begin{enumerate}
\item We employ an existing finite type of size $3$ to model program variables.
\item We define a $3\times 3$ matrix (named @{term K}) to denote the linear operator that models 
the constantly accelerated motion.
\item We define a local flow (@{term \<phi>\<^sub>K}) and use it to compute the wlp for this linear operator.
\item The verification is done equivalently to the above example.
\end{enumerate} \<close>

term "x::2" \<comment> \<open>It turns out that there is already a 2-element type:\<close>

lemma "CARD(program_vars) = CARD(2)"
  unfolding number_of_program_vars by simp

text \<open>In fact, for each natural number $n$ there is already a corresponding $n$-element type in 
Isabelle. however, there are still lemmas to prove about them in order to do verification of hybrid
systems in $n$-dimensional Euclidean spaces.\<close>

lemma exhaust_5: \<comment> \<open>The analogs for $1,2$ and $3$ have already been proven in Analysis.\<close>
  fixes x::5 
  shows "x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or> x=5"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 5" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4" by arith
  then show ?case by auto
qed

lemma UNIV_3: "(UNIV::3 set) = {0, 1, 2}"
  apply safe using exhaust_3 three_eq_zero by(blast, auto)

lemma sum_axis_UNIV_3[simp]: "(\<Sum>j\<in>(UNIV::3 set). axis i 1 $ j \<cdot> f j) = (f::3 \<Rightarrow> real) i"
  unfolding axis_def UNIV_3 apply simp
  using exhaust_3 by force

text\<open> We can rewrite the original constant acceleration kinematics as a linear operator applied to 
a 3-dimensional vector. For that we take advantage of the following fact: \<close>

lemma "\<e> 1 = (\<chi> j::3. if j= 0 then 0 else if j = 1 then 1 else 0)"
  unfolding axis_def by(rule Cart_lambda_cong, simp)

abbreviation "constant_acceleration_kinematics_matrix \<equiv> 
  (\<chi> i::3. if i=0 then \<e> 1 else if i=1 then \<e> 2 else (0::real^3))"

abbreviation "constant_acceleration_kinematics_matrix_flow t s \<equiv> 
  (\<chi> i::3. if i=0 then s $ 2 \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0
   else if i=1 then s $ 2 \<cdot> t + s $ 1 else s $ 2)"

notation constant_acceleration_kinematics_matrix ("A")

notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>A")

text\<open> With these 2 definitions and the proof that linear systems of ODEs are Picard-Lindeloef, we 
can show that they form a pair of vector-field and its flow. \<close>

lemma entries_cnst_acc_matrix: "entries A = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma local_flow_cnst_acc_matrix: "local_flow ((*v) A) UNIV UNIV \<phi>\<^sub>A"
  unfolding local_flow_def local_flow_axioms_def apply safe
     apply(rule picard_lindeloef_linear_system[where A=A], simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda)
   apply(auto intro!: poly_derivatives simp: matrix_vector_mult_def vec_eq_iff)
  using exhaust_3 by force

text\<open> Finally, we compute the wlp and use it to verify the single-evolution ball again.\<close>

lemma single_evolution_ball_matrix: 
  "{s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2} 
  \<le> fb\<^sub>\<F> (x\<acute>=(*v) A & (\<lambda> s. s $ 0 \<ge> 0))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(subst local_flow.ffb_g_orbit[of "(*v) A"])
  using local_flow_cnst_acc_matrix apply force
  by(auto simp: mult_nonneg_nonpos2)


subsubsection\<open> Circular Motion \<close>

text\<open> The characteristics that distinguish this example are:
\begin{enumerate}
\item We employ an existing finite type of size $2$ to model program variables.
\item We define a $2\times 2$ matrix (named @{term C}) to denote the linear operator that models 
circular motion.
\item We show that the circle equation is a differential invariant for the linear operator.
\item We prove the partial correctness specification corresponding to the previous point.
\item For completeness, we define a local flow (@{term \<phi>\<^sub>C}) and use it to compute the wlp for the 
linear operator and the specification is proven again with this flow.
\end{enumerate} \<close>

lemma two_eq_zero: "(2::2) = 0" 
  by simp

lemma [simp]: "i \<noteq> (0::2) \<longrightarrow> i = 1" 
  using exhaust_2 by fastforce

lemma UNIV_2: "(UNIV::2 set) = {0, 1}"
  apply safe using exhaust_2 two_eq_zero by auto

abbreviation circular_motion_matrix :: "real^2^2" 
  where "circular_motion_matrix \<equiv> (\<chi> i. if i=0 then - \<e> 1 else \<e> 0)"

notation circular_motion_matrix ("C")

lemma circle_invariant: 
  "diff_invariant (\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) ((*v) C) UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="0" in has_vderiv_on_vec_nth, drule_tac i="1" in has_vderiv_on_vec_nth)
  apply(rule_tac S="UNIV" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: matrix_vector_mult_def)

lemma circular_motion_invariants:
  "{s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>=(*v) C & G) {s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2}"
  unfolding ffb_diff_inv using circle_invariant by auto

\<comment> \<open>Proof of the same specification by providing solutions:\<close>

lemma entries_circ_matrix: "entries C = {0, - 1, 1}"
  apply (simp_all add: axis_def, safe)
  subgoal by(rule_tac x="0" in exI, simp)+
  subgoal by(rule_tac x="0" in exI, simp)+
  by(rule_tac x="1" in exI, simp)+

abbreviation "circular_motion_matrix_flow t s \<equiv> 
  (\<chi> i. if i= (0::2) then s$0 \<cdot> cos t - s$1 \<cdot> sin t else s$0 \<cdot> sin t + s$1 \<cdot> cos t)"

notation circular_motion_matrix_flow ("\<phi>\<^sub>C")

lemma local_flow_circ_matrix: "local_flow ((*v) C) UNIV UNIV \<phi>\<^sub>C"
  unfolding local_flow_def local_flow_axioms_def apply safe
  apply(rule picard_lindeloef_linear_system[where A=C], simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda)
  apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by(force simp: vec_eq_iff)

lemma circular_motion:
  "{s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>=(*v) C & G) {s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2}"
  by(subst local_flow.ffb_g_orbit[OF local_flow_circ_matrix]) auto

no_notation circular_motion_matrix ("C")

no_notation circular_motion_matrix_flow ("\<phi>\<^sub>C")


subsubsection\<open> Bouncing Ball with solution \<close>

text\<open> We revisit the previous dynamics for a constantly accelerated object modelled with the matrix
@{term K}. We compose the corresponding evolution command with an if-statement, and iterate this 
hybrid program to model a (completely elastic) ``bouncing ball''. Using the previously defined flow
for this dynamics, proving a specification for this hybrid program is merely an exercise of real 
arithmetic. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]: 
  assumes "0 > g" and inv: "2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h = v \<cdot> v"
  shows "(x::real) \<le> h"
proof-
  have "v \<cdot> v = 2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h \<and> 0 > g" 
    using inv and \<open>0 > g\<close> by auto
  hence obs:"v \<cdot> v = 2 \<cdot> g \<cdot> (x - h) \<and> 0 > g \<and> v \<cdot> v \<ge> 0" 
    using left_diff_distrib mult.commute by (metis zero_le_square) 
  hence "(v \<cdot> v)/(2 \<cdot> g) = (x - h)" 
    by auto 
  also from obs have "(v \<cdot> v)/(2 \<cdot> g) \<le> 0"
    using divide_nonneg_neg by fastforce 
  ultimately have "h - x \<ge> 0" 
    by linarith
  thus ?thesis by auto
qed

lemma [bb_real_arith]:
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
    and pos: "g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real) = 0"
  shows "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    and "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
proof-
  from pos have "g \<cdot> \<tau>\<^sup>2  + 2 \<cdot> v \<cdot> \<tau> + 2 \<cdot> x = 0" by auto
  then have "g\<^sup>2  \<cdot> \<tau>\<^sup>2  + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + v\<^sup>2 + 2 \<cdot> g \<cdot> h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  hence obs: "(g \<cdot> \<tau> + v)\<^sup>2 + 2 \<cdot> g \<cdot> h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  thus "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
  have  "2 \<cdot> g \<cdot> h + (- ((g \<cdot> \<tau>) + v))\<^sup>2 = 0"
    using obs by (metis Groups.add_ac(2) power2_minus)
  thus "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
qed
    
lemma [bb_real_arith]:
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
  shows "2 \<cdot> g \<cdot> (g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real)) = 
  2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v))" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x" 
      apply(subst Rat.sign_simps(18))+ 
      by(auto simp: semiring_normalization_rules(29))
    also have "... = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> h + v \<cdot> v" (is "... = ?middle")
      by(subst invar, simp)
    finally have "?lhs = ?middle".
  moreover 
  {have "?rhs = g \<cdot> g \<cdot> (\<tau> \<cdot> \<tau>) + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> h + v \<cdot> v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball:
  "{s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> 
  fb\<^sub>\<F> (kstar ((x\<acute>=(*v) A & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)}"])
    apply(clarsimp, simp only: ffb_kcomp)
   apply(subst local_flow.ffb_g_orbit[OF local_flow_cnst_acc_matrix])
  unfolding ffb_if_then_else
  by(auto simp: bb_real_arith)


subsubsection\<open> Bouncing Ball with invariants \<close>

text\<open> We prove again the bouncing ball but this time with differential invariants. \<close>

lemma gravity_invariant: "diff_invariant (\<lambda>s. s $ 2 < 0) ((*v) A) UNIV UNIV 0 G"
  apply(rule_tac \<mu>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in diff_invariant_rules(3), clarsimp, simp, clarsimp)
  apply(drule_tac i="2" in has_vderiv_on_vec_nth)
  apply(rule_tac S="UNIV" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: vec_eq_iff matrix_vector_mult_def)

lemma energy_conservation_invariant: 
  "diff_invariant (\<lambda>s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> h - s$1 \<cdot> s $ 1 = 0) ((*v) A) UNIV UNIV 0 G"
  apply(rule diff_invariant_rules, simp, simp, clarify)
  apply(frule_tac i="2" in has_vderiv_on_vec_nth)
  apply(frule_tac i="1" in has_vderiv_on_vec_nth)
  apply(drule_tac i="0" in has_vderiv_on_vec_nth)
  apply(rule_tac S="UNIV" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: vec_eq_iff matrix_vector_mult_def)

lemma bouncing_ball_invariants:
  fixes h::real
  defines dinv: "I \<equiv> \<lambda>s::real^3. s $ 2 < 0 \<and> 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> h - (s$1 \<cdot> s$1) = 0"
  shows "{s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> 
  fb\<^sub>\<F> (kstar ((x\<acute>=(*v) A & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(rule_tac I="{s. 0 \<le> s$0 \<and> I s}" in ffb_kstarI)
    apply(force simp: dinv, simp add: ffb_kcomp ffb_if_then_else)
   apply(rule_tac b="fb\<^sub>\<F> (x\<acute>=(*v) A & (\<lambda> s. s $ 0 \<ge> 0)) {s. 0 \<le> s$0 \<and> I s}" in order.trans)
  apply(simp add: ffb_g_orbital_guard)
    apply(rule_tac b="{s. I s}" in order.trans, force)
    apply(simp_all add: ffb_diff_inv dinv)
    apply(rule diff_invariant_rules)
  using gravity_invariant apply force
  using energy_conservation_invariant apply force
  apply(rule ffb_iso)
  unfolding dinv ffb_eq by (auto simp: bb_real_arith le_fun_def)

no_notation constant_acceleration_kinematics_matrix ("A")

no_notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>A")


subsubsection\<open> Bouncing Ball with exponential solution \<close>

text\<open> In our final example, we prove again the bouncing ball specification but this time we do it 
with the general solution for linear systems.\<close>

abbreviation "constant_acceleration_kinematics_sq_mtx \<equiv> 
  sq_mtx_chi constant_acceleration_kinematics_matrix"

notation constant_acceleration_kinematics_sq_mtx ("K")

lemma max_norm_cnst_acc_sq_mtx: "\<parallel>to_vec K\<parallel>\<^sub>m\<^sub>a\<^sub>x = 1"
proof-
  have "{to_vec K $ i $ j |i j. i \<in> UNIV \<and> j \<in> UNIV} = {0, 1}"
    apply (simp_all add: axis_def, safe)
    by(rule_tac x="1" in exI, simp)+
  thus ?thesis
    by auto
qed

lemma const_acc_mtx_pow2: "(\<tau> *\<^sub>R K)\<^sup>2 = sq_mtx_chi (\<chi> i. if i=0 then \<tau>\<^sup>2 *\<^sub>R \<e> 2 else 0)"
  unfolding power2_eq_square apply(simp add: scaleR_sqrd_matrix_def)
  unfolding times_sqrd_matrix_def apply(simp add: sq_mtx_chi_inject vec_eq_iff)
  apply(simp add: matrix_matrix_mult_def)
  unfolding UNIV_3 by(auto simp: axis_def)

lemma const_acc_mtx_powN: "n > 2 \<Longrightarrow> (\<tau> *\<^sub>R K)^n = 0"
proof(induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  assume IH: "2 < n \<Longrightarrow> (\<tau> *\<^sub>R K)^n = 0" and "2 < Suc n"
  then show ?case 
  proof(cases "n \<le> 2")
    case True
    hence "n = 2"
      using \<open>2 < Suc n\<close> le_less_Suc_eq by blast 
    hence "(\<tau> *\<^sub>R K)^(Suc n) = (\<tau> *\<^sub>R K)^3"
      by simp
    also have "... = (\<tau> *\<^sub>R K) \<cdot> (\<tau> *\<^sub>R K)^2"
      by (metis (no_types, lifting) \<open>n = 2\<close> calculation power_Suc)
    also have "... = (\<tau> *\<^sub>R K) \<cdot> sq_mtx_chi (\<chi> i. if i=0 then \<tau>\<^sup>2 *\<^sub>R \<e> 2 else 0)"
      by (subst const_acc_mtx_pow2) simp
    also have "... = 0"
      unfolding times_sqrd_matrix_def zero_sqrd_matrix_def
      apply(simp add: sq_mtx_chi_inject vec_eq_iff scaleR_sqrd_matrix_def)
      apply(simp add: matrix_matrix_mult_def)
      unfolding UNIV_3 by(auto simp: axis_def)
    finally show ?thesis .
  next
    case False
    thus ?thesis 
      using IH by auto
  qed
qed

lemma suminf_eq_sum:
  fixes f :: "nat \<Rightarrow> ('a::real_normed_vector)"
  assumes "\<And>n. n > m \<Longrightarrow> f n = 0"
  shows "(\<Sum>n. f n) = (\<Sum>n \<le> m. f n)"
  using assms by (meson atMost_iff finite_atMost not_le suminf_finite)

lemma exp_cnst_acc_sq_mtx: "exp (\<tau> *\<^sub>R K) = ((\<tau> *\<^sub>R K)\<^sup>2/\<^sub>R 2) + (\<tau> *\<^sub>R K) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using const_acc_mtx_powN by (simp_all add: numeral_2_eq_2)
 
lemma exp_cnst_acc_sq_mtx_simps:
 "exp (\<tau> *\<^sub>R K) $$ 0 $ 0 = 1" "exp (\<tau> *\<^sub>R K) $$ 0 $ 1 = \<tau>" "exp (\<tau> *\<^sub>R K) $$ 0 $ 2 = \<tau>^2/2"
 "exp (\<tau> *\<^sub>R K) $$ 1 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R K) $$ 1 $ 2 = \<tau>"
 "exp (\<tau> *\<^sub>R K) $$ 2 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 2 = 1"
  unfolding exp_cnst_acc_sq_mtx const_acc_mtx_pow2 
  by(auto simp: plus_sqrd_matrix_def scaleR_sqrd_matrix_def one_sqrd_matrix_def mat_def 
      scaleR_vec_def axis_def plus_vec_def)

lemma bouncing_ball_K: 
  "{s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> fb\<^sub>\<F> 
  (kstar ((x\<acute>=(*\<^sub>V) K & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. 0 \<le> s $ (0::3) \<and> 0 > s $ 2 \<and> 
  2 \<cdot> s $ 2 \<cdot> s $ 0 = 2 \<cdot> s $ 2 \<cdot> h + (s $ 1 \<cdot> s $ 1)}"])
    apply(clarsimp, simp only: ffb_kcomp)
   apply(subst local_flow.ffb_g_orbit[OF local_flow_exp], simp, clarify)
   apply(rule ffb_if_then_elseI, clarsimp)
   apply(simp_all add: sq_mtx_vec_prod_eq)
  unfolding UNIV_3 image_le_pred apply(simp_all add: exp_cnst_acc_sq_mtx_simps)
  subgoal for x using bb_real_arith(3)[of "x $ 2"]
    by (simp add: add.commute mult.commute)
  subgoal for x \<tau> using bb_real_arith(4)[where g="x $ 2" and v="x $ 1"]
    by(simp add: add.commute mult.commute)
  by (force simp: bb_real_arith)

no_notation constant_acceleration_kinematics_sq_mtx ("K")

end