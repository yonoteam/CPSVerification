theory kat2rel_examples
  imports kat2rel

begin

subsection\<open> Examples \<close>

text\<open> The examples in this subsection show different approaches for the verification of hybrid 
systems. however, the general approach can be outlined as follows: First, we select a finite type to
model program variables @{typ 'n}. We use this to define a vector field @{term f} of type
 @{typ "'a^'n \<Rightarrow> 'a^'n"} to model the dynamics of our system. Then we show a partial correctness 
specification involving the evolution command @{term "([x\<acute>=f]T & G)"} either by finding a flow for 
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

typedef program_vars ="{''x'',''v''}"
  morphisms to_str to_var
  apply(rule_tac x="''x''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_program_vars:"CARD(program_vars) = 2"
  using type_definition.card type_definition_program_vars by fastforce

instance program_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV "{''x'',''v''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma program_vars_univD:"(UNIV::program_vars set) = {\<restriction>\<^sub>V ''x'', \<restriction>\<^sub>V ''v''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma program_vars_exhaust:"x = \<restriction>\<^sub>V ''x'' \<or> x = \<restriction>\<^sub>V ''v''"
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
  fixes g::real assumes "0 \<le> \<tau>" and "\<tau> < 1 "
  shows "picard_lindeloef_closed_ivl (\<lambda>t. K g) {0..\<tau>} 1 0"
  unfolding picard_lindeloef_closed_ivl_def apply(simp add: lipschitz_on_def assms, safe)
  apply(rule_tac t="UNIV" and f="snd" in continuous_on_compose2)
  apply(simp_all add: cnst_acc_continuous continuous_on_snd)
   apply(simp add: dist_vec_def L2_set_def dist_real_def)
   apply(subst program_vars_univD, subst program_vars_univD)
   apply(simp_all add: to_var_inject)
  using assms by linarith

abbreviation "constant_acceleration_kinematics_flow g \<tau> s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then g \<cdot> \<tau> ^ 2/2 + s $ (\<restriction>\<^sub>V ''v'') \<cdot> \<tau> + s $ (\<restriction>\<^sub>V ''x'') 
        else g \<cdot> \<tau> + s $ (\<restriction>\<^sub>V ''v''))"

notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

term "D (\<lambda>t. \<phi>\<^sub>K g t s) = (\<lambda>t. K g (\<phi>\<^sub>K g t s)) on {0..\<tau>}"

lemma local_flow_cnst_acc:
  assumes "0 \<le> \<tau>" and "\<tau> < 1 "
  shows "local_flow (K g) {0..\<tau>} 1 (\<phi>\<^sub>K g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using assms picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V ''x''")
  using program_vars_exhaust
  by(auto intro!: poly_derivatives simp: to_var_inject vec_eq_iff)


lemma single_evolution_ball:
  fixes h::real assumes "0 \<le> \<tau>" and "\<tau> < 1" and "g < 0"
  shows "rel_kat.H
  \<lceil>\<lambda>s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') = h \<and> s $ (\<restriction>\<^sub>V ''v'') = 0\<rceil> 
  ([x\<acute>=K g]{0..\<tau>} & (\<lambda> s. s $ (\<restriction>\<^sub>V ''y'') \<ge> 0))
  \<lceil>\<lambda>s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') \<le> h\<rceil>"
  apply(subst local_flow.sH_g_orbit[OF local_flow_cnst_acc])
  using assms by (auto simp: mult_nonneg_nonpos2) 
    (metis (full_types) less_eq_real_def program_vars_exhaust split_mult_neg_le)

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

lemma UNIV_3:"(UNIV::3 set) = {0, 1, 2}"
  apply safe using exhaust_3 three_eq_zero by(blast, auto)

lemma sum_axis_UNIV_3[simp]:"(\<Sum>j\<in>(UNIV::3 set). axis i 1 $ j \<cdot> f j) = (f::3 \<Rightarrow> real) i"
  unfolding axis_def UNIV_3 apply simp
  using exhaust_3 by force

text\<open> We can rewrite the original constant acceleration kinematics as a linear operator applied to 
a 3-dimensional vector. For that we take advantage of the following fact: \<close>

lemma "\<e> 1 = (\<chi> j::3. if j= 0 then 0 else if j = 1 then 1 else 0)"
  unfolding axis_def by(rule Cart_lambda_cong, simp)

abbreviation "constant_acceleration_kinematics_matrix \<equiv> 
  (\<chi> i::3. if i=0 then \<e> 1 else if i=1 then \<e> 2 else (0::real^3))"

abbreviation "constant_acceleration_kinematics_matrix_flow \<tau> s \<equiv> 
  (\<chi> i::3. if i=0 then s $ 2 \<cdot> \<tau> ^ 2/2 + s $ 1 \<cdot> \<tau> + s $ 0
   else if i=1 then s $ 2 \<cdot> \<tau> + s $ 1 else s $ 2)"

notation constant_acceleration_kinematics_matrix ("A")

notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>A")

text\<open> With these 2 definitions and the proof that linear systems of ODEs are Picard-Lindeloef, we 
can show that they form a pair of vector-field and its flow. \<close>

lemma entries_cnst_acc_matrix: "entries A = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma local_flow_cnst_acc_matrix:
  assumes "0 \<le> \<tau>" and "\<tau> < 1/9"
  shows "local_flow ((*v) A) {0..\<tau>} ((real CARD(3))\<^sup>2 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)) \<phi>\<^sub>A"
  unfolding local_flow_def local_flow_axioms_def apply safe
    apply(rule picard_lindeloef_linear_system[where A=A and t=\<tau>])
  using entries_cnst_acc_matrix assms apply(force, simp, force)
   apply(rule has_vderiv_on_vec_lambda)
   apply(auto intro!: poly_derivatives simp: matrix_vector_mult_def vec_eq_iff)
  using exhaust_3 by force

text\<open> Finally, we compute the wlp of this example and use it to verify the single-evolution ball again.\<close>

lemma single_evolution_ball_K:
  assumes "0 \<le> \<tau>" and "\<tau> < 1/9" 
  shows "rel_kat.H 
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> 
  ([x\<acute>=(*v) A]{0..\<tau>} & (\<lambda>s. s $ 0 \<ge> 0)) 
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(subst local_flow.sH_g_orbit[of _ _ "9 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)" \<phi>\<^sub>A])
  using local_flow_cnst_acc_matrix and assms apply force
  using assms by(auto simp: mult_nonneg_nonpos2)


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
  shows "(\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) is_diff_invariant_of (*v) C along {0..\<tau>}"
  apply(rule_tac diff_invariant_rules, clarsimp)
  apply(frule_tac i="0" in has_vderiv_on_vec_nth, drule_tac i="1" in has_vderiv_on_vec_nth)
  apply(rule_tac S="{0..\<tau>}" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: matrix_vector_mult_def)

lemma circular_motion_invariants:
  shows "rel_kat.H 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil> 
  ([x\<acute>=(*v) C]{0..\<tau>} & G) 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  apply(rule_tac C="\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2" in dCut)
   apply(rule_tac I="\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2" in dI)
  using circle_invariant apply(blast, force, force)
  by(rule dWeakening, auto)

\<comment> \<open>Proof of the same specification by providing solutions:\<close>

lemma entries_circ_matrix:"entries C = {0, - 1, 1}"
  apply (simp_all add: axis_def, safe)
  subgoal by(rule_tac x="0" in exI, simp)+
  subgoal by(rule_tac x="0" in exI, simp)+
  by(rule_tac x="1" in exI, simp)+

abbreviation "circular_motion_matrix_flow \<tau> s \<equiv> 
  (\<chi> i::2. if i=0 then s$0 \<cdot> cos \<tau> - s$1 \<cdot> sin \<tau> else s$0 \<cdot> sin \<tau> + s$1 \<cdot> cos \<tau>)"

notation circular_motion_matrix_flow ("\<phi>\<^sub>C")

lemma local_flow_circ_mtx: 
  assumes "0 \<le> \<tau>" and "\<tau> < 1/4" 
  shows "local_flow ((*v) C) {0..\<tau>} ((real CARD(2))\<^sup>2 \<cdot> (\<parallel>C\<parallel>\<^sub>m\<^sub>a\<^sub>x)) \<phi>\<^sub>C"
  unfolding local_flow_def local_flow_axioms_def apply safe
    apply(rule picard_lindeloef_linear_system)
  unfolding entries_circ_matrix using assms apply(simp_all)
   apply(rule has_vderiv_on_vec_lambda)
  apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by(force simp: vec_eq_iff)

lemma circular_motion:
  assumes "0 \<le> \<tau>" and "\<tau> < 1/4"
  shows "rel_kat.H 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>
  ([x\<acute>=(*v) C]{0..\<tau>} & G) 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  apply(subst local_flow.sH_g_orbit[OF local_flow_circ_mtx])
  using assms by simp_all

no_notation circular_motion_matrix ("C")

no_notation circular_motion_matrix_flow ("\<phi>\<^sub>C")


subsubsection\<open> Bouncing Ball with solution \<close>

text\<open> We revisit the previous dynamics for a constantly accelerated object modelled with the matrix
@{term K}. We compose the corresponding evolution command with an if-statement, and iterate this 
hybrid program to model a (completely elastic) ``bouncing ball''. Using the previously defined flow
for this dynamics, proving a specification for this hybrid program is merely an exercise of real 
arithmetic. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]: "0 \<le> x \<Longrightarrow> 0 > g \<Longrightarrow> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v \<Longrightarrow> (x::real) \<le> h"
proof-
  assume "0 \<le> x" and "0 > g" and "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
  then have "v \<cdot> v = 2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h \<and> 0 > g" by auto
  hence *:"v \<cdot> v = 2 \<cdot> g \<cdot> (x - h) \<and> 0 > g \<and> v \<cdot> v \<ge> 0" 
    using left_diff_distrib mult.commute by (metis zero_le_square) 
  from this have "(v \<cdot> v)/(2 \<cdot> g) = (x - h)" by auto 
  also from * have "(v \<cdot> v)/(2 \<cdot> g) \<le> 0"
    using divide_nonneg_neg by fastforce 
  ultimately have "h - x \<ge> 0" by linarith
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
  from this have *:"(g \<cdot> \<tau> + v)\<^sup>2 + 2 \<cdot> g \<cdot> h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  hence "2 \<cdot> g \<cdot> h + (- ((g \<cdot> \<tau>) + v))\<^sup>2 = 0"
    by (metis Groups.add_ac(2) power2_minus)
  thus "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
  from * show "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
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
  assumes "0 \<le> \<tau>" and "\<tau> < 1/9" 
  shows "rel_kat.H 
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> 
  ((([x\<acute>=\<lambda>s. A *v s]{0..\<tau>} & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule sH_star [of _ "\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"], simp)
   apply(rule sH_relcomp[where R="\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"])
    apply(subst local_flow.sH_g_orbit[of _ _ "9 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x)" \<phi>\<^sub>A])
  using local_flow_cnst_acc_matrix[OF assms] apply force
    apply(force simp: bb_real_arith)
   apply(rule sH_cond, subst sH_assign_iff, force simp: bb_real_arith)
  by(subst sH_H, simp_all, force simp: bb_real_arith)

subsubsection\<open> Bouncing Ball with invariants \<close>

text\<open> We prove again the bouncing ball but this time with differential invariants. \<close>

lemma gravity_invariant: "(\<lambda>s. s $ 2 < 0) is_diff_invariant_of (*v) A along {0..\<tau>}"
  apply(rule_tac \<theta>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in diff_invariant_rules(3), clarsimp)
  apply(drule_tac i="2" in has_vderiv_on_vec_nth)
  apply(rule_tac S="{0..\<tau>}" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: vec_eq_iff matrix_vector_mult_def)

lemma energy_conservation_invariant: 
  "(\<lambda>s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> h - s$1 \<cdot> s $ 1 = 0) is_diff_invariant_of (*v) A along {0..\<tau>}"
  apply(rule diff_invariant_rules, clarify)
  apply(frule_tac i="2" in has_vderiv_on_vec_nth)
  apply(frule_tac i="1" in has_vderiv_on_vec_nth)
  apply(drule_tac i="0" in has_vderiv_on_vec_nth)
  apply(rule_tac S="{0..\<tau>}" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: vec_eq_iff matrix_vector_mult_def)

lemma bouncing_ball_invariants: 
  "rel_kat.H 
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> 
  ((([x\<acute>=\<lambda>s. A *v s]{0..\<tau>} & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule sH_star [of _ "\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"], simp)
   apply(rule sH_relcomp[where R="\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"])
   apply(rule dCut[where C="\<lambda> s. s $ 2 < 0"])
    apply(rule_tac I="\<lambda> s. s $ 2 < 0" in dI)
  using gravity_invariant apply blast
     apply(force simp: p2r_def, force simp: p2r_def)
   apply(rule_tac C="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> h - s$1 \<cdot> s$1 = 0" in dCut)
    apply(rule_tac I="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> h - s$1 \<cdot> s$1 = 0" in dI)
  using energy_conservation_invariant apply blast
     apply(force simp: p2r_def, force simp: p2r_def)
    apply(rule dWeakening, force simp: p2r_def)
   apply(rule sH_cond, subst sH_assign_iff, force simp: bb_real_arith)
  by(subst sH_H, simp_all, force simp: bb_real_arith)

no_notation constant_acceleration_kinematics_matrix ("A")

no_notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>A")

end