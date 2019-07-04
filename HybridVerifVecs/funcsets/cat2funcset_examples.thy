theory cat2funcset_examples
  imports "../hs_prelims_matrices" cat2funcset

begin

subsection\<open> Examples \<close>

text\<open> The examples in this subsection show different approaches for the verification of hybrid 
systems. However, the general approach can be outlined as follows: First, we select a finite type to
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

typedef program_vars ="{''y'',''v''}"
  morphisms to_str to_var
  apply(rule_tac x="''y''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_program_vars:"CARD(program_vars) = 2"
  using type_definition.card type_definition_program_vars by fastforce

instance program_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV "{''y'',''v''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma program_vars_univD:"(UNIV::program_vars set) = {\<restriction>\<^sub>V ''y'', \<restriction>\<^sub>V ''v''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma program_vars_exhaust:"\<forall>x::program_vars. x = \<restriction>\<^sub>V ''y'' \<or> x = \<restriction>\<^sub>V ''v''"
  using program_vars_univD by auto

abbreviation "constant_acceleration_kinematics g s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''y'') then s $ (\<restriction>\<^sub>V ''v'') else g)"

notation constant_acceleration_kinematics ("K")

lemma cnst_acc_continuous:
  fixes X::"(real^program_vars) set"
  shows "continuous_on X (K g)"
  apply(rule continuous_on_vec_lambda)
  unfolding continuous_on_def apply clarsimp
  by(intro tendsto_intros)

lemma picard_lindeloef_cnst_acc:
  fixes g::real assumes "0 \<le> t" and "t < 1 "
  shows "picard_lindeloef (\<lambda>t. K g) {0..t} 1 0"
  unfolding picard_lindeloef_def apply(simp add: lipschitz_on_def assms, safe)
  apply(rule_tac t="UNIV" and f="snd" in continuous_on_compose2)
  apply(simp_all add: cnst_acc_continuous continuous_on_snd)
   apply(simp add: dist_vec_def L2_set_def dist_real_def)
   apply(subst program_vars_univD, subst program_vars_univD)
   apply(simp_all add: to_var_inject)
  using assms by linarith

abbreviation "constant_acceleration_kinematics_flow g t s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''y'') then g \<cdot> t ^ 2/2 + s $ (\<restriction>\<^sub>V ''v'') \<cdot> t + s $ (\<restriction>\<^sub>V ''y'') 
        else g \<cdot> t + s $ (\<restriction>\<^sub>V ''v''))"

notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

lemma local_flow_cnst_acc:
  assumes "0 \<le> t" and "t < 1 "
  shows "local_flow (K g) {0..t} 1 (\<phi>\<^sub>K g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using assms picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda)
  using poly_derivatives(3,4) program_vars_exhaust
   apply(simp_all add: to_var_inject vec_eq_iff has_vderiv_on_def has_vector_derivative_def)
  using program_vars_exhaust by blast

lemma ffb_cnst_acc:
  assumes "0 \<le> t" and "t < 1"
  shows "fb\<^sub>\<F> ([x\<acute>=K g]{0..t} & G) Q = {s. \<forall>\<tau>\<in>{0..t}. (G \<rhd> (\<lambda>r. \<phi>\<^sub>K g r s){0--\<tau>}) \<longrightarrow> (\<phi>\<^sub>K g \<tau> s) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "K g" _ 1 "(\<lambda> t x. \<phi>\<^sub>K g t x)"])
  using local_flow_cnst_acc and assms by auto

lemma single_evolution_ball:
  fixes H::real assumes "0 \<le> t" and "t < 1" and "g < 0"
  shows "{s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') = H \<and> s $ (\<restriction>\<^sub>V ''v'') = 0} 
  \<le> fb\<^sub>\<F> ([x\<acute>=K g]{0..t} & (\<lambda> s. s $ (\<restriction>\<^sub>V ''y'') \<ge> 0))
  {s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') \<le> H}"
  apply(subst ffb_cnst_acc)
  using assms by(auto simp: mult_nonpos_nonneg)

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
Isabelle. However, there are still lemmas to prove about them in order to do verification of hybrid
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
  (\<chi> i. if i= (0::3) then axis (1::3) (1::real) else if i= 1 then axis 2 1 else 0)"

abbreviation "constant_acceleration_kinematics_matrix_flow t s \<equiv> 
  (\<chi> i. if i= (0::3) then s $ 2 \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0
   else if i=1 then s $ 2 \<cdot> t + s $ 1 else s $ 2)"

notation constant_acceleration_kinematics_matrix ("K")

notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>K")

text\<open> With these 2 definitions and the proof that linear systems of ODEs are Picard-Lindeloef, we 
can show that they form a pair of vector-field and its flow. \<close>

lemma entries_cnst_acc_matrix: "entries K = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma picard_lindeloef_cnst_acc_matrix:
  assumes "0 \<le> t" and "t < 1/9"
  shows "picard_lindeloef (\<lambda> t s. K *v s) {0..t} ((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x)) 0"
  apply(rule picard_lindeloef_linear_system)
  unfolding entries_cnst_acc_matrix using assms by auto

lemma local_flow_cnst_acc_matrix:
  assumes "0 \<le> t" and "t < 1/9"
  shows "local_flow ((*v) K) {0..t} ((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x)) \<phi>\<^sub>K"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_cnst_acc_matrix[OF assms] apply blast
   apply(rule has_vderiv_on_vec_lambda)
  using poly_derivatives(1,3, 4) 
   apply(force simp: matrix_vector_mult_def)
  using exhaust_3 by(force simp: matrix_vector_mult_def vec_eq_iff)

text\<open> Finally, we compute the wlp and use it to verify the single-evolution ball again.\<close>

lemma ffb_cnst_acc_mtx:
  assumes "0 \<le> t" and "t < 1/9"
  shows "fb\<^sub>\<F> ([x\<acute>=(*v) K]{0..t} & G) Q = {s. \<forall>\<tau>\<in>{0..t}. (G \<rhd> (\<lambda>r. \<phi>\<^sub>K r s){0--\<tau>}) \<longrightarrow> (\<phi>\<^sub>K \<tau> s) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "(*v) K" _ "((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x))" \<phi>\<^sub>K])
  using local_flow_cnst_acc_matrix and assms by auto

lemma single_evolution_ball_matrix:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "{s. 0 \<le> s $ 0 \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} 
  \<le> fb\<^sub>\<F> ([x\<acute>=(*v) K]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(subst ffb_cnst_acc_mtx)
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

lemma [simp]:"i \<noteq> (0::2) \<longrightarrow> i = 1" 
  using exhaust_2 by fastforce

lemma UNIV_2:"(UNIV::2 set) = {0, 1}"
  apply safe using exhaust_2 two_eq_zero by auto

abbreviation "circular_motion_matrix \<equiv> 
  (\<chi> i. if i= (0::2) then axis (1::2) (- 1::real) else axis 0 1)"

notation circular_motion_matrix ("C")

lemma circle_invariant:
  assumes "0 < R"
  shows "(\<lambda>s. R\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) is_diff_invariant_of (*v) C along {0..t}"
  apply(rule_tac ode_invariant_rules, clarsimp)
  apply(frule_tac i="0" in has_vderiv_on_vec_nth, drule_tac i="1" in has_vderiv_on_vec_nth)
  apply(unfold has_vderiv_on_def has_vector_derivative_def, clarsimp)
  apply(erule_tac x="r" in ballE)+
    apply(simp add: matrix_vector_mult_def has_vderiv_on_vec_lambda)
  subgoal for x \<tau> r apply(rule_tac f'1="\<lambda>t. 0" and g'1="\<lambda>t. 0" in derivative_eq_intros(11), simp_all)
     apply(rule_tac f'1="\<lambda>t. - 2 \<cdot> (x r $ 0) \<cdot> (t \<cdot> x r $ 1)" 
        and g'1="\<lambda>t. 2 \<cdot> (x r $ 1) \<cdot> t \<cdot> x r $ 0" in derivative_eq_intros(8), simp_all)
       apply(rule_tac f'1="\<lambda>t. - (t \<cdot> x r $ 1)" in derivative_eq_intros(15))
        apply(rule_tac t="{0--\<tau>}" and s="{0..t}" in has_derivative_within_subset)
         apply(simp, simp add: closed_segment_eq_real_ivl, force)
       apply(rule_tac f'1="\<lambda>t. (t \<cdot> x r $ 0)" in derivative_eq_intros(15))
        apply(rule_tac t="{0--\<tau>}" and s="{0..t}" in has_derivative_within_subset)
    by(simp, simp add: closed_segment_eq_real_ivl, force)
  by(auto simp: closed_segment_eq_real_ivl)

lemma circular_motion_invariants:
  assumes "(R::real) > 0"
  shows"{s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2} 
  \<le> fb\<^sub>\<F> ([x\<acute>=(*v) C]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
  {s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2}"
  using assms apply(rule_tac C="\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2" in dCut)
   apply(rule_tac I="\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2" in dInvariant)
  using circle_invariant apply blast
  by(rule dWeakening, auto)

\<comment> \<open>Proof of the same specification by providing solutions:\<close>

lemma entries_circ_mtx:"entries C = {0, - 1, 1}"
  apply (simp_all add: axis_def, safe)
  subgoal by(rule_tac x="0" in exI, simp)+
  subgoal by(rule_tac x="0" in exI, simp)+
  by(rule_tac x="1" in exI, simp)+

lemma picard_lindeloef_circ_mtx:
  assumes "0 \<le> t" and "t < 1/4" 
  shows "picard_lindeloef (\<lambda>t. (*v) C) {0..t} ((real CARD(2))\<^sup>2 \<cdot> (\<parallel>C\<parallel>\<^sub>m\<^sub>a\<^sub>x)) 0"
  apply(rule picard_lindeloef_linear_system)
  unfolding entries_circ_mtx using assms by auto

abbreviation "circular_motion_matrix_flow t s \<equiv> (\<chi> i. if i= (0::2) then 
s$0 \<cdot> cos t - s$1 \<cdot> sin t else s$0 \<cdot> sin t + s$1 \<cdot> cos t)"

notation circular_motion_matrix_flow ("\<phi>\<^sub>C")

lemma local_flow_circ_mtx: 
  assumes "0 \<le> t" and "t < 1/4" 
  shows "local_flow ((*v) C) {0..t} ((real CARD(2))\<^sup>2 \<cdot> (\<parallel>C\<parallel>\<^sub>m\<^sub>a\<^sub>x)) \<phi>\<^sub>C"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_circ_mtx assms apply blast
   apply(rule has_vderiv_on_vec_lambda)
   apply(simp add: matrix_vector_mult_def has_vderiv_on_def has_vector_derivative_def, safe)
  subgoal for s i x
    apply(rule_tac f'1="\<lambda>t. - s$0 \<cdot> (t \<cdot> sin x)" and g'1="\<lambda>t. s$1 \<cdot> (t \<cdot> cos x)"in derivative_eq_intros(11))
      apply(rule derivative_eq_intros(6)[of cos "(\<lambda>xa. - (xa \<cdot> sin x))"])
       apply(rule_tac Db1="1" in derivative_eq_intros(58))
        apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
     apply(rule derivative_eq_intros(6)[of sin "(\<lambda>xa. (xa \<cdot> cos x))"])
      apply(rule_tac Db1="1" in derivative_eq_intros(55))
       apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
    by (simp add: Groups.mult_ac(3) Rings.ring_distribs(4))
  subgoal for s i x
    apply(rule_tac f'1="\<lambda>t. s$0 \<cdot> (t \<cdot> cos x)" and g'1="\<lambda>t. - s$1 \<cdot> (t \<cdot> sin x)"in derivative_eq_intros(8))
      apply(rule derivative_eq_intros(6)[of sin "(\<lambda>xa. xa \<cdot> cos x)"])
       apply(rule_tac Db1="1" in derivative_eq_intros(55))
        apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
     apply(rule derivative_eq_intros(6)[of cos "(\<lambda>xa. - (xa \<cdot> sin x))"])
      apply(rule_tac Db1="1" in derivative_eq_intros(58))
       apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
    by (simp add: Groups.mult_ac(3) Rings.ring_distribs(4))
  using exhaust_2 two_eq_zero by(force simp: vec_eq_iff)

lemma ffb_circ_mtx:
  assumes "0 \<le> t" and "t < 1/4"
  shows "fb\<^sub>\<F> ([x\<acute>=\<lambda>s. C *v s]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (\<phi>\<^sub>C r x)) \<longrightarrow> (\<phi>\<^sub>C \<tau> x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. C *v s" _ "((real CARD(2))\<^sup>2 \<cdot> (\<parallel>C\<parallel>\<^sub>m\<^sub>a\<^sub>x))"
"(\<lambda> t x. \<phi>\<^sub>C t x)"])
  using local_flow_circ_mtx and assms by auto

lemma circular_motion:
  assumes "0 \<le> t" and "t < 1/4" and "(R::real) > 0"
  shows "{s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> 
  ([x\<acute>=\<lambda>s. C *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
  {s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2}"
  apply(subst ffb_circ_mtx)
  using assms by auto

no_notation circular_motion_matrix ("C")

no_notation circular_motion_matrix_flow ("\<phi>\<^sub>C")


subsubsection\<open> Bouncing Ball with solution \<close>

text\<open> We revisit the previous dynamics for a constantly accelerated object modelled with the matrix
@{term K}. We compose the corresponding evolution command with an if-statement, and iterate this 
hybrid program to model a (completely elastic) ``bouncing ball''. Using the previously defined flow
for this dynamics, proving a specification for this hybrid program is merely an exercise of real 
arithmetic. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]:"0 \<le> x \<Longrightarrow> 0 > g \<Longrightarrow> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H + v \<cdot> v \<Longrightarrow> (x::real) \<le> H"
proof-
  assume "0 \<le> x" and "0 > g" and "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H + v \<cdot> v"
  then have "v \<cdot> v = 2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> H \<and> 0 > g" by auto
  hence *:"v \<cdot> v = 2 \<cdot> g \<cdot> (x - H) \<and> 0 > g \<and> v \<cdot> v \<ge> 0" 
    using left_diff_distrib mult.commute by (metis zero_le_square) 
  from this have "(v \<cdot> v)/(2 \<cdot> g) = (x - H)" by auto 
  also from * have "(v \<cdot> v)/(2 \<cdot> g) \<le> 0"
    using divide_nonneg_neg by fastforce 
  ultimately have "H - x \<ge> 0" by linarith
  thus ?thesis by auto
qed

lemma [bb_real_arith]:
  assumes invar:"2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H + v \<cdot> v"
    and pos:"g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real) = 0"
  shows "2 \<cdot> g \<cdot> H + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    and "2 \<cdot> g \<cdot> H + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
proof-
  from pos have "g \<cdot> \<tau>\<^sup>2  + 2 \<cdot> v \<cdot> \<tau> + 2 \<cdot> x = 0" by auto
  then have "g\<^sup>2  \<cdot> \<tau>\<^sup>2  + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + v\<^sup>2 + 2 \<cdot> g \<cdot> H = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  from this have *:"(g \<cdot> \<tau> + v)\<^sup>2 + 2 \<cdot> g \<cdot> H = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  hence "2 \<cdot> g \<cdot> H + (- ((g \<cdot> \<tau>) + v))\<^sup>2 = 0"
    by (metis Groups.add_ac(2) power2_minus)
  thus "2 \<cdot> g \<cdot> H + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
  from * show "2 \<cdot> g \<cdot> H + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
qed
    
lemma [bb_real_arith]:
  assumes invar:"2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H + v \<cdot> v"
  shows "2 \<cdot> g \<cdot> (g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real)) = 
  2 \<cdot> g \<cdot> H + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v))" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x" 
      apply(subst Rat.sign_simps(18))+ 
      by(auto simp: semiring_normalization_rules(29))
    also have "... = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> H + v \<cdot> v" (is "... = ?middle")
      by(subst invar, simp)
    finally have "?lhs = ?middle".
  moreover 
  {have "?rhs = g \<cdot> g \<cdot> (\<tau> \<cdot> \<tau>) + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> H + v \<cdot> v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "{s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> fb\<^sub>\<F> 
  (kstar (([x\<acute>=\<lambda>s. K *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(rule ffb_starI[of _ "{s. 0 \<le> s $ (0::3) \<and> 0 > s $ 2 \<and> 
  2 \<cdot> s $ 2 \<cdot> s $ 0 = 2 \<cdot> s $ 2 \<cdot> H + (s $ 1 \<cdot> s $ 1)}"])
  apply(clarsimp, simp only: ffb_kcomp)
    apply(subst ffb_cnst_acc_mtx)
  using assms apply(simp, simp, clarsimp)
    apply(rule ffb_if_then_elseD)
  by(auto simp: bb_real_arith)

subsubsection\<open> Bouncing Ball with invariants \<close>

text\<open> We prove again the bouncing ball but this time with differential invariants. \<close>

lemma gravity_invariant: "(\<lambda>s. s $ 2 < 0) is_diff_invariant_of (*v) K along {0..t}"
  apply(rule_tac \<theta>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in ode_invariant_rules(3), clarsimp)
  apply(drule_tac i="2" in has_vderiv_on_vec_nth)
  apply(unfold has_vderiv_on_def has_vector_derivative_def)
  apply(erule_tac x="r" in ballE, simp add: matrix_vector_mult_def)
   apply(rule_tac f'1="\<lambda>s. 0" in derivative_eq_intros(10))
  by(auto simp: closed_segment_eq_real_ivl has_derivative_within_subset)

lemma energy_conservation_invariant: 
"(\<lambda>s. 2 \<cdot> s $ 2 \<cdot> s $ 0 - 2 \<cdot> s $ 2 \<cdot> H - s $ 1 \<cdot> s $ 1 = 0) is_diff_invariant_of (*v) K along {0..t}"
  apply(rule ode_invariant_rules, clarify)
  apply(frule_tac i="2" in has_vderiv_on_vec_nth)
  apply(frule_tac i="1" in has_vderiv_on_vec_nth)
  apply(drule_tac i="0" in has_vderiv_on_vec_nth)
  apply(unfold has_vderiv_on_def has_vector_derivative_def)
  apply(erule_tac x="r" in ballE, simp_all add: matrix_vector_mult_def)+
     apply(rule_tac f'1="\<lambda>t. 2 \<cdot> x r $ 2 \<cdot> (t \<cdot> x r $ 1)" 
      and g'1="\<lambda>t. 2 \<cdot> (t \<cdot> (x r $ 1 \<cdot> x r $ 2))" in derivative_eq_intros(11))
     apply(rule_tac f'1="\<lambda>t. 2 \<cdot> x r $ 2 \<cdot> (t \<cdot> x r $ 1)" and g'1="\<lambda>t. 0" in derivative_eq_intros(11))
     apply(rule_tac f'1="\<lambda>t. 0" and g'1="(\<lambda>xa. xa \<cdot> x r $ 1)" in derivative_eq_intros(12))
     apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(6))
     apply(simp_all add: has_derivative_within_subset closed_segment_eq_real_ivl)
     apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(7))
    apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(6))
     apply(simp_all add: has_derivative_within_subset)
  apply(rule_tac f'1="(\<lambda>xa. xa \<cdot> x r $ 2)" and g'1="(\<lambda>xa. xa \<cdot> x r $ 2)" in derivative_eq_intros(12))
  by(simp_all add: has_derivative_within_subset)

lemma bouncing_ball_invariants:
  shows "{s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> fb\<^sub>\<F> 
  (kstar (([x\<acute>=\<lambda>s. K *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(rule_tac I="{s. 0 \<le> s$0 \<and> 0 > s$2 \<and> 2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> H + (s$1 \<cdot> s$1)}" in ffb_starI)
    apply(clarsimp, simp only: ffb_kcomp)
   apply(rule dCut[where C="\<lambda> s. s $ 2 < 0"])
    apply(rule_tac I="\<lambda> s. s $ 2 < 0" in dI)
  using gravity_invariant apply(blast, force, force)
   apply(rule_tac C="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1 = 0" in dCut)
    apply(rule_tac I="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1 = 0" in dI)
  using energy_conservation_invariant apply(blast, force, force)
   apply(rule dWeakening)
   apply(rule ffb_if_then_else)
  by(auto simp: bb_real_arith le_fun_def)

no_notation constant_acceleration_kinematics_matrix ("K")

no_notation constant_acceleration_kinematics_matrix_flow ("\<phi>\<^sub>K")


subsubsection\<open> Bouncing Ball with exponential solution \<close>

text\<open> In our final example, we prove again the bouncing ball specification but this time we do it 
with the general solution for linear systems.\<close>

abbreviation "constant_acceleration_kinematics_sq_mtx \<equiv> sq_mtx_chi constant_acceleration_kinematics_matrix"

notation constant_acceleration_kinematics_sq_mtx ("K")

lemma max_norm_cnst_acc_sq_mtx: "\<parallel>to_vec K\<parallel>\<^sub>m\<^sub>a\<^sub>x = 1"
proof-
  have "{to_vec K $ i $ j |i j. s2p UNIV i \<and> s2p UNIV j} = {0, 1}"
    apply (simp_all add: axis_def, safe)
    by(rule_tac x="1" in exI, simp)+
  thus ?thesis
    by auto
qed

lemma ffb_cnst_acc_sq_mtx:
  assumes "0 \<le> t" and "t < 1/9"
  shows "fb\<^sub>\<F> ([x\<acute>=(*\<^sub>V) K]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G ((exp (r *\<^sub>R K)) *\<^sub>V x)) \<longrightarrow> ((exp (\<tau> *\<^sub>R K)) *\<^sub>V x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "(*\<^sub>V) K" _ "((real CARD(3))\<^sup>2 \<cdot> (\<parallel>to_vec K\<parallel>\<^sub>m\<^sub>a\<^sub>x))" 
"(\<lambda>t x. (exp (t *\<^sub>R K)) *\<^sub>V x)"])
   apply(rule local_flow_exp)
  using max_norm_cnst_acc_sq_mtx assms by auto

lemma exp_cnst_acc_sq_mtx_simps:
 "exp (\<tau> *\<^sub>R K) $$ 0 $ 0 = 1" "exp (\<tau> *\<^sub>R K) $$ 0 $ 1 = \<tau>" "exp (\<tau> *\<^sub>R K) $$ 0 $ 2 = \<tau>^2/2"
 "exp (\<tau> *\<^sub>R K) $$ 1 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R K) $$ 1 $ 2 = \<tau>"
 "exp (\<tau> *\<^sub>R K) $$ 2 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 2 = 1"
  sorry

lemma bouncing_ball_sq_mtx:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "{s. 0 \<le> s $ 0 \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> fb\<^sub>\<F> 
  (kstar (([x\<acute>=(*\<^sub>V) K]{0..t} & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(rule ffb_starI[of _ "{s. 0 \<le> s $ (0::3) \<and> 0 > s $ 2 \<and> 
  2 \<cdot> s $ 2 \<cdot> s $ 0 = 2 \<cdot> s $ 2 \<cdot> H + (s $ 1 \<cdot> s $ 1)}"])
    apply(clarsimp, simp only: ffb_kcomp)
   apply(subst ffb_cnst_acc_sq_mtx)
  using assms apply(simp, simp, clarify)
  apply(rule ffb_if_then_elseD, clarsimp)
   apply(simp_all add: sq_mtx_vec_prod_eq)
  unfolding UNIV_3 apply(simp_all add: exp_cnst_acc_sq_mtx_simps)
  subgoal for x using bb_real_arith(3)[of "x $ 2"]
    by (simp add: add.commute mult.commute)
  subgoal for x \<tau> using bb_real_arith(4)[where g="x $ 2" and v="x $ 1"]
    by(simp add: add.commute mult.commute)
  by (force simp: bb_real_arith)

end