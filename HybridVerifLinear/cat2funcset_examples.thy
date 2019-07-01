theory cat2funcset_examples
  imports cat2funcset hs_prelims_matrices

begin

subsection\<open> Examples \<close>

text\<open> Here we do our first verification example: the single-evolution ball. We do it in two ways.
The first one provides (1) a finite type and (2) its corresponding problem-specific vector-field and
flow. The second approach uses an existing finite type and defines a more general vector-field which
is later instantiated to the problem at hand.\<close>

subsubsection\<open> Specific vector field \<close>

text\<open> We define a finite type of three elements. All the lemmas below proven about this type must
exist in order to do the verification example.\<close>

typedef program_vars ="{''y'',''v'',''g''}"
  morphisms to_str to_var
  apply(rule_tac x="''y''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_program_vars:"CARD(program_vars) = 3"
  using type_definition.card type_definition_program_vars by fastforce

instance program_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV "{''y'',''v'',''g''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma program_vars_univD:"(UNIV::program_vars set) = {\<restriction>\<^sub>V ''y'', \<restriction>\<^sub>V ''v'', \<restriction>\<^sub>V ''g''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma program_vars_exhaust:"\<forall>x::program_vars. x = \<restriction>\<^sub>V ''y'' \<or> x = \<restriction>\<^sub>V ''v'' \<or> x = \<restriction>\<^sub>V ''g''"
  using program_vars_univD by auto

text\<open> Next we use our recently created type to work in a 3-dimensional vector space. We define the
vector field and a flow-candidate for the single-evolution ball on this vector space. Then we follow 
the standard procedure to prove that they are in fact a Lipschitz vector-field and a its flow. \<close>

abbreviation "free_fall_kinematics s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''y'') then s $ (\<restriction>\<^sub>V ''v'') else if i=(\<restriction>\<^sub>V ''v'') then s $ (\<restriction>\<^sub>V ''g'') else 0)"

abbreviation "free_fall_flow t s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''y'') then s $ (\<restriction>\<^sub>V ''g'') \<cdot> t ^ 2/2 + s $ (\<restriction>\<^sub>V ''v'') \<cdot> t + s $ (\<restriction>\<^sub>V ''y'')
   else if i=(\<restriction>\<^sub>V ''v'') then s $ (\<restriction>\<^sub>V ''g'') \<cdot> t + s $ (\<restriction>\<^sub>V ''v'') else s $ (\<restriction>\<^sub>V ''g''))"

lemma bounded_linear_free_fall_kinematics: "bounded_linear free_fall_kinematics"
  apply unfold_locales
    apply(simp_all add: plus_vec_def scaleR_vec_def ext norm_vec_def L2_set_def)
  apply(rule_tac x="1" in exI, clarsimp)
  apply(subst program_vars_univD, subst program_vars_univD)
  by(auto simp: to_var_inject)

lemma free_fall_kinematics_continuous_on:
  fixes X::"(real^program_vars) set"
  shows "continuous_on X free_fall_kinematics"
  using bounded_linear_free_fall_kinematics linear_continuous_on by blast

lemma free_fall_kinematics_is_picard_lindeloef:
  assumes "0 \<le> t" and "t < 1 "
  shows "picard_lindeloef (\<lambda> t (s::real^program_vars). free_fall_kinematics s) {0..t} 1 0"
  unfolding picard_lindeloef_def apply(simp add: lipschitz_on_def assms, safe)
  apply(rule_tac t="UNIV" and f="snd" in continuous_on_compose2)
  apply(simp_all add: free_fall_kinematics_continuous_on continuous_on_snd)
   apply(simp add: dist_vec_def L2_set_def dist_real_def)
   apply(subst program_vars_univD, subst program_vars_univD)
   apply(simp_all add: to_var_inject)
  using assms by linarith

lemma local_flow_free_fall_flow:
  assumes "0 \<le> t" and "t < 1 "
  shows "local_flow free_fall_kinematics {0..t} 1 free_fall_flow"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using assms free_fall_kinematics_is_picard_lindeloef apply blast
   apply(rule has_vderiv_on_vec_lambda)
  using poly_derivatives(3,4) program_vars_exhaust
   apply(simp_all add: to_var_inject vec_eq_iff has_vderiv_on_def has_vector_derivative_def)
  using program_vars_exhaust by blast

text\<open> We end the first example by computing the wlp of the kinematics for the single-evolution
ball and then using it to verify "its safety".\<close>

lemma free_fall_flow_DS:
  assumes "0 \<le> t" and "t < 1"
  shows "fb\<^sub>\<F> ([x\<acute>=free_fall_kinematics]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (free_fall_flow r x)) \<longrightarrow> (free_fall_flow \<tau> x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "free_fall_kinematics" _ 1 "(\<lambda> t x. free_fall_flow t x)"])
  using local_flow_free_fall_flow and assms by auto

lemma single_evolution_ball:
  fixes H::real assumes "0 \<le> t" and "t < 1" 
  shows "{s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') = H \<and> s $ (\<restriction>\<^sub>V ''v'') = 0 \<and> 0 > s $ (\<restriction>\<^sub>V ''g'')} 
  \<le> fb\<^sub>\<F> ([x\<acute>=free_fall_kinematics]{0..t} & (\<lambda> s. s $ (\<restriction>\<^sub>V ''y'') \<ge> 0))
  {s. 0 \<le> s $ (\<restriction>\<^sub>V ''y'') \<and> s $ (\<restriction>\<^sub>V ''y'') \<le> H}"
  apply(subst free_fall_flow_DS)
  by(auto simp: assms mult_nonneg_nonpos2)

subsubsection \<open>General vector field \<close>

text \<open>It turns out that there is already a 3-element type:\<close>
term "x::3"
lemma "CARD(program_vars) = CARD(3)"
  unfolding number_of_program_vars by simp

text \<open>In fact, for each natural number $n$ there is already a corresponding $n$-element type in 
Isabelle. However, there are still some lemmas that one needs to prove in order to use them for 
verification in $n$-dimensional vector spaces.\<close>

lemma exhaust_5: \<comment> \<open>The analog for 3 has already been proven in Analysis.\<close>
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

text\<open> Next, we prove that every linear system of differential equations (i.e. it can be rewritten 
as $x' = A\cdot x$ ) satisfies the conditions of the Picard-Lindeloef theorem: \<close>

lemma matrix_lipschitz_constant:
  fixes A::"real^('n::finite)^'n"
  shows "dist (A *v x) (A *v y) \<le> (real CARD('n))\<^sup>2 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) \<cdot> dist x y"
  unfolding dist_norm matrix_vector_mult_diff_distrib[THEN sym]
proof(subst mult_norm_matrix_sgn_eq[symmetric])
  have "\<parallel>A\<parallel>\<^sub>o\<^sub>p \<le> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) \<cdot> (real CARD('n) \<cdot> real CARD('n))"
    by (metis (no_types) Groups.mult_ac(2) op_norm_le_max_norm)
  then have "(\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<cdot> (\<parallel>x - y\<parallel>) \<le> (real CARD('n))\<^sup>2 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) \<cdot> (\<parallel>x - y\<parallel>)"
    by (simp add: cross3_simps(11) mult_left_mono semiring_normalization_rules(29))
  also have "(\<parallel>A *v sgn (x - y)\<parallel>) \<cdot> (\<parallel>x - y\<parallel>) \<le> (\<parallel>A\<parallel>\<^sub>o\<^sub>p) \<cdot> (\<parallel>x - y\<parallel>)"
    by (simp add: norm_sgn_le_op_norm cross3_simps(11) mult_left_mono) 
  ultimately show "(\<parallel>A *v sgn (x - y)\<parallel>) \<cdot> (\<parallel>x - y\<parallel>) \<le> (real CARD('n))\<^sup>2 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x) \<cdot> (\<parallel>x - y\<parallel>)"
    using order_trans_rules(23) by blast
qed

lemma picard_lindeloef_linear_system:
  fixes A::"real^('n::finite)^'n" 
  assumes "0 < ((real CARD('n))\<^sup>2 \<cdot> (\<parallel>A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_lindeloef (\<lambda> t s. A *v s) {0..t} ?L 0"
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

text\<open> We can rewrite the original free-fall kinematics as a linear operator applied to a 3-dimensional
vector. For that we take advantage of the following fact: \<close>

lemma "axis (1::3) (1::real) = (\<chi> j. if j= 0 then 0 else if j = 1 then 1 else 0)"
  unfolding axis_def by(rule Cart_lambda_cong, simp)

abbreviation "K \<equiv> (\<chi> i. if i= (0::3) then axis (1::3) (1::real) else if i= 1 then axis 2 1 else 0)"

abbreviation "flow_for_K t s \<equiv> (\<chi> i. if i= (0::3) then s $ 2 \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0
else if i=1 then s $ 2 \<cdot> t + s $ 1 else s $ 2)"

text\<open> With these 2 definitions and the proof that linear systems of ODEs are Picard-Lindeloef, we can 
show that they form a pair of vector-field and its flow. \<close>

lemma entries_K:"entries K = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma K_is_picard_lindeloef:"0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> 
picard_lindeloef (\<lambda> t s. K *v s) {0..t} ((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x)) 0"
  apply(rule picard_lindeloef_linear_system)
  unfolding entries_K by auto

lemma local_flow_flow_for_K:
"0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> local_flow (\<lambda>s. K *v s) {0..t} ((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x)) flow_for_K"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using K_is_picard_lindeloef apply blast
   apply(rule has_vderiv_on_vec_lambda)
  using poly_derivatives(1,3, 4) 
   apply(force simp: matrix_vector_mult_def)
  using exhaust_3 by(force simp: matrix_vector_mult_def vec_eq_iff)

text\<open> Finally, we compute the wlp of this example and use it to verify the single-evolution ball again.\<close>

lemma flow_for_K_DS:
  assumes "0 \<le> t" and "t < 1/9"
  shows "fb\<^sub>\<F> ([x\<acute>=\<lambda>s. K *v s]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (flow_for_K r x)) \<longrightarrow> (flow_for_K \<tau> x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. K *v s" _ "((real CARD(3))\<^sup>2 \<cdot> (\<parallel>K\<parallel>\<^sub>m\<^sub>a\<^sub>x))" 
"(\<lambda> t x. flow_for_K t x)"])
  using local_flow_flow_for_K and assms by auto

lemma single_evolution_ball_K:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "{s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} 
  \<le> fb\<^sub>\<F> ([x\<acute>=\<lambda>s. K *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
        {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(subst flow_for_K_DS)
  using assms by(auto simp: mult_nonneg_nonpos2)

subsubsection\<open> Circular motion with invariants \<close>

lemma two_eq_zero: "(2::2) = 0" by simp

lemma [simp]:"i \<noteq> (0::2) \<longrightarrow> i = 1" using exhaust_2 by fastforce

lemma UNIV_2:"(UNIV::2 set) = {0, 1}"
  apply safe using exhaust_2 two_eq_zero by auto

abbreviation "Circ \<equiv> (\<chi> i. if i= (0::2) then axis (1::2) (- 1::real) else axis 0 1)"

abbreviation "flow_for_Circ t s \<equiv> (\<chi> i. if i= (0::2) then 
s$0 \<cdot> cos t - s$1 \<cdot> sin t else s$0 \<cdot> sin t + s$1 \<cdot> cos t)"

lemma entries_Circ:"entries Circ = {0, - 1, 1}"
  apply (simp_all add: axis_def, safe)
  subgoal by(rule_tac x="0" in exI, simp)+
  subgoal by(rule_tac x="0" in exI, simp)+
  by(rule_tac x="1" in exI, simp)+

lemma Circ_is_picard_lindeloef:"0 \<le> t \<Longrightarrow> t < 1/4 \<Longrightarrow> 
picard_lindeloef (\<lambda> t s. Circ *v s) {0..t} ((real CARD(2))\<^sup>2 \<cdot> (\<parallel>Circ\<parallel>\<^sub>m\<^sub>a\<^sub>x)) 0"
  apply(rule picard_lindeloef_linear_system)
  unfolding entries_Circ by auto

lemma local_flow_flow_for_Circ: "0 \<le> t \<Longrightarrow> t < 1/4 \<Longrightarrow> 
local_flow (\<lambda>s. Circ *v s) {0..t} ((real CARD(2))\<^sup>2 \<cdot> (\<parallel>Circ\<parallel>\<^sub>m\<^sub>a\<^sub>x)) flow_for_Circ"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using Circ_is_picard_lindeloef apply blast
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

lemma flow_for_Circ_DS:
  assumes "0 \<le> t" and "t < 1/4"
  shows "fb\<^sub>\<F> ([x\<acute>=\<lambda>s. Circ *v s]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (flow_for_Circ r x)) \<longrightarrow> (flow_for_Circ \<tau> x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. Circ *v s" _ "((real CARD(2))\<^sup>2 \<cdot> (\<parallel>Circ\<parallel>\<^sub>m\<^sub>a\<^sub>x))"
"(\<lambda> t x. flow_for_Circ t x)"])
  using local_flow_flow_for_Circ and assms by auto

lemma circular_motion:
  assumes "0 \<le> t" and "t < 1/4" and "(R::real) > 0"
  shows"{s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> 
  ([x\<acute>=\<lambda>s. Circ *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
  {s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2}"
  apply(subst flow_for_Circ_DS)
  using assms by auto

lemma circle_invariant:
  assumes "0 < R"
  shows "(\<lambda>s. R\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) is_diff_invariant_of (*v) Circ along {0..t}"
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
  shows"{s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> 
  ([x\<acute>=\<lambda>s. Circ *v s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0))
  {s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2}"
  using assms apply(rule_tac C="\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2" in dCut)
   apply(rule_tac I="\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2" in dInvariant)
  using circle_invariant apply blast
  by(rule dWeakening, auto)

subsubsection\<open> Bouncing Ball with solution \<close>
text\<open> Armed now with two vector fields for free-fall kinematics and their respective flows, proving
the safety of a ``bouncing ball'' is merely an exercise of real arithmetic: \<close>

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
    apply(subst flow_for_K_DS)
  using assms apply(simp, simp, clarsimp)
    apply(rule ffb_if_then_elseD)
  by(auto simp: bb_real_arith)

subsubsection\<open> Bouncing Ball with invariants \<close>

lemma gravity_is_invariant: "(\<lambda>s. s $ 2 < 0) is_diff_invariant_of (*v) K along {0..t}"
  apply(rule_tac \<theta>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in ode_invariant_rules(3), clarsimp)
  apply(drule_tac i="2" in has_vderiv_on_vec_nth)
  apply(unfold has_vderiv_on_def has_vector_derivative_def)
  apply(erule_tac x="r" in ballE, simp add: matrix_vector_mult_def)
   apply(rule_tac f'1="\<lambda>s. 0" in derivative_eq_intros(10))
  by(auto simp: closed_segment_eq_real_ivl has_derivative_within_subset)

lemma bouncing_ball_invariant: 
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
  using gravity_is_invariant apply(blast, force, force)
   apply(rule_tac C="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1 = 0" in dCut)
    apply(rule_tac I="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1 = 0" in dI)
  using bouncing_ball_invariant apply(blast, force, force)
   apply(rule dWeakening)
   apply(rule ffb_if_then_else)
  by(auto simp: bb_real_arith le_fun_def)


(**************************************************************************************************)

abbreviation "KK \<equiv> sq_mtx_chi K"

lemma picard_lindeloef_sq_mtx:
  fixes A::"('n::finite) sqrd_matrix"
  assumes "0 < ((real CARD('n))\<^sup>2 \<cdot> (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_lindeloef (\<lambda> t s. A *\<^sub>V s) {0..t} ?L 0"
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
  assumes "0 < ((real CARD('n))\<^sup>2 \<cdot> (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "local_flow (\<lambda>s. A *\<^sub>V s) {0..t} ((real CARD('n))\<^sup>2 \<cdot> (\<parallel>to_vec A\<parallel>\<^sub>m\<^sub>a\<^sub>x)) ((\<lambda>t s. exp (t *\<^sub>R A) *\<^sub>V s))"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_sq_mtx assms apply blast
  using exp_has_vderiv_on_linear[of 0] apply force
  by(auto simp: sq_mtx_one_vec )

lemma max_norm_KK: "\<parallel>to_vec KK\<parallel>\<^sub>m\<^sub>a\<^sub>x = 1"
proof-
  have "{to_vec KK $ i $ j |i j. s2p UNIV i \<and> s2p UNIV j} = {0, 1}"
    apply (simp_all add: axis_def, safe)
    by(rule_tac x="1" in exI, simp)+
  thus ?thesis
    by auto
qed

corollary flow_for_KK_DS:
  assumes "0 \<le> t" and "t < 1/9"
  shows "fb\<^sub>\<F> ([x\<acute>=\<lambda>s. KK *\<^sub>V s]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G ((exp (r *\<^sub>R KK)) *\<^sub>V x)) \<longrightarrow> ((exp (\<tau> *\<^sub>R KK)) *\<^sub>V x) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. KK *\<^sub>V s" _ "((real CARD(3))\<^sup>2 \<cdot> (\<parallel>to_vec KK\<parallel>\<^sub>m\<^sub>a\<^sub>x))" 
"(\<lambda>t x. (exp (t *\<^sub>R KK)) *\<^sub>V x)"])
    apply(rule local_flow_exp)
  using max_norm_KK assms by auto

lemma sq_mtx_vec_prod_eq: "m *\<^sub>V x = (\<chi> i. sum (\<lambda>j. ((m$$i)$j) * (x$j)) UNIV)"
  by(transfer, simp add: matrix_vector_mult_def)

lemma exp_KK_simps:
 "exp (\<tau> *\<^sub>R KK) $$ 0 $ 0 = 1" "exp (\<tau> *\<^sub>R KK) $$ 0 $ 1 = \<tau>" "exp (\<tau> *\<^sub>R KK) $$ 0 $ 2 = \<tau>^2/2"
 "exp (\<tau> *\<^sub>R KK) $$ 1 $ 0 = 0" "exp (\<tau> *\<^sub>R KK) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R KK) $$ 1 $ 2 = \<tau>"
 "exp (\<tau> *\<^sub>R KK) $$ 2 $ 0 = 0" "exp (\<tau> *\<^sub>R KK) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R KK) $$ 2 $ 2 = 1"
  sorry

lemma bouncing_ball_KK:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "{s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2} \<le> fb\<^sub>\<F> 
  (kstar (([x\<acute>=\<lambda>s. KK *\<^sub>V s]{0..t} & (\<lambda> s. s $ 0 \<ge> 0)) \<circ>\<^sub>K
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE \<eta> FI)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H}"
  apply(rule ffb_starI[of _ "{s. 0 \<le> s $ (0::3) \<and> 0 > s $ 2 \<and> 
  2 \<cdot> s $ 2 \<cdot> s $ 0 = 2 \<cdot> s $ 2 \<cdot> H + (s $ 1 \<cdot> s $ 1)}"])
  apply(clarsimp, simp only: ffb_kcomp)
    apply(subst flow_for_KK_DS)
  using assms apply(simp, simp, clarsimp)
  apply(rule ffb_if_then_elseD, clarsimp)
   apply(simp_all add: sq_mtx_vec_prod_eq)
  unfolding UNIV_3 apply(simp_all add: exp_KK_simps)
  subgoal for x using bb_real_arith(3)[of "x $ 2"]
    by (simp add: add.commute mult.commute)
  subgoal for x \<tau> using bb_real_arith(4)[where g="x $ 2" and v="x $ 1"]
    by(simp add: add.commute mult.commute)
  by (force simp: bb_real_arith)

end