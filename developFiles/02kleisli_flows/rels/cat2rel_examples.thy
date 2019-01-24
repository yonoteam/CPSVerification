theory cat2rel_examples
  imports cat2rel

begin

subsection{* Examples *}

text{* Here we do our first verification example: the single-evolution ball. We do it in two ways.
The first one provides (1) a finite type and (2) its corresponding problem-specific vector-field and
flow. The second approach uses an existing finite type and defines a more general vector-field which
is later instantiated to the problem at hand.*}

subsubsection{* Specific vector field *}

text{* We define a finite type of three elements. All the lemmas below proven about this type must
exist in order to do the verification example.*}

typedef three ="{m::nat. m < 3}"
  apply(rule_tac x="0" in exI)
  by simp

lemma CARD_of_three:"CARD(three) = 3"
  using type_definition.card type_definition_three by fastforce

instance three::finite
  apply(standard, subst bij_betw_finite[of Rep_three UNIV "{m::nat. m < 3}"])
   apply(rule bij_betwI')
     apply (simp add: Rep_three_inject)
  using Rep_three apply blast
   apply (metis Abs_three_inverse UNIV_I)
  by simp

lemma three_univD:"(UNIV::three set) = {Abs_three 0, Abs_three 1, Abs_three 2}"
proof-
  have "(UNIV::three set) = Abs_three ` {m::nat. m < 3}"
    apply auto by (metis Rep_three Rep_three_inverse image_iff)
  also have "{m::nat. m < 3} = {0, 1, 2}" by auto
  ultimately show ?thesis by auto
qed

lemma three_exhaust:"\<forall> x::three. x = Abs_three 0 \<or> x = Abs_three 1 \<or> x = Abs_three 2"
  using three_univD by auto

text{* Next we use our recently created type to generate a 3-dimensional vector space. We then define 
the vector field and the flow for the single-evolution ball on this vector space. Then we follow the 
standard procedure to prove that they are in fact a Lipschitz vector-field and a its flow. *}

abbreviation "free_fall_kinematics (s::real^three) \<equiv> (\<chi> i. if i=(Abs_three 0) then s $ (Abs_three 1) else 
if i=(Abs_three 1) then s $ (Abs_three 2) else 0)"

abbreviation "free_fall_flow t s \<equiv> 
(\<chi> i. if i=(Abs_three 0) then s $ (Abs_three 2) \<cdot> t ^ 2/2 + s $ (Abs_three 1) \<cdot> t + s $ (Abs_three 0)
else if i=(Abs_three 1) then s $ (Abs_three 2) \<cdot> t + s $ (Abs_three 1) else s $ (Abs_three 2))"

lemma bounded_linear_free_fall_kinematics:"bounded_linear free_fall_kinematics"
  apply unfold_locales
    apply(simp_all add: plus_vec_def scaleR_vec_def ext norm_vec_def L2_set_def)
  apply(rule_tac x="1" in exI, clarsimp)
  apply(subst three_univD, subst three_univD)
  by(auto simp: Abs_three_inject)

lemma free_fall_kinematics_continuous_on: "continuous_on X free_fall_kinematics"
  using bounded_linear_free_fall_kinematics linear_continuous_on by blast

lemma free_fall_kinematics_is_picard_ivp:"0 \<le> t \<Longrightarrow> t < 1 \<Longrightarrow> 
picard_ivp (\<lambda> t s. free_fall_kinematics s) {0..t} UNIV 1 0"
  unfolding picard_ivp_def picard_ivp_axioms_def ubc_definitions
  apply(simp_all add: nonempty_set_def lipschitz_on_def, safe)
     apply(rule continuous_on_compose2[of UNIV _ "{0..t} \<times> UNIV" snd])
  apply(simp_all add: free_fall_kinematics_continuous_on continuous_on_snd)
   apply(simp add: dist_vec_def L2_set_def dist_real_def)
   apply(subst three_univD, subst three_univD)
  by(simp add: Abs_three_inject)

lemma free_fall_flow_solves_free_fall_kinematics:
  "((\<lambda> \<tau>. free_fall_flow \<tau> s) solves_ode (\<lambda>t s. free_fall_kinematics s)) {0..t} UNIV"
  apply (rule solves_vec_lambda)
  apply(simp add: solves_ode_def)
  unfolding has_vderiv_on_def has_vector_derivative_def apply(auto simp: Abs_three_inject)
  using poly_derivatives(3, 4) unfolding has_vderiv_on_def has_vector_derivative_def by auto

lemma free_fall_flow_is_local_flow:
"0 \<le> t \<Longrightarrow> t < 1 \<Longrightarrow> local_flow (\<lambda> s. free_fall_kinematics s) UNIV {0..t} 1 (\<lambda> t x. free_fall_flow t x)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using free_fall_kinematics_is_picard_ivp apply simp
  subgoal for x _ \<tau>
    apply(rule picard_ivp.unique_solution [of "\<lambda> t s. free_fall_kinematics s" "{0..t}" 
          UNIV 1 0 "(\<lambda> t. free_fall_flow t (x 0))" "x 0"])
    using free_fall_kinematics_is_picard_ivp apply simp
         apply(rule free_fall_flow_solves_free_fall_kinematics)
        apply(simp_all add: vec_eq_iff Abs_three_inject)
    using three_univD by fastforce
  done

text{* We end the first example by computing the wlp of the kinematics for the single-evolution
ball and then using it to verify "its safety".*}

corollary free_fall_flow_DS:
  assumes "0 \<le> t" and "t < 1"
  shows " wp {[x\<acute>=\<lambda>s. free_fall_kinematics s]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (free_fall_flow r x)) \<longrightarrow> Q (free_fall_flow \<tau> x)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda>s. free_fall_kinematics s" _ _ 1 "(\<lambda> t x. free_fall_flow t x)"])
  using free_fall_flow_is_local_flow and assms by (blast, simp)

lemma single_evolution_ball:
  assumes "0 \<le> t" and "t < 1" 
  shows 
 "\<lceil>\<lambda>s. (0::real) \<le> s $ (Abs_three 0) \<and> s $ (Abs_three 0) = H \<and> s $ (Abs_three 1) = 0 \<and> 0 > s $ (Abs_three 2)\<rceil> 
  \<subseteq> wp ({[x\<acute>=\<lambda>s. free_fall_kinematics s]{0..t} UNIV @ 0 & (\<lambda> s. s $ (Abs_three 0) \<ge> 0)})
         \<lceil>\<lambda>s. 0 \<le> s $ (Abs_three 0) \<and> s $ (Abs_three 0) \<le> H\<rceil>"
  apply(subst free_fall_flow_DS)
  by(simp_all add: assms mult_nonneg_nonpos2)

subsubsection{* General vector field *}

text{* It turns out that there is already a 3-element type:*}
term "x::3"
lemma "CARD(three) = CARD(3)"
  unfolding CARD_of_three by simp

text{* In fact, for each natural number $n$ 
there is already a corresponding $n$-element type in Isabelle. However, there are still some lemmas
that one needs to prove in order to use it in verification in $n$-dimensional vector spaces. *}

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

text{* Next, we prove that every linear system of differential equations (i.e. it can be rewritten 
as $x' = A\cdot x$ ) satisfies the conditions of the Picard-Lindeloef theorem: *}

lemma matrix_lipschitz_constant:
  fixes A::"real^('n::finite)^'n"
  shows "dist (A *v x) (A *v y) \<le> (real CARD('n))\<^sup>2 \<cdot> maxAbs A \<cdot> dist x y"
  unfolding dist_norm vector_norm_distr_minus proof(subst norm_matrix_sgn)
  have "norm\<^sub>S A \<le> maxAbs A \<cdot> (real CARD('n) \<cdot> real CARD('n))"
    by (metis (no_types) Groups.mult_ac(2) norms_le_dims_maxAbs)
  then have "norm\<^sub>S A \<cdot> norm (x - y) \<le> (real (card (UNIV::'n set)))\<^sup>2 \<cdot> maxAbs A \<cdot> norm (x - y)"
    by (simp add: cross3_simps(11) mult_left_mono semiring_normalization_rules(29))
  also have "norm (A *v sgn (x - y)) \<cdot> norm (x - y) \<le> norm\<^sub>S A \<cdot> norm (x - y)"
    by (simp add: norm_sgn_le_norms cross3_simps(11) mult_left_mono) 
  ultimately show "norm (A *v sgn (x - y)) \<cdot> norm (x - y) \<le> (real CARD('n))\<^sup>2 \<cdot> maxAbs A \<cdot> norm (x - y)"
    using order_trans_rules(23) by blast
qed

lemma picard_ivp_linear_system:
  fixes A::"real^('n::finite)^'n" 
  assumes "0 < ((real CARD('n))\<^sup>2 \<cdot> (maxAbs A))" (is "0 < ?L") 
  assumes "0 \<le> t" and "t < 1/?L"
  shows "picard_ivp (\<lambda> t s. A *v s) {0..t} UNIV ?L 0"
  apply unfold_locales
  subgoal by(simp, metis continuous_on_compose2 continuous_on_cong continuous_on_id 
        continuous_on_snd matrix_vector_mult_linear_continuous_on top_greatest) 
  subgoal using matrix_lipschitz_constant maxAbs_ge_0 zero_compare_simps(4,12) 
    unfolding lipschitz_on_def by blast
  apply(simp_all add: assms)
  subgoal for r s apply(subgoal_tac "\<bar>r - s\<bar> < 1/((real CARD('n))\<^sup>2 \<cdot> maxAbs A)")
     apply(subst (asm) pos_less_divide_eq[of ?L "\<bar>r - s\<bar>" 1])
    using assms by auto
  done

text{* We can rewrite the original free-fall kinematics as a linear operator applied to a 3-dimensional
vector. For that we take advantage of the following fact: *}

lemma "axis (1::3) (1::real) = (\<chi> j. if j= 0 then 0 else if j = 1 then 1 else 0)"
  unfolding axis_def by(rule Cart_lambda_cong, simp)

abbreviation "K \<equiv> (\<chi> i. if i= (0::3) then axis (1::3) (1::real) else if i= 1 then axis 2 1 else 0)"

abbreviation "flow_for_K t s \<equiv> (\<chi> i. if i= (0::3) then s $ 2 \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0
else if i=1 then s $ 2 \<cdot> t + s $ 1 else s $ 2)"

text{* With these 2 definitions and the proof that linear systems of ODEs are Picard-Lindeloef, we can 
show that they form a pair of vector-field and its flow. *}

lemma entries_K:"entries K = {0, 1}"
  apply (simp_all add: axis_def, safe)
  by(rule_tac x="1" in exI, simp)+

lemma "0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> picard_ivp (\<lambda> t s. K *v s) {0..t} UNIV ((real CARD(3))\<^sup>2 \<cdot> maxAbs K) 0"
  apply(rule picard_ivp_linear_system)
  unfolding entries_K by auto

lemma flow_for_K_solves_K: "((\<lambda> \<tau>. flow_for_K \<tau> s) solves_ode (\<lambda>t s.  K *v s)) {0..t} UNIV"
  apply (rule solves_vec_lambda)
  apply(simp add: solves_ode_def)
  using poly_derivatives(1, 3, 4) 
  by(auto simp: matrix_vector_mult_def)

lemma flow_for_K_is_local_flow: "0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> 
  local_flow (\<lambda> s. K *v s) UNIV {0..t} ((real CARD(3))\<^sup>2 \<cdot> maxAbs K) (\<lambda> t x. flow_for_K t x)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  subgoal apply(rule picard_ivp_linear_system) unfolding entries_K by auto
  subgoal for x _ \<tau> apply(rule picard_ivp.unique_solution [of "(\<lambda>t. ( *v) K)" "{0..t}" UNIV 
          "((real CARD(3))\<^sup>2 \<cdot> maxAbs K)" 0])
    subgoal apply(rule picard_ivp_linear_system) unfolding entries_K by auto 
         apply(rule flow_for_K_solves_K)
        apply(simp_all add: vec_eq_iff)
    using UNIV_3 by fastforce+
  done

text{* Finally, we compute the wlp of this example and use it to verify the single-evolution ball again.*}

corollary flow_for_K_DS:
  assumes "0 \<le> t" and "t < 1/9"
  shows " wp {[x\<acute>=\<lambda>s. K *v s]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (flow_for_K r x)) \<longrightarrow> Q (flow_for_K \<tau> x)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda>s. K *v s" _ _ "((real CARD(3))\<^sup>2 \<cdot> maxAbs K)" "(\<lambda> t x. flow_for_K t x)"])
  using flow_for_K_is_local_flow and assms apply blast by simp 

lemma single_evolution_ball_K:
  assumes "0 \<le> t" and "t < 1/9" 
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> 
  \<subseteq> wp ({[x\<acute>=\<lambda>s. K *v s]{0..t} UNIV @ 0 & (\<lambda> s. s $ 0 \<ge> 0)})
        \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H\<rceil>"
  apply(subst flow_for_K_DS)
  using assms by(simp_all add: mult_nonneg_nonpos2)

subsubsection{* Bouncing Ball with solution *}
text{* Armed now with two vector fields for free-fall kinematics and their respective flows, proving
the safety of a ``bouncing ball'' is merely an exercise of real arithmetic: *}

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
proof-
  from pos have "g \<cdot> \<tau>\<^sup>2  + 2 \<cdot> v \<cdot> \<tau> + 2 \<cdot> x = 0" by auto
  then have "g\<^sup>2  \<cdot> \<tau>\<^sup>2  + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + v\<^sup>2 + 2 \<cdot> g \<cdot> H = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  from this have "(g \<cdot> \<tau> + v)\<^sup>2 + 2 \<cdot> g \<cdot> H = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  hence "2 \<cdot> g \<cdot> H + (- ((g \<cdot> \<tau>) + v))\<^sup>2 = 0"
    by (metis Groups.add_ac(2) power2_minus)
  thus ?thesis
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
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> \<subseteq> wp 
  (({[x\<acute>=\<lambda>s. K *v s]{0..t} UNIV @ 0 & (\<lambda> s. s $ 0 \<ge> 0)};
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H\<rceil>"
  apply(rule rel_ad_mka_starI [of _ "\<lceil>\<lambda>s. 0 \<le> s $ (0::3) \<and> 0 > s $ 2 \<and> 
  2 \<cdot> s $ 2 \<cdot> s $ 0 = 2 \<cdot> s $ 2 \<cdot> H + (s $ 1 \<cdot> s $ 1)\<rceil>"])
    apply(simp, simp only: rel_antidomain_kleene_algebra.fbox_seq)
   apply(subst p2r_r2p_wp_sym[of "(IF (\<lambda>s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE Id FI)"])
   apply(subst flow_for_K_DS) using assms apply(simp, simp) apply(subst wp_trafo)
  by(auto simp: p2r_def rel_antidomain_kleene_algebra.cond_def 
      rel_antidomain_kleene_algebra.ads_d_def rel_ad_def closed_segment_eq_real_ivl bb_real_arith)

subsubsection{* Bouncing Ball with invariants *}

lemma gravity_is_invariant:"(x solves_ode (\<lambda>t. ( *v) K)) {0..t} UNIV \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> r \<in> {0..\<tau>} \<Longrightarrow> 
((\<lambda>\<tau>. x \<tau> $ 2) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R 0)) (at r within {0..\<tau>})"
  apply(drule_tac i="2" in solves_vec_nth)
  apply(unfold solves_ode_def has_vderiv_on_def has_vector_derivative_def, clarify)
  apply(erule_tac x="r" in ballE, simp add: matrix_vector_mult_def)
  by (simp_all add: has_derivative_within_subset)

lemma bouncing_ball_invariant:"(x solves_ode (\<lambda>t. ( *v) K)) {0..t} UNIV \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
r \<in> {0..\<tau>} \<Longrightarrow> ((\<lambda>\<tau>. 2 \<cdot> x \<tau> $ 2 \<cdot> x \<tau> $ 0 - 2 \<cdot> x \<tau> $ 2 \<cdot> H - x \<tau> $ 1 \<cdot> x \<tau> $ 1) has_derivative 
(\<lambda>\<tau>. \<tau> *\<^sub>R 0)) (at r within {0..\<tau>})"
  apply(frule_tac i="2" in solves_vec_nth,frule_tac i="1" in solves_vec_nth,drule_tac i="0" in solves_vec_nth)
  apply(unfold solves_ode_def has_vderiv_on_def has_vector_derivative_def, clarify)
  apply(erule_tac x="r" in ballE, simp_all add: matrix_vector_mult_def)+
  apply(rule_tac f'1="\<lambda>t. 2 \<cdot> x r $ 2 \<cdot> (t \<cdot> x r $ 1)" 
      and g'1="\<lambda>t. 2 \<cdot> (t \<cdot> (x r $ 1 \<cdot> x r $ 2))" in derivative_eq_intros(11))
    apply(rule_tac f'1="\<lambda>t. 2 \<cdot> x r $ 2 \<cdot> (t \<cdot> x r $ 1)" and g'1="\<lambda>t. 0" in derivative_eq_intros(11))
      apply(rule_tac f'1="\<lambda>t. 0" and g'1="(\<lambda>xa. xa \<cdot> x r $ 1)" in derivative_eq_intros(12))
        apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(6), simp_all add: has_derivative_within_subset)
  apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(7))
    apply(rule_tac g'1="\<lambda>t. 0" in derivative_eq_intros(6), simp_all add: has_derivative_within_subset)
  by(rule_tac f'1="(\<lambda>xa. xa \<cdot> x r $ 2)" and g'1="(\<lambda>xa. xa \<cdot> x r $ 2)" in derivative_eq_intros(12), 
      simp_all add: has_derivative_within_subset)

lemma bouncing_ball_invariants:
  assumes "0 \<le> t" and "t < 1/9" 
  shows"\<lceil>\<lambda>s. (0::real) \<le> s $ (0::3) \<and> s $ 0 = H \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> \<subseteq> wp 
  (({[x\<acute>=\<lambda>s. K *v s]{0..t} UNIV @ 0 & (\<lambda> s. s $ 0 \<ge> 0)};
  (IF (\<lambda> s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> H\<rceil>"
  apply(rule_tac I="\<lceil>\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and> 2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> H + (s$1 \<cdot> s$1)\<rceil>" in rel_ad_mka_starI)
    apply(simp, simp only: rel_antidomain_kleene_algebra.fbox_seq)
   apply(subst p2r_r2p_wp_sym[of "(IF (\<lambda>s. s $ 0 = 0) THEN ([1 ::== (\<lambda>s. - s $ 1)]) ELSE Id FI)"])
  using assms(1) apply(rule dCut_interval[of _ _ _ _ _ _ "\<lambda> s. s $ 2 < 0"])
   apply(rule_tac \<theta>="\<lambda>s. s $ 2" and \<nu>="\<lambda>s. 0" in dInvariant_below_0)
  using gravity_is_invariant apply force
       apply(simp, simp, simp, simp add: \<open>0 \<le> t\<close>)
   apply(rule_tac C="\<lambda> s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1 = 0" in dCut_interval, simp add: \<open>0 \<le> t\<close>)
   apply(rule_tac \<theta>="\<lambda>s. 2 \<cdot> s$2 \<cdot> s$0 - 2 \<cdot> s$2 \<cdot> H - s$1 \<cdot> s$1" and \<nu>="\<lambda> s. 0" in dInvariant_eq_0)
  using bouncing_ball_invariant apply force
  apply(simp, simp, simp, simp add: \<open>0 \<le> t\<close>)
  apply(rule dWeakening, subst p2r_r2p_wp)
  by(auto simp: bb_real_arith p2r_def rel_antidomain_kleene_algebra.cond_def
      rel_antidomain_kleene_algebra.fbox_def rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)

subsubsection{* Circular motion with invariants *}

lemma two_eq_zero: "(2::2) = 0" by simp

lemma [simp]:"i \<noteq> (0::2) \<longrightarrow> i = 1" using exhaust_2 by fastforce

lemma UNIV_2:"(UNIV::2 set) = {0, 1}"
  apply safe using exhaust_2 two_eq_zero by auto

lemma sum_axis_UNIV_2[simp]:"(\<Sum>j\<in>(UNIV::2 set). axis i r $ j \<cdot> f j) = r \<cdot> (f::2 \<Rightarrow> real) i"
  unfolding axis_def UNIV_2 by simp

abbreviation "Circ \<equiv> (\<chi> i. if i= (0::2) then axis (1::2) (- 1::real) else axis 0 1)"

abbreviation "flow_for_Circ t s \<equiv> (\<chi> i. if i= (0::2) then 
s$0 \<cdot> cos t - s$1 \<cdot> sin t else s$0 \<cdot> sin t + s$1 \<cdot> cos t)"

lemma entries_Circ:"entries Circ = {0, - 1, 1}"
  apply (simp_all add: axis_def, safe)
  subgoal by(rule_tac x="0" in exI, simp)+
  subgoal by(rule_tac x="0" in exI, simp)+
  by(rule_tac x="1" in exI, simp)+

lemma "0 \<le> t \<Longrightarrow> t < 1/4 \<Longrightarrow> picard_ivp (\<lambda> t s. Circ *v s) {0..t} UNIV ((real CARD(2))\<^sup>2 \<cdot> maxAbs Circ) 0"
  apply(rule picard_ivp_linear_system)
  unfolding entries_Circ by auto

lemma flow_for_Circ_solves_Circ: "((\<lambda> \<tau>. flow_for_Circ \<tau> s) solves_ode (\<lambda>t s.  Circ *v s)) {0..t} UNIV"
  apply (rule solves_vec_lambda, clarsimp)
  subgoal for i apply(cases "i=0")
     apply(simp_all add: matrix_vector_mult_def)
    unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def apply auto
    subgoal for x
      apply(rule_tac f'1="\<lambda>t. - s$0 \<cdot> (t \<cdot> sin x)" and g'1="\<lambda>t. s$1 \<cdot> (t \<cdot> cos x)"in derivative_eq_intros(11))
      apply(rule derivative_eq_intros(6)[of cos "(\<lambda>xa. - (xa \<cdot> sin x))"])
       apply(rule_tac Db1="1" in derivative_eq_intros(58))
          apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
       apply(rule derivative_eq_intros(6)[of sin "(\<lambda>xa. (xa \<cdot> cos x))"])
        apply(rule_tac Db1="1" in derivative_eq_intros(55))
         apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
      by (simp add: Groups.mult_ac(3) Rings.ring_distribs(4))
    subgoal for x
      apply(rule_tac f'1="\<lambda>t. s$0 \<cdot> (t \<cdot> cos x)" and g'1="\<lambda>t. - s$1 \<cdot> (t \<cdot> sin x)"in derivative_eq_intros(8))
      apply(rule derivative_eq_intros(6)[of sin "(\<lambda>xa. xa \<cdot> cos x)"])
       apply(rule_tac Db1="1" in derivative_eq_intros(55))
          apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
       apply(rule derivative_eq_intros(6)[of cos "(\<lambda>xa. - (xa \<cdot> sin x))"])
        apply(rule_tac Db1="1" in derivative_eq_intros(58))
         apply(rule ssubst[of "(\<cdot>) 1" id], force, simp, force, force)
      by (simp add: Groups.mult_ac(3) Rings.ring_distribs(4))
    done
  done

lemma flow_for_Circ_is_local_flow: "0 \<le> t \<Longrightarrow> t < 1/4 \<Longrightarrow> 
  local_flow (\<lambda> s. Circ *v s) UNIV {0..t} ((real CARD(2))\<^sup>2 \<cdot> maxAbs Circ) (\<lambda> t x. flow_for_Circ t x)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  subgoal apply(rule picard_ivp_linear_system) unfolding entries_Circ by auto
  subgoal for x _ \<tau> apply(rule picard_ivp.unique_solution [of "(\<lambda>t. ( *v) Circ)" "{0..t}" UNIV 
          "((real CARD(2))\<^sup>2 \<cdot> maxAbs Circ)" 0])
    subgoal apply(rule picard_ivp_linear_system) unfolding entries_Circ by auto
         apply(rule flow_for_Circ_solves_Circ)
        apply(simp_all add: vec_eq_iff)
    using UNIV_2 by fastforce+
  done

corollary flow_for_Circ_DS:
  assumes "0 \<le> t" and "t < 1/4"
  shows " wp {[x\<acute>=\<lambda>s. Circ *v s]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (flow_for_Circ r x)) \<longrightarrow> Q (flow_for_Circ \<tau> x)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda>s. Circ *v s" _ _ "((real CARD(2))\<^sup>2 \<cdot> maxAbs Circ)" "(\<lambda> t x. flow_for_Circ t x)"])
  using flow_for_Circ_is_local_flow and assms apply blast by simp

lemma semiring_factor_left:"a \<cdot> b + a \<cdot> c = a \<cdot> ((b::('a::semiring)) + c)"
  by(subst Groups.algebra_simps(18), simp)

lemma sin_cos_squared_add3:"(x::('a:: {banach,real_normed_field})) \<cdot> (sin t)\<^sup>2 + x \<cdot> (cos t)\<^sup>2 = x"
  by(subst semiring_factor_left, subst sin_cos_squared_add, simp)

lemma sin_cos_squared_add4:"(x::('a:: {banach,real_normed_field})) \<cdot> (cos t)\<^sup>2 + x \<cdot> (sin t)\<^sup>2 = x"
  by(subst semiring_factor_left, subst sin_cos_squared_add2, simp)

lemma [simp]:"((x::real) \<cdot> cos t - y \<cdot> sin t)\<^sup>2 + (x \<cdot> sin t + y \<cdot> cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x \<cdot> cos t - y \<cdot> sin t)\<^sup>2 = x\<^sup>2 \<cdot> (cos t)\<^sup>2 + y\<^sup>2 \<cdot> (sin t)\<^sup>2 - 2 \<cdot> (x \<cdot> cos t) \<cdot> (y \<cdot> sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x \<cdot> sin t + y \<cdot> cos t)\<^sup>2 = y\<^sup>2 \<cdot> (cos t)\<^sup>2 + x\<^sup>2 \<cdot> (sin t)\<^sup>2 + 2 \<cdot> (x \<cdot> cos t) \<cdot> (y \<cdot> sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x \<cdot> cos t - y \<cdot> sin t)\<^sup>2 + (x \<cdot> sin t + y \<cdot> cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"  
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq) 
qed

lemma circular_motion:
  assumes "0 \<le> t" and "t < 1/4" and "(R::real) > 0"
  shows"\<lceil>\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2\<rceil> \<subseteq> wp 
  {[x\<acute>=\<lambda>s. Circ *v s]{0..t} UNIV @ 0 & (\<lambda> s. s $ 0 \<ge> 0)}
  \<lceil>\<lambda>s. R\<^sup>2 = (s $ (0::2))\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  apply(subst flow_for_Circ_DS)
  using assms by simp_all
  

(* FOR FUTURE REFERENCE *)

thm bij_betwI  bij_betwI' bij_betw_finite
thm Rep_three  Rep_three_inject Rep_three_cases Rep_three_inverse
thm           Abs_three_inject Abs_three_cases Abs_three_inverse
thm vec_nth   vec_nth_inject vec_nth_cases vec_nth_inverse 
thm           vec_lambda_inject vec_lambda_cases vec_lambda_inverse
thm L2_set_def norm_vec_def component_le_norm_cart norm_bound_component_le_cart
thm matrix_vector_mult_def matrix_mult_dot matrix_mult_sum vector_componentwise basis_expansion
thm card_eq_sum sum_def real_scaleR_def Connected.bounded_has_Sup sum_norm_allsubsets_bound
thm dist_norm matrix_vector_mult_diff_distrib
value "card (UNIV :: nat set)"
term "the_inv"
term "the_inv_into"

(* PENDING: *)

(* Generalized theorems for each finite type: *)
lemma fun_1:"f (x::num1) = f 1"
  apply(subgoal_tac "\<forall> x::num1. f x = f 1")
  by(erule_tac x="x" in allE, simp_all)

lemma "(\<Sum>(j::num1)\<in>UNIV. axis i 1 $ j \<cdot> f j) = ((f i)::real)"
  unfolding axis_def apply simp
  using fun_1 by metis

declare [[show_sorts, show_types]]
term "x::4" term "x::5" term "x::10" term "x::1000" term "(x::0) = x :: 5"

(* Understand the following concept in Isabelle *)
term "frechet_derivative"

end