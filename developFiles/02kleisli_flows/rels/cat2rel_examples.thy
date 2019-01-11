theory cat2rel_examples
  imports cat2rel

begin

subsection{* Examples *}

text{* Here we do our first verification example: the single-hop bouncing ball. We do it in two ways.
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
the vector field and the flow for the single-hop ball on this vector space. Then we follow the 
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
  apply (rule componentwise_solves)
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

text{* We end the first example by computing the wlp of the kinematics for the single-hop bouncing
ball and then using it to verify "its safety".*}

corollary free_fall_flow_DS:
  assumes "0 \<le> t" and "t < 1"
  shows " wp {[x\<acute>=\<lambda>s. free_fall_kinematics s]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (free_fall_flow r x)) \<longrightarrow> Q (free_fall_flow \<tau> x)\<rceil>"
  apply(subst wp_g_orbit[of "\<lambda>s. free_fall_kinematics s" _ _ 1 "(\<lambda> t x. free_fall_flow t x)"])
  using free_fall_flow_is_local_flow and assms by (blast, simp)

lemma single_evolution_ball:
  assumes "0 \<le> t" and "t < 1" 
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ (Abs_three 0) \<and> s $ (Abs_three 0) = H \<and> s $ (Abs_three 1) = 0 \<and> 0 > s $ (Abs_three 2)\<rceil> 
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

lemma flow_for_K_solves_K:
  "((\<lambda> \<tau>. flow_for_K \<tau> s) solves_ode (\<lambda>t s.  K *v s)) {0..t} UNIV"
  apply (rule componentwise_solves)
  apply(simp add: solves_ode_def)
  using poly_derivatives(1, 3, 4) 
  by(auto simp: matrix_vector_mult_def)

lemma flow_for_K_is_local_flow:
"0 \<le> t \<Longrightarrow> t < 1/9 \<Longrightarrow> local_flow (\<lambda> s. K *v s) UNIV {0..t} ((real CARD(3))\<^sup>2 \<cdot> maxAbs K) (\<lambda> t x. flow_for_K t x)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  subgoal apply(rule picard_ivp_linear_system)
    unfolding entries_K by auto
  subgoal for x _ \<tau>
    apply(rule picard_ivp.unique_solution [of "(\<lambda>t. ( *v) K)" "{0..t}" UNIV "((real CARD(3))\<^sup>2 \<cdot> maxAbs K)" 0])
    subgoal apply(rule picard_ivp_linear_system) unfolding entries_K by auto 
         apply(rule flow_for_K_solves_K)
        apply(simp_all add: vec_eq_iff)
    using UNIV_3 by fastforce+
  done

text{* Finally, we compute the wlp of these example and use it to verify the single-hop bouncing ball
again.*}

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

term "{[x\<acute>= (f::real^three \<Rightarrow> real^three)]T S @ t0 & G}"
term "{(s, (\<chi> i. ((($) s)(x := expr)) i))| s. True}" (* assignment *)

lemma bouncing_ball:
  fixes  x v g ::three
  (* assumes "x \<noteq> v" and "v \<noteq> g" and "x \<noteq> g" *)
  (* assumes "x = Abs_three 0" and "v = Abs_three 1" and "g = Abs_three 2" *)
  shows "\<lceil>\<lambda>s. (0::real) \<le> s $ x \<and> s $ x = H \<and> s $ v = 0 \<and> 0 < s $ g\<rceil> \<subseteq> wp 
  (({[x\<acute>=\<lambda>s. (\<chi> i. if i=x then s $ v else 
                (if i=v then - s $ g else 0))]{0..t} UNIV @ 0 & (\<lambda> s. s $ x \<ge> 0)};
  (IF (\<lambda> s. s $ x = 0) 
   THEN ({(s, (\<chi> i. ((($) s)(v := (- s $ v))) i))| s. True}) 
   ELSE ({(s, (\<chi> i. ((($) s)(v := s $ v)) i))| s. True}) FI)
  )\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ x \<and> s $ x \<le> H\<rceil>"
  apply simp
  oops

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