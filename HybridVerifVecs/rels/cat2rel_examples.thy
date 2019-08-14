theory cat2rel_examples
  imports "../hs_prelims_matrices" cat2rel

begin

subsection\<open> Examples \<close>

text\<open> Preliminary preparation for the examples.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")

\<comment> \<open>Finite set of program variables.\<close>

typedef program_vars = "{''x'',''y''}"
  morphisms to_str to_var
  apply(rule_tac x="''x''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_program_vars: "CARD(program_vars) = 2"
  using type_definition.card type_definition_program_vars by fastforce

instance program_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV "{''x'',''y''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma program_vars_univ_eq: "(UNIV::program_vars set) = {\<restriction>\<^sub>V''x'', \<restriction>\<^sub>V''y''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma program_vars_exhaust: "x = \<restriction>\<^sub>V''x'' \<or> x = \<restriction>\<^sub>V''y''"
  using program_vars_univ_eq by auto

\<comment> \<open>Alternative to the finite set of program variables.\<close>

lemma "CARD(2) = CARD(program_vars)"
  unfolding number_of_program_vars by simp

lemma [simp]: "i \<noteq> (0::2) \<longrightarrow> i = 1" 
  using exhaust_2 by fastforce

lemma two_eq_zero: "(2::2) = 0" 
  by simp

lemma UNIV_2: "(UNIV::2 set) = {0, 1}"
  apply safe using exhaust_2 two_eq_zero by auto

lemma UNIV_3: "(UNIV::3 set) = {0, 1, 2}"
  apply safe using exhaust_3 three_eq_zero by auto

lemma sum_axis_UNIV_3[simp]: "(\<Sum>j\<in>(UNIV::3 set). axis i 1 $ j \<cdot> f j) = (f::3 \<Rightarrow> real) i"
  unfolding axis_def UNIV_3 apply simp
  using exhaust_3 by force


subsubsection\<open>Circular Motion\<close>

\<comment> \<open>Verified with differential invariants. \<close>

abbreviation circular_motion_kinematics :: "real^program_vars \<Rightarrow> real^program_vars" 
  where "circular_motion_kinematics s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V''x'') then s$(\<restriction>\<^sub>V''y'') else -s$(\<restriction>\<^sub>V''x''))"

notation circular_motion_kinematics ("C")

lemma circular_motion_invariant: 
  "diff_invariant (\<lambda>s. (r::real)\<^sup>2 = (s$(\<restriction>\<^sub>V''x''))\<^sup>2 + (s$(\<restriction>\<^sub>V''y''))\<^sup>2) C UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth, drule_tac i="\<restriction>\<^sub>V''y''" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives simp: to_var_inject)

lemma circular_motion_invariants:
  "\<lceil>\<lambda>s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''y'')\<^sup>2\<rceil> \<le> wp (x\<acute>= C & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''y'')\<^sup>2\<rceil>"
  unfolding wp_diff_inv using circular_motion_invariant by auto

\<comment> \<open>Verified with the flow. \<close>

abbreviation "circular_motion_flow t s \<equiv> 
  (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s$(\<restriction>\<^sub>V''x'') \<cdot> cos t + s$(\<restriction>\<^sub>V''y'') \<cdot> sin t
  else - s$(\<restriction>\<^sub>V''x'') \<cdot> sin t + s$(\<restriction>\<^sub>V''y'') \<cdot> cos t)"

notation circular_motion_flow ("\<phi>\<^sub>C")

lemma picard_lindeloef_circ_motion: "picard_lindeloef (\<lambda>t. C) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject power2_commute)

lemma local_flow_circ_motion: "local_flow C UNIV UNIV \<phi>\<^sub>C"
  unfolding local_flow_def local_flow_axioms_def apply safe
  apply(rule picard_lindeloef_circ_motion, simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V''x''", simp)
    apply(force intro!: poly_derivatives derivative_intros simp: to_var_inject)
  apply(force intro!: poly_derivatives derivative_intros simp: to_var_inject)
  using program_vars_exhaust by force

lemma circular_motion:
  "\<lceil>\<lambda>s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''y'')\<^sup>2\<rceil> \<le> wp (x\<acute>= C & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''y'')\<^sup>2\<rceil>"
  by (subst local_flow.wp_g_orbit[OF local_flow_circ_motion]) (auto simp: to_var_inject)

no_notation circular_motion_kinematics ("C")

no_notation circular_motion_flow ("\<phi>\<^sub>C")


\<comment> \<open>Verified as a linear system (using uniqueness). \<close>

abbreviation circular_motion_sq_mtx :: "2 sq_mtx" 
  where "circular_motion_sq_mtx \<equiv> sq_mtx_chi (\<chi> i. if i=0 then - \<e> 1 else \<e> 0)"

abbreviation circular_motion_mtx_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" 
  where "circular_motion_mtx_flow t s \<equiv> 
  (\<chi> i. if i=(0::2) then s$0 \<cdot> cos t - s$1 \<cdot> sin t else s$0 \<cdot> sin t + s$1 \<cdot> cos t)"

notation circular_motion_sq_mtx ("C")

notation circular_motion_mtx_flow ("\<phi>\<^sub>C")

lemma circular_motion_mtx_exp_eq: "exp (t *\<^sub>R C) *\<^sub>V s = \<phi>\<^sub>C t s"
  apply(rule local_flow.eq_solution[OF local_flow_exp, symmetric])
    apply(rule ivp_solsI, rule has_vderiv_on_vec_lambda, clarsimp)
  unfolding sq_mtx_vec_prod_def matrix_vector_mult_def apply simp
      apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by (force simp: vec_eq_iff, auto)

lemma circular_motion_sq_mtx:
  "\<lceil>\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2\<rceil> \<le> wp (x\<acute>= ((*\<^sub>V) C) & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2\<rceil>"
  unfolding local_flow.wp_g_orbit[OF local_flow_exp] circular_motion_mtx_exp_eq by auto

no_notation circular_motion_sq_mtx ("C")

no_notation circular_motion_mtx_flow ("\<phi>\<^sub>C")


subsubsection\<open> Bouncing Ball \<close>

\<comment> \<open>Verified with differential invariants. \<close>

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

abbreviation "constant_acceleration_kinematics g s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V''x'') then s$(\<restriction>\<^sub>V''y'') else g)"

notation constant_acceleration_kinematics ("K")

lemma energy_conservation_invariant: 
  fixes g h :: real
  defines dinv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V''x'') - 2 \<cdot> g \<cdot> h - (s$(\<restriction>\<^sub>V''y'') \<cdot> s$(\<restriction>\<^sub>V''y'')) = 0)"
  shows "diff_invariant I (K g) UNIV UNIV 0 G"
  unfolding dinv apply(rule diff_invariant_rules, simp, simp, clarify)
  apply(frule_tac i="\<restriction>\<^sub>V''y''" in has_vderiv_on_vec_nth)
  apply(drule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives simp: to_var_inject)

lemma bouncing_ball_invariants:
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines diff_inv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V''x'') - 2 \<cdot> g \<cdot> h - (s$(\<restriction>\<^sub>V''y'') \<cdot> s$(\<restriction>\<^sub>V''y'')) = 0)"
  shows "\<lceil>\<lambda>s. s$(\<restriction>\<^sub>V''x'') = h \<and> s$(\<restriction>\<^sub>V''y'') = 0\<rceil> \<le> 
  wp (((x\<acute>=K g & (\<lambda> s. s$(\<restriction>\<^sub>V''x'') \<ge> 0));
  (IF (\<lambda> s. s$(\<restriction>\<^sub>V''x'') = 0) THEN ((\<restriction>\<^sub>V''y'') ::= (\<lambda>s. - s$(\<restriction>\<^sub>V''y''))) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and> s$(\<restriction>\<^sub>V''x'') \<le> h\<rceil>"
  apply(rule_tac I="\<lceil>\<lambda>s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and> I s\<rceil>" in rel_ad_mka_starI)
  using \<open>h \<ge> 0\<close> apply(simp add: diff_inv, simp only: rel_antidomain_kleene_algebra.fbox_seq)
   apply(subst p2r_r2p_wp[symmetric, of "(IF _ THEN _ ELSE Id FI)"])
   apply(rule order.trans[where b="wp (x\<acute>=K g & (\<lambda>s. s$(\<restriction>\<^sub>V''x'')\<ge>0)) \<lceil>\<lambda>s. 0\<le>s$(\<restriction>\<^sub>V''x'') \<and> I s\<rceil>"])
    apply(simp only: wp_g_evolution_guard)
    apply(rule order.trans[where b="\<lceil>I\<rceil>"], simp)
    apply(subst wp_diff_inv, unfold diff_inv)
  using energy_conservation_invariant apply force
   apply(subst wp_trafo, rule rel_antidomain_kleene_algebra.fbox_iso) 
  using assms unfolding rel_antidomain_kleene_algebra.cond_def image_le_pred
    rel_antidomain_kleene_algebra.ads_d_def by(auto simp: p2r_def rel_ad_def bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma picard_lindeloef_cnst_acc:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. K g) UNIV UNIV 0"
  apply(unfold_locales)
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject)

abbreviation "constant_acceleration_kinematics_flow g t s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then g \<cdot> t ^ 2/2 + s $ (\<restriction>\<^sub>V ''y'') \<cdot> t + s $ (\<restriction>\<^sub>V ''x'') 
        else g \<cdot> t + s $ (\<restriction>\<^sub>V ''y''))"

notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

lemma local_flow_cnst_acc: "local_flow (K g) UNIV UNIV (\<phi>\<^sub>K g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V ''x''")
  using program_vars_exhaust by(auto intro!: poly_derivatives simp: to_var_inject vec_eq_iff)

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
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines loop_inv: "I \<equiv> (\<lambda>s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and>  2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V''x'') = 
    2 \<cdot> g \<cdot> h + (s$(\<restriction>\<^sub>V''y'') \<cdot> s$(\<restriction>\<^sub>V''y'')))"
  shows "\<lceil>\<lambda>s. s$(\<restriction>\<^sub>V''x'') = h \<and> s$(\<restriction>\<^sub>V''y'') = 0\<rceil> \<le> 
  wp (((x\<acute>=K g & (\<lambda> s. s$(\<restriction>\<^sub>V''x'') \<ge> 0));
  (IF (\<lambda> s. s$(\<restriction>\<^sub>V''x'') = 0) THEN ((\<restriction>\<^sub>V''y'') ::= (\<lambda>s. - s$(\<restriction>\<^sub>V''y''))) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and> s$(\<restriction>\<^sub>V''x'') \<le> h\<rceil>"
 apply(rule_tac I="\<lceil>I\<rceil>" in rel_ad_mka_starI)
  using \<open>h \<ge> 0\<close> apply(simp add: loop_inv, simp only: rel_antidomain_kleene_algebra.fbox_seq)
   apply(subst p2r_r2p_wp[symmetric, of "(IF _ THEN _ ELSE Id FI)"])
   apply(subst local_flow.wp_g_orbit[OF local_flow_cnst_acc])
   apply(subst wp_trafo, simp add: rel_antidomain_kleene_algebra.cond_def p2r_def)
  apply(simp add: rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)
  unfolding loop_inv using \<open>g < 0\<close> \<open>h \<ge> 0\<close> by (auto simp: to_var_inject bb_real_arith)

no_notation constant_acceleration_kinematics ("K")

no_notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

no_notation to_var ("\<restriction>\<^sub>V")

\<comment> \<open>Verified as a linear system (computing exponential). \<close>

abbreviation constant_acceleration_kinematics_sq_mtx :: "3 sq_mtx" 
  where "constant_acceleration_kinematics_sq_mtx \<equiv> 
    sq_mtx_chi (\<chi> i::3. if i=0 then \<e> 1 else if i=1 then \<e> 2 else 0)"

notation constant_acceleration_kinematics_sq_mtx ("K")

lemma const_acc_mtx_pow2: "K\<^sup>2 = sq_mtx_chi (\<chi> i. if i=0 then \<e> 2 else 0)"
  unfolding monoid_mult_class.power2_eq_square times_sq_mtx_def
  by (simp add: sq_mtx_chi_inject vec_eq_iff matrix_matrix_mult_def)

lemma const_acc_mtx_powN: "n > 2 \<Longrightarrow> (\<tau> *\<^sub>R K)^n = 0"
  apply(induct n, simp, case_tac "n \<le> 2")
   apply(simp only: le_less_Suc_eq power_class.power.simps(2), simp)
  by (auto simp: const_acc_mtx_pow2 sq_mtx_chi_inject vec_eq_iff 
      times_sq_mtx_def zero_sq_mtx_def matrix_matrix_mult_def)

lemma exp_cnst_acc_sq_mtx: "exp (\<tau> *\<^sub>R K) = ((\<tau> *\<^sub>R K)\<^sup>2/\<^sub>R 2) + (\<tau> *\<^sub>R K) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using const_acc_mtx_powN by (simp_all add: numeral_2_eq_2)

lemma exp_cnst_acc_sq_mtx_simps:
  "exp (\<tau> *\<^sub>R K) $$ 0 $ 0 = 1" "exp (\<tau> *\<^sub>R K) $$ 0 $ 1 = \<tau>" "exp (\<tau> *\<^sub>R K) $$ 0 $ 2 = \<tau>^2/2"
  "exp (\<tau> *\<^sub>R K) $$ 1 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R K) $$ 1 $ 2 = \<tau>"
  "exp (\<tau> *\<^sub>R K) $$ 2 $ 0 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R K) $$ 2 $ 2 = 1"
  unfolding exp_cnst_acc_sq_mtx scaleR_power const_acc_mtx_pow2
  by (auto simp: plus_sq_mtx_def scaleR_sq_mtx_def one_sq_mtx_def 
      mat_def scaleR_vec_def axis_def plus_vec_def)

lemma bouncing_ball_K: 
  "\<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil> \<subseteq> 
  wp (((x\<acute>=(*\<^sub>V) K & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE Id FI))\<^sup>*)
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule_tac I="\<lceil>\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and> 
  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)\<rceil>" in rel_ad_mka_starI)
    apply(simp, simp only: rel_antidomain_kleene_algebra.fbox_seq)
   apply(subst p2r_r2p_wp[symmetric, of "(IF (\<lambda>s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE Id FI)"])
   apply(subst local_flow.wp_g_orbit[OF local_flow_exp])
   apply(subst rel_antidomain_kleene_algebra.fbox_cond_var)
   apply(simp add: wp_rel sq_mtx_vec_prod_eq)
   apply(simp add: p2r_r2p_simps)
  unfolding UNIV_3 image_le_pred apply(simp add: exp_cnst_acc_sq_mtx_simps, safe)
  subgoal for x using bb_real_arith(3)[of "x $ 2"]
    by (simp add: add.commute mult.commute)
  subgoal for x \<tau> using bb_real_arith(4)[where g="x $ 2" and v="x $ 1"]
    by(simp add: add.commute mult.commute)
  by (force simp: bb_real_arith p2r_def)

no_notation constant_acceleration_kinematics_sq_mtx ("K")

end