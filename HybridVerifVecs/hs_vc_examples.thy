theory hs_vc_examples
  imports hs_prelims_matrices hs_vc_spartan

begin


subsection\<open> Examples \<close>

text\<open> Preliminary preparation for the examples.\<close>

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

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

lemma sum_axis_UNIV_3[simp]: "(\<Sum>j\<in>(UNIV::3 set). axis i 1 $ j * f j) = (f::3 \<Rightarrow> real) i"
  unfolding axis_def UNIV_3 apply simp
  using exhaust_3 by force


subsubsection\<open>Circular Motion\<close>

\<comment> \<open>Verified with differential invariants. \<close>

abbreviation "valP store var \<equiv> store$\<restriction>\<^sub>Vvar"

notation valP (infixl "\<downharpoonright>\<^sub>V" 90)

abbreviation circular_motion_kinematics :: "real^program_vars \<Rightarrow> real^program_vars" 
  where "circular_motion_kinematics s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s\<downharpoonright>\<^sub>V''y'' else -s\<downharpoonright>\<^sub>V''x'')"

notation circular_motion_kinematics ("C")

lemma circular_motion_invariant: 
  "diff_invariant (\<lambda>s. (r::real)\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) C UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth, drule_tac i="\<restriction>\<^sub>V''y''" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives simp: to_var_inject)

lemma circular_motion_invariants:
  "(\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) \<le> fbox (x\<acute>=C & G) (\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2)"
  unfolding fbox_diff_inv using circular_motion_invariant by simp

\<comment> \<open>Verified with the flow. \<close>

abbreviation "circular_motion_flow t s \<equiv> 
  (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s\<downharpoonright>\<^sub>V''x'' * cos t + s\<downharpoonright>\<^sub>V''y'' * sin t
  else - s\<downharpoonright>\<^sub>V''x'' * sin t + s\<downharpoonright>\<^sub>V''y'' * cos t)"

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
  "(\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) \<le> fbox (x\<acute>=C & G) (\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2)"
  by (subst local_flow.fbox_g_orbit[OF local_flow_circ_motion]) (auto simp: to_var_inject)

no_notation circular_motion_kinematics ("C")
        and circular_motion_flow ("\<phi>\<^sub>C")

\<comment> \<open>Verified as a linear system (using uniqueness). \<close>

abbreviation circular_motion_sq_mtx :: "2 sq_mtx" 
  where "circular_motion_sq_mtx \<equiv> sq_mtx_chi (\<chi> i. if i=0 then - \<e> 1 else \<e> 0)"

abbreviation circular_motion_mtx_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" 
  where "circular_motion_mtx_flow t s \<equiv> 
  (\<chi> i. if i=(0::2) then s$0 * cos t - s$1 * sin t else s$0 * sin t + s$1 * cos t)"

notation circular_motion_sq_mtx ("C")
     and circular_motion_mtx_flow ("\<phi>\<^sub>C")

lemma circular_motion_mtx_exp_eq: "exp (t *\<^sub>R C) *\<^sub>V s = \<phi>\<^sub>C t s"
  apply(rule local_flow.eq_solution[OF local_flow_exp, symmetric])
    apply(rule ivp_solsI, rule has_vderiv_on_vec_lambda, clarsimp)
  unfolding sq_mtx_vec_prod_def matrix_vector_mult_def apply simp
      apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by (force simp: vec_eq_iff, auto)

lemma circular_motion_sq_mtx:
  "(\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2) \<le> fbox (x\<acute>=(*\<^sub>V) C & G) (\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2)"
  unfolding local_flow.fbox_g_orbit[OF local_flow_exp] circular_motion_mtx_exp_eq by auto

no_notation circular_motion_sq_mtx ("C")
        and circular_motion_mtx_flow ("\<phi>\<^sub>C")


subsubsection\<open> Bouncing Ball \<close>

\<comment> \<open>Verified with differential invariants. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]: 
  assumes "0 > g" and inv: "2 * g * x - 2 * g * h = v * v"
  shows "(x::real) \<le> h"
proof-
  have "v * v = 2 * g * x - 2 * g * h \<and> 0 > g" 
    using inv and \<open>0 > g\<close> by auto
  hence obs:"v * v = 2 * g * (x - h) \<and> 0 > g \<and> v * v \<ge> 0" 
    using left_diff_distrib mult.commute by (metis zero_le_square) 
  hence "(v * v)/(2 * g) = (x - h)" 
    by auto 
  also from obs have "(v * v)/(2 * g) \<le> 0"
    using divide_nonneg_neg by fastforce 
  ultimately have "h - x \<ge> 0" 
    by linarith
  thus ?thesis by auto
qed

abbreviation "constant_acceleration_kinematics g s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V''x'') then s\<downharpoonright>\<^sub>V''y'' else g)"

notation constant_acceleration_kinematics ("K")

lemma energy_conservation_invariant: 
  fixes g h :: real
  defines dinv: "I \<equiv> (\<lambda>s. 2 * g * s\<downharpoonright>\<^sub>V''x'' - 2 * g * h - (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y'') = 0)"
  shows "diff_invariant I (K g) UNIV UNIV 0 G"
  unfolding dinv apply(rule diff_invariant_rules, simp, simp, clarify)
  apply(frule_tac i="\<restriction>\<^sub>V''y''" in has_vderiv_on_vec_nth)
  apply(drule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives simp: to_var_inject)

lemma bouncing_ball_invariants:
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines diff_inv: "I \<equiv> (\<lambda>s. 2 * g * s\<downharpoonright>\<^sub>V''x'' - 2 * g * h - (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y'') = 0)"
  shows "(\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = h \<and> s\<downharpoonright>\<^sub>V''y'' = 0) \<le> fbox 
  ( ( (x\<acute>=K g & (\<lambda> s. s\<downharpoonright>\<^sub>V''x'' \<ge> 0)) ;
  (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = 0) THEN ((\<restriction>\<^sub>V''y'') ::= (\<lambda>s. - s\<downharpoonright>\<^sub>V''y'')) ELSE (\<lambda>s.{s})) )\<^sup>*)
  (\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and> s\<downharpoonright>\<^sub>V''x'' \<le> h)"
  apply(rule fbox_kstarI[of _ "(\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and> I s)"])
  using \<open>h \<ge> 0\<close> apply(subst diff_inv, clarsimp)
  using \<open>g < 0\<close> apply(subst diff_inv, clarsimp, force simp: bb_real_arith)
  apply(simp only: fbox_kcomp)
  apply(rule_tac b="fbox (x\<acute>=(K g) & (\<lambda> s. s\<downharpoonright>\<^sub>V''x''\<ge>0)) (\<lambda>s. 0\<le>s\<downharpoonright>\<^sub>V''x'' \<and> I s)" in order.trans)
   apply(simp add: fbox_g_orbital_guard)
   apply(rule_tac b="I" in order.trans, force)
  unfolding fbox_diff_inv apply(simp_all add: diff_inv)
  using energy_conservation_invariant apply force
  apply(rule fbox_iso) using assms unfolding diff_inv fbox_if_then_else
  by (force simp: bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma picard_lindeloef_cnst_acc:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. K g) UNIV UNIV 0"
  apply(unfold_locales)
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject)

abbreviation "constant_acceleration_kinematics_flow g t s \<equiv> 
  (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then g * t ^ 2/2 + s $ (\<restriction>\<^sub>V ''y'') * t + s $ (\<restriction>\<^sub>V ''x'') 
        else g * t + s $ (\<restriction>\<^sub>V ''y''))"

notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")

lemma local_flow_cnst_acc: "local_flow (K g) UNIV UNIV (\<phi>\<^sub>K g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V ''x''")
  using program_vars_exhaust by(auto intro!: poly_derivatives simp: to_var_inject vec_eq_iff)

lemma [bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
    and pos: "g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real) = 0"
  shows "2 * g * h + (g * \<tau> * (g * \<tau> + v) + v * (g * \<tau> + v)) = 0"
    and "2 * g * h + (- (g * \<tau>) - v) * (- (g * \<tau>) - v) = 0"
proof-
  from pos have "g * \<tau>\<^sup>2  + 2 * v * \<tau> + 2 * x = 0" by auto
  then have "g\<^sup>2  * \<tau>\<^sup>2  + 2 * g * v * \<tau> + 2 * g * x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + v\<^sup>2 + 2 * g * h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  hence obs: "(g * \<tau> + v)\<^sup>2 + 2 * g * h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  thus "2 * g * h + (g * \<tau> * (g * \<tau> + v) + v * (g * \<tau> + v)) = 0"
    by (simp add: add.commute distrib_right power2_eq_square)
  have  "2 * g * h + (- ((g * \<tau>) + v))\<^sup>2 = 0"
    using obs by (metis Groups.add_ac(2) power2_minus)
  thus "2 * g * h + (- (g * \<tau>) - v) * (- (g * \<tau>) - v) = 0"
    by (simp add: distrib_right power2_eq_square)
qed

lemma [bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
  shows "2 * g * (g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real)) = 
  2 * g * h + (g * \<tau> * (g * \<tau> + v) + v * (g * \<tau> + v))" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * x" 
      apply(subst Rat.sign_simps(18))+ 
      by(auto simp: semiring_normalization_rules(29))
    also have "... = g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + 2 * g * h + v * v" (is "... = ?middle")
      by(subst invar, simp)
    finally have "?lhs = ?middle".
  moreover 
  {have "?rhs = g * g * (\<tau> * \<tau>) + 2 * g * v * \<tau> + 2 * g * h + v * v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball:
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines loop_inv: "I \<equiv> (\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and>  2 * g * s\<downharpoonright>\<^sub>V''x'' = 2 * g * h + (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y''))"
  shows "(\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = h \<and> s\<downharpoonright>\<^sub>V''y'' = 0) \<le> fbox 
  (((x\<acute>=K g & (\<lambda> s. s\<downharpoonright>\<^sub>V''x'' \<ge> 0)) ;
  (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = 0) THEN ((\<restriction>\<^sub>V''y'')::=(\<lambda>s. - s\<downharpoonright>\<^sub>V''y'')) ELSE skip))\<^sup>*)
  (\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and> s\<downharpoonright>\<^sub>V''x'' \<le> h)"
  apply(rule fbox_kstarI[of _ I])
  using \<open>h \<ge> 0\<close> apply(subst loop_inv, clarsimp)
  using \<open>g < 0\<close> apply(subst loop_inv, clarsimp, force simp: bb_real_arith)
  apply(simp only: fbox_kcomp)
  unfolding loop_inv using \<open>h \<ge> 0\<close> apply(clarsimp, simp only: fbox_kcomp)
   apply(subst local_flow.fbox_g_orbit[OF local_flow_cnst_acc], simp)
  unfolding fbox_if_then_else fbox_assign using \<open>g < 0\<close>
  by (auto simp: bb_real_arith to_var_inject) (force simp: field_simps)

no_notation constant_acceleration_kinematics ("K")
        and constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")
        and to_var ("\<restriction>\<^sub>V")
        and valP (infixl "\<downharpoonright>\<^sub>V" 90)


\<comment> \<open>Verified as a linear system (computing exponential). \<close>

abbreviation constant_acceleration_kinematics_sq_mtx :: "3 sq_mtx" 
  where "constant_acceleration_kinematics_sq_mtx \<equiv> 
    sq_mtx_chi (\<chi> i::3. if i=0 then \<e> 1 else if i=1 then \<e> 2 else 0)"

notation constant_acceleration_kinematics_sq_mtx ("K")

lemma const_acc_mtx_pow2: "K\<^sup>2 = sq_mtx_chi (\<chi> i. if i=0 then \<e> 2 else 0)"
  unfolding power2_eq_square times_sq_mtx_def 
  by(simp add: sq_mtx_chi_inject vec_eq_iff matrix_matrix_mult_def)

lemma const_acc_mtx_powN: "n > 2 \<Longrightarrow> (\<tau> *\<^sub>R K)^n = 0"
  apply(induct n, simp, case_tac "n \<le> 2")
   apply(simp only: le_less_Suc_eq power_Suc, simp)
  by(auto simp: const_acc_mtx_pow2 sq_mtx_chi_inject vec_eq_iff 
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
  "(\<lambda>s. 0 \<le> s$0 \<and> s$0 = h \<and> s$1 = 0 \<and> 0 > s$2) \<le> fbox 
  (((x\<acute>=(*\<^sub>V) K & (\<lambda> s. s$0 \<ge> 0)) ;
  (IF (\<lambda> s. s$0 = 0) THEN (1 ::= (\<lambda>s. - s$1)) ELSE skip))\<^sup>*)
  (\<lambda>s. 0 \<le> s$0 \<and> s$0 \<le> h)"
  apply(rule fbox_kstarI[of _ "(\<lambda>s. 0\<le>s$0 \<and> 0>s$2 \<and> 2 * s$2 * s$0 = 2 * s$2 * h + (s$1 * s$1))"])
    apply(clarsimp, clarsimp, force simp: bb_real_arith)
  apply(simp only: fbox_kcomp)
   apply(subst local_flow.fbox_g_orbit[OF local_flow_exp])
  apply(subst fbox_if_then_else, simp add: sq_mtx_vec_prod_eq)
  unfolding UNIV_3 apply(simp add: exp_cnst_acc_sq_mtx_simps, safe)
  subgoal for s \<tau> using bb_real_arith(2)[of "s$2" "s$0" h "s$1" \<tau>]
    by (simp add: field_simps)
  subgoal for s \<tau> using bb_real_arith(4)[where g="s$2" and v="s$1"]
    by(simp add: field_simps)
  done

no_notation constant_acceleration_kinematics_sq_mtx ("K")


subsubsection\<open> Thermostat \<close>

typedef thermostat_vars = "{''t'',''T'',''on'',''TT''}"
  morphisms to_str to_var
  apply(rule_tac x="''t''" in exI)
  by simp

notation to_var ("\<restriction>\<^sub>V")

lemma number_of_thermostat_vars: "CARD(thermostat_vars) = 4"
  using type_definition.card type_definition_thermostat_vars by fastforce

instance thermostat_vars::finite
  apply(standard)
  apply(subst bij_betw_finite[of to_str UNIV "{''t'',''T'',''on'',''TT''}"])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma thermostat_vars_univ_eq: 
  "(UNIV::thermostat_vars set) = {\<restriction>\<^sub>V''t'',\<restriction>\<^sub>V''T'',\<restriction>\<^sub>V''on'',\<restriction>\<^sub>V''TT''}"
  apply auto by (metis to_str to_str_inverse insertE singletonD) 

lemma thermostat_vars_exhaust: "x=\<restriction>\<^sub>V''t'' \<or> x=\<restriction>\<^sub>V''T'' \<or> x=\<restriction>\<^sub>V''on'' \<or> x=\<restriction>\<^sub>V''TT''"
  using thermostat_vars_univ_eq by auto

lemma thermostat_vars_sum:
  fixes f :: "thermostat_vars \<Rightarrow> ('a::banach)"
  shows "(\<Sum>(i::thermostat_vars)\<in>UNIV. f i) = 
  f (\<restriction>\<^sub>V''t'') + f (\<restriction>\<^sub>V''T'') + f (\<restriction>\<^sub>V''on'')+ f (\<restriction>\<^sub>V''TT'')"
  unfolding thermostat_vars_univ_eq by (simp add: to_var_inject)

abbreviation "valT store var \<equiv> store$\<restriction>\<^sub>Vvar"

notation valT (infixl "\<downharpoonright>\<^sub>V" 90)

lemma thermostat_vars_allI: 
  "P (\<restriction>\<^sub>V''t'') \<Longrightarrow> P (\<restriction>\<^sub>V''T'') \<Longrightarrow> P (\<restriction>\<^sub>V''on'') \<Longrightarrow> P (\<restriction>\<^sub>V''TT'') \<Longrightarrow> \<forall>i. P i"
  using thermostat_vars_exhaust by metis

abbreviation "temp_dynamics (a::real) L s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''t'' then 1 else 
  (if i=\<restriction>\<^sub>V''T'' then - a * (s\<downharpoonright>\<^sub>V''T'' - L) else 0))"

notation temp_dynamics ("f\<^sub>T")

abbreviation "temp_flow a L t s \<equiv> 
  (\<chi> i. if i=\<restriction>\<^sub>V''T'' then - exp(-a * t) * (L - s\<downharpoonright>\<^sub>V''T'') + L else 
  (if i=\<restriction>\<^sub>V''t'' then t + s\<downharpoonright>\<^sub>V''t'' else 
  (if i=\<restriction>\<^sub>V''on'' then s\<downharpoonright>\<^sub>V''on'' else s\<downharpoonright>\<^sub>V''TT'')))"

notation temp_flow ("\<phi>\<^sub>T")

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f\<^sub>T a L s\<^sub>1 - f\<^sub>T a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1\<downharpoonright>\<^sub>V''T'' - s\<^sub>2\<downharpoonright>\<^sub>V''T''\<bar>"
proof(simp add: norm_vec_def L2_set_def thermostat_vars_sum to_var_inject)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1\<downharpoonright>\<^sub>V''T'' + - L) + - (a * (s\<^sub>2\<downharpoonright>\<^sub>V''T'' + - L))\<bar> = a * \<bar>s\<^sub>1\<downharpoonright>\<^sub>V''T'' + - s\<^sub>2\<downharpoonright>\<^sub>V''T''\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2\<downharpoonright>\<^sub>V''T'' - L) - a * (s\<^sub>1\<downharpoonright>\<^sub>V''T'' - L)\<bar> = a * \<bar>s\<^sub>1\<downharpoonright>\<^sub>V''T'' - s\<^sub>2\<downharpoonright>\<^sub>V''T''\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_temp_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f\<^sub>T a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms apply(simp add: norm_diff_temp_dyn)
  apply(simp add: norm_vec_def L2_set_def)
  apply(unfold thermostat_vars_univ_eq, simp add: to_var_inject, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp_up: "a > 0 \<Longrightarrow> local_flow (f\<^sub>T a L) UNIV UNIV (\<phi>\<^sub>T a L)"
  apply(unfold_locales, simp_all)
  using local_lipschitz_temp_dyn apply blast
   apply(rule has_vderiv_on_vec_lambda, rule thermostat_vars_allI, simp_all add: to_var_inject)
  using thermostat_vars_exhaust by (auto intro!: poly_derivatives simp: vec_eq_iff to_var_inject)

lemmas wlp_temp_dyn = local_flow.fbox_g_orbit_ivl[OF local_flow_temp_up _ UNIV_I]

lemma temp_dyn_down_real_arith:
  assumes "a > 0" and Thyps: "0 < Tmin" "Tmin \<le> T" "T \<le> Tmax"
    and thyps: "0 \<le> (t::real)" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln (Tmin / T) / a) "
  shows "Tmin \<le> exp (-a * t) * T" and "exp (-a * t) * T \<le> Tmax"
proof-
  have "0 \<le> t \<and> t \<le> - (ln (Tmin / T) / a)"
    using thyps by auto
  hence "ln (Tmin / T) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "Tmin / T > 0"
    using Thyps by auto
  ultimately have obs: "Tmin / T \<le> exp (-a * t)" "exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "Tmin \<le> exp (-a * t) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * t) * T \<le> Tmax"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T] 
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma temp_dyn_up_real_arith:
  assumes "a > 0" and Thyps: "Tmin \<le> T" "T \<le> Tmax" "Tmax < (L::real)"
    and thyps: "0 \<le> t" "\<forall>\<tau>\<in>{0..t}. \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a) "
  shows "L - Tmax \<le> exp (-(a * t)) * (L - T)" 
    and "L - exp (-(a * t)) * (L - T) \<le> Tmax" 
    and "Tmin \<le> L - exp (-(a * t)) * (L - T)"
proof-
  have "0 \<le> t \<and> t \<le> - (ln ((L - Tmax) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - Tmax) / (L - T)) \<le> - a * t \<and> - a * t \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - Tmax) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - Tmax) / (L - T) \<le> exp (-a * t) \<and> exp (-a * t) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - Tmax) \<le> exp (-a * t) * (L - T) \<and> exp (-a * t) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - Tmax) \<le> exp (-(a * t)) * (L - T)"
    by auto
  thus "L - exp (-(a * t)) * (L - T) \<le> Tmax"
    by auto
  show "Tmin \<le> L - exp (-(a * t)) * (L - T)"
    using Thyps and obs by auto
qed

lemma thermostat: 
  assumes "a > 0" and "0 \<le> t" and "0 < Tmin" and "Tmax < L"
  shows "(\<lambda>s. Tmin \<le> s\<downharpoonright>\<^sub>V''T'' \<and> s\<downharpoonright>\<^sub>V''T'' \<le> Tmax \<and> s\<downharpoonright>\<^sub>V''on''=0) \<le> fbox 
  ((((\<restriction>\<^sub>V''t'')::=(\<lambda>s.0));((\<restriction>\<^sub>V''TT'')::=(\<lambda>s. s\<downharpoonright>\<^sub>V''T''));
  (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=0 \<and> s\<downharpoonright>\<^sub>V''TT''\<le>Tmin + 1) THEN (\<restriction>\<^sub>V''on'' ::= (\<lambda>s.1)) ELSE 
  (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=1 \<and> s\<downharpoonright>\<^sub>V''TT''\<ge>Tmax - 1) THEN (\<restriction>\<^sub>V''on'' ::= (\<lambda>s.0)) ELSE skip));
  (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=0) THEN (x\<acute>=(f\<^sub>T a 0) & (\<lambda>s. s\<downharpoonright>\<^sub>V''t'' \<le> - (ln (Tmin/s\<downharpoonright>\<^sub>V''TT''))/a) on {0..t} UNIV @ 0) 
  ELSE (x\<acute>=(f\<^sub>T a L) & (\<lambda>s. s\<downharpoonright>\<^sub>V''t'' \<le> - (ln ((L-Tmax)/(L-s\<downharpoonright>\<^sub>V''TT'')))/a) on {0..t} UNIV @ 0)) )\<^sup>*)
  (\<lambda>s. Tmin \<le> s$\<restriction>\<^sub>V''T'' \<and> s$\<restriction>\<^sub>V''T'' \<le> Tmax)"
  apply(rule_tac I="\<lambda>s. Tmin \<le>s\<downharpoonright>\<^sub>V''T'' \<and> s\<downharpoonright>\<^sub>V''T''\<le>Tmax \<and> (s\<downharpoonright>\<^sub>V''on''=0 \<or> s\<downharpoonright>\<^sub>V''on''=1)" in fbox_kstarI)
    apply(simp add: le_fun_def, simp add: le_fun_def)
  apply(simp only: fbox_kcomp fbox_if_then_else fbox_assign)
  apply(simp only: wlp_temp_dyn[OF assms(1,2)], simp add: to_var_inject, clarsimp, safe)
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

no_notation thermostat_vars.to_var ("\<restriction>\<^sub>V")
        and valT (infixl "\<downharpoonright>\<^sub>V" 90)
        and temp_dynamics ("f\<^sub>T")
        and temp_flow ("\<phi>\<^sub>T")

end