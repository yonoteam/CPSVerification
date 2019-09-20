(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory hs_vc_examples
  imports hs_prelims_matrices hs_vc_spartan

begin

text\<open> Preliminary preparation for the examples.\<close>

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

abbreviation val_p :: "real^program_vars \<Rightarrow> string \<Rightarrow> real" (infixl "\<downharpoonright>\<^sub>V" 90) 
  where "store\<downharpoonright>\<^sub>Vvar \<equiv> store$\<restriction>\<^sub>Vvar"

\<comment> \<open>Alternative to the finite set of program variables.\<close>

lemma "CARD(2) = CARD(program_vars)"
  unfolding number_of_program_vars by simp

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

abbreviation circular_motion_vec_field :: "real^program_vars \<Rightarrow> real^program_vars" ("C")
  where "circular_motion_vec_field s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s\<downharpoonright>\<^sub>V''y'' else -s\<downharpoonright>\<^sub>V''x'')"

lemma circular_motion_invariants:
  "(\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) \<le> |x\<acute>=C & G] (\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2)"
  by (auto intro!: diff_invariant_rules poly_derivatives simp: to_var_inject)

\<comment> \<open>Verified with the flow. \<close>

abbreviation circular_motion_flow :: "real \<Rightarrow> real^program_vars \<Rightarrow> real^program_vars" ("\<phi>\<^sub>C")
  where "\<phi>\<^sub>C t s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s\<downharpoonright>\<^sub>V''x'' * cos t + s\<downharpoonright>\<^sub>V''y'' * sin t
  else - s\<downharpoonright>\<^sub>V''x'' * sin t + s\<downharpoonright>\<^sub>V''y'' * cos t)"

lemma local_flow_circ_motion: "local_flow C UNIV UNIV \<phi>\<^sub>C"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject power2_commute)
   apply(clarsimp, case_tac "i = \<restriction>\<^sub>V''x''")
    using program_vars_exhaust by (force intro!: poly_derivatives simp: to_var_inject)+

lemma circular_motion:
  "(\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) \<le> |x\<acute>=C & G] (\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2)"
  by (force simp: local_flow.fbox_g_ode[OF local_flow_circ_motion] to_var_inject)

\<comment> \<open>Verified by providing dynamics. \<close>

lemma circular_motion_dyn:
  "(\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2) \<le> |EVOL \<phi>\<^sub>C G T] (\<lambda>s. r\<^sup>2 = (s\<downharpoonright>\<^sub>V''x'')\<^sup>2 + (s\<downharpoonright>\<^sub>V''y'')\<^sup>2)"
  by (force simp: to_var_inject)

no_notation circular_motion_vec_field ("C")
        and circular_motion_flow ("\<phi>\<^sub>C")

\<comment> \<open>Verified as a linear system (using uniqueness). \<close>

abbreviation circular_motion_sq_mtx :: "2 sq_mtx" ("C")
  where "C \<equiv> sq_mtx_chi (\<chi> i. if i=0 then - \<e> 1 else \<e> 0)"

abbreviation circular_motion_mtx_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>\<^sub>C")
  where "\<phi>\<^sub>C t s \<equiv> (\<chi> i. if i = 0 then s$0 * cos t - s$1 * sin t else s$0 * sin t + s$1 * cos t)"

lemma circular_motion_mtx_exp_eq: "exp (t *\<^sub>R C) *\<^sub>V s = \<phi>\<^sub>C t s"
  apply(rule local_flow.eq_solution[OF local_flow_exp, symmetric])
    apply(rule ivp_solsI, simp add: sq_mtx_vec_prod_def matrix_vector_mult_def)
      apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by (force simp: vec_eq_iff, auto)

lemma circular_motion_sq_mtx:
  "(\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2) \<le> fbox (x\<acute>=(*\<^sub>V) C & G) (\<lambda>s. r\<^sup>2 = (s$0)\<^sup>2 + (s$1)\<^sup>2)"
  unfolding local_flow.fbox_g_ode[OF local_flow_exp] circular_motion_mtx_exp_eq by auto

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

abbreviation cnst_acc_vec_field :: "real \<Rightarrow> real^program_vars \<Rightarrow> real^program_vars" ("K")
  where "K a s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V''x'') then s\<downharpoonright>\<^sub>V''y'' else a)"

lemma bouncing_ball_invariants:
  shows "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = h \<and> s\<downharpoonright>\<^sub>V''y'' = 0) \<le> fbox 
  (LOOP 
    ((x\<acute>=K g & (\<lambda> s. s\<downharpoonright>\<^sub>V''x'' \<ge> 0) DINV (\<lambda>s. 2 * g * s\<downharpoonright>\<^sub>V''x'' - 2 * g * h - (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y'') = 0)) ;
    (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = 0) THEN (\<restriction>\<^sub>V''y'' ::= (\<lambda>s. - s\<downharpoonright>\<^sub>V''y'')) ELSE skip))
  INV (\<lambda>s.  s\<downharpoonright>\<^sub>V''x'' \<ge> 0 \<and> 2 * g * s\<downharpoonright>\<^sub>V''x'' - 2 * g * h - (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y'') = 0))
  (\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and> s\<downharpoonright>\<^sub>V''x'' \<le> h)"
  apply(rule fbox_loopI, simp_all)
    apply(force, force simp: bb_real_arith)
  by (rule fbox_g_odei) (auto intro!: poly_derivatives diff_invariant_rules simp: to_var_inject)

\<comment> \<open>Verified with the flow. \<close>

lemma picard_lindeloef_cnst_acc:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. K g) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject)

abbreviation cnst_acc_flow :: "real \<Rightarrow> real \<Rightarrow> real^program_vars \<Rightarrow> real^program_vars" ("\<phi>\<^sub>K")
  where "\<phi>\<^sub>K a t s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V ''x'') then a * t ^ 2/2 + s $ (\<restriction>\<^sub>V ''y'') * t + s $ (\<restriction>\<^sub>V ''x'') 
        else a * t + s $ (\<restriction>\<^sub>V ''y''))"

lemma local_flow_cnst_acc: "local_flow (K g) UNIV UNIV (\<phi>\<^sub>K g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  apply(simp add: dist_norm norm_vec_def L2_set_def program_vars_univ_eq to_var_inject)
   apply(clarsimp, case_tac "i = \<restriction>\<^sub>V ''x''")
  using program_vars_exhaust by(auto intro!: poly_derivatives simp: to_var_inject vec_eq_iff)

lemma [bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
    and pos: "g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real) = 0"
  shows "2 * g * h + (g * \<tau> + v) * (g * \<tau> + v) = 0"
proof-
  from pos have "g * \<tau>\<^sup>2  + 2 * v * \<tau> + 2 * x = 0" by auto
  then have "g\<^sup>2 * \<tau>\<^sup>2  + 2 * g * v * \<tau> + 2 * g * x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 * \<tau>\<^sup>2 + 2 * g * v * \<tau> + v\<^sup>2 + 2 * g * h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  hence obs: "(g * \<tau> + v)\<^sup>2 + 2 * g * h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  thus "2 * g * h + (g * \<tau> + v) * (g * \<tau> + v) = 0"
    by (simp add: add.commute distrib_right power2_eq_square)
qed

lemma [bb_real_arith]:
  assumes invar: "2 * g * x = 2 * g * h + v * v"
  shows "2 * g * (g * \<tau>\<^sup>2 / 2 + v * \<tau> + (x::real)) = 
  2 * g * h + (g * \<tau> + v) * (g * \<tau> + v)" (is "?lhs = ?rhs")
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

lemma bouncing_ball: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = h \<and> s\<downharpoonright>\<^sub>V''y'' = 0) \<le> fbox 
  (LOOP 
    ((x\<acute>=K g & (\<lambda> s. s\<downharpoonright>\<^sub>V''x'' \<ge> 0)) ;
    (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''x'' = 0) THEN (\<restriction>\<^sub>V''y'' ::= (\<lambda>s. - s\<downharpoonright>\<^sub>V''y'')) ELSE skip))
  INV (\<lambda>s.  s\<downharpoonright>\<^sub>V''x'' \<ge> 0 \<and> 2 * g * s\<downharpoonright>\<^sub>V''x'' = 2 * g * h + (s\<downharpoonright>\<^sub>V''y'' * s\<downharpoonright>\<^sub>V''y'')))
  (\<lambda>s. 0 \<le> s\<downharpoonright>\<^sub>V''x'' \<and> s\<downharpoonright>\<^sub>V''x'' \<le> h)"
  apply(rule fbox_loopI, simp_all add: local_flow.fbox_g_ode[OF local_flow_cnst_acc])
  by (auto simp: bb_real_arith to_var_inject)

no_notation cnst_acc_vec_field ("K")
        and cnst_acc_flow ("\<phi>\<^sub>K")
        and to_var ("\<restriction>\<^sub>V")
        and val_p (infixl "\<downharpoonright>\<^sub>V" 90)


\<comment> \<open>Verified as a linear system (computing exponential). \<close>

abbreviation cnst_acc_sq_mtx :: "3 sq_mtx" ("K")
  where "K \<equiv> sq_mtx_chi (\<chi> i::3. if i=0 then \<e> 1 else if i=1 then \<e> 2 else 0)"

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

lemma bouncing_ball_sq_mtx: 
  "(\<lambda>s. 0 \<le> s$0 \<and> s$0 = h \<and> s$1 = 0 \<and> 0 > s$2) \<le> fbox 
  (LOOP ((x\<acute>=(*\<^sub>V) K & (\<lambda> s. s$0 \<ge> 0)) ;
  (IF (\<lambda> s. s$0 = 0) THEN (1 ::= (\<lambda>s. - s$1)) ELSE skip))
  INV (\<lambda>s. 0\<le>s$0 \<and> 0>s$2 \<and> 2 * s$2 * s$0 = 2 * s$2 * h + (s$1 * s$1)))
  (\<lambda>s. 0 \<le> s$0 \<and> s$0 \<le> h)"
  apply(rule fbox_loopI[of _ "(\<lambda>s. 0\<le>s$0 \<and> 0>s$2 \<and> 2 * s$2 * s$0 = 2 * s$2 * h + (s$1 * s$1))"])
    apply(simp_all add: local_flow.fbox_g_ode[OF local_flow_exp] sq_mtx_vec_prod_eq)
    apply(force, force simp: bb_real_arith)
  unfolding UNIV_3 apply(simp add: exp_cnst_acc_sq_mtx_simps, safe)
  using bb_real_arith(2)[of _ _ h] apply (force simp: field_simps)
  subgoal for s \<tau> using bb_real_arith(3)[of "s$2"] by(simp add: field_simps)
  done

no_notation cnst_acc_sq_mtx ("K")


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

abbreviation val_T :: "real^thermostat_vars \<Rightarrow> string \<Rightarrow> real" (infixl "\<downharpoonright>\<^sub>V" 90) 
  where "store\<downharpoonright>\<^sub>Vvar \<equiv> store$\<restriction>\<^sub>Vvar"

lemma thermostat_vars_allI: 
  "P (\<restriction>\<^sub>V''t'') \<Longrightarrow> P (\<restriction>\<^sub>V''T'') \<Longrightarrow> P (\<restriction>\<^sub>V''on'') \<Longrightarrow> P (\<restriction>\<^sub>V''TT'') \<Longrightarrow> \<forall>i. P i"
  using thermostat_vars_exhaust by metis

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^thermostat_vars \<Rightarrow> real^thermostat_vars" ("f\<^sub>T")
  where "f\<^sub>T a L s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''t'' then 1 else (if i=\<restriction>\<^sub>V''T'' then - a * (s\<downharpoonright>\<^sub>V''T'' - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^thermostat_vars \<Rightarrow> real^thermostat_vars" ("\<phi>\<^sub>T")
  where "\<phi>\<^sub>T a L t s \<equiv> (\<chi> i. if i=\<restriction>\<^sub>V''T'' then - exp(-a * t) * (L - s\<downharpoonright>\<^sub>V''T'') + L else 
  (if i=\<restriction>\<^sub>V''t'' then t + s\<downharpoonright>\<^sub>V''t'' else 
  (if i=\<restriction>\<^sub>V''on'' then s\<downharpoonright>\<^sub>V''on'' else s\<downharpoonright>\<^sub>V''TT'')))"

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
   apply(rule thermostat_vars_allI, simp_all add: to_var_inject)
  using thermostat_vars_exhaust by (auto intro!: poly_derivatives simp: vec_eq_iff to_var_inject)

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

lemmas wlp_temp_dyn = local_flow.fbox_g_ode_ivl[OF local_flow_temp_up _ UNIV_I]

lemma thermostat: 
  assumes "a > 0" and "0 \<le> t" and "0 < Tmin" and "Tmax < L"
  shows "(\<lambda>s. Tmin \<le> s\<downharpoonright>\<^sub>V''T'' \<and> s\<downharpoonright>\<^sub>V''T'' \<le> Tmax \<and> s\<downharpoonright>\<^sub>V''on''=0) \<le> 
  |LOOP 
    \<comment> \<open>control\<close>
    (((\<restriction>\<^sub>V''t'')::=(\<lambda>s.0));((\<restriction>\<^sub>V''TT'')::=(\<lambda>s. s\<downharpoonright>\<^sub>V''T''));
    (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=0 \<and> s\<downharpoonright>\<^sub>V''TT''\<le>Tmin + 1) THEN (\<restriction>\<^sub>V''on'' ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=1 \<and> s\<downharpoonright>\<^sub>V''TT''\<ge>Tmax - 1) THEN (\<restriction>\<^sub>V''on'' ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s\<downharpoonright>\<^sub>V''on''=0) THEN (x\<acute>=(f\<^sub>T a 0) & (\<lambda>s. s\<downharpoonright>\<^sub>V''t'' \<le> - (ln (Tmin/s\<downharpoonright>\<^sub>V''TT''))/a) on {0..t} UNIV @ 0) 
     ELSE (x\<acute>=(f\<^sub>T a L) & (\<lambda>s. s\<downharpoonright>\<^sub>V''t'' \<le> - (ln ((L-Tmax)/(L-s\<downharpoonright>\<^sub>V''TT'')))/a) on {0..t} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s\<downharpoonright>\<^sub>V''T'' \<and> s\<downharpoonright>\<^sub>V''T''\<le>Tmax \<and> (s\<downharpoonright>\<^sub>V''on''=0 \<or> s\<downharpoonright>\<^sub>V''on''=1))]
  (\<lambda>s. Tmin \<le> s$\<restriction>\<^sub>V''T'' \<and> s$\<restriction>\<^sub>V''T'' \<le> Tmax)"
  apply(rule fbox_loopI, simp_all add: wlp_temp_dyn[OF assms(1,2)] le_fun_def to_var_inject, safe)
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

no_notation thermostat_vars.to_var ("\<restriction>\<^sub>V")
        and val_T (infixl "\<downharpoonright>\<^sub>V" 90)
        and temp_vec_field ("f\<^sub>T")
        and temp_flow ("\<phi>\<^sub>T")


subsubsection\<open> Thermostat \<close>

abbreviation tank_vec_field :: "real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f k s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then k else 0))"

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> k \<tau> s \<equiv> (\<chi> i. if i = 1 then k * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Hm k s \<equiv> s$2 \<le> (Hm - s$3)/k"

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I hmin hmax s \<equiv> hmin \<le> s$1 \<and> s$1 \<le> hmax \<and> (s$4 = 0 \<or> s$4 = 1)"

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("dI")
  where "dI hmin hmax k s \<equiv> s$1 = k * s$2 + s$3 \<and> 0 \<le> s$2 \<and> 
    hmin \<le> s$3 \<and> s$3 \<le> hmax \<and> (s$4 =0 \<or> s$4 = 1)"

lemma local_flow_tank: "local_flow (f k) UNIV UNIV (\<phi> k)"
  apply (unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4)
  by (auto intro!: poly_derivatives simp: vec_eq_iff)

lemma tank_arith:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((hmin - y) / c\<^sub>o) \<Longrightarrow>  hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> hmax"
    and "hmin \<le> y \<Longrightarrow> hmin \<le> (c\<^sub>i - c\<^sub>o) * \<tau> + y"
    and "y \<le> hmax \<Longrightarrow> y - c\<^sub>o * \<tau> \<le> hmax"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

lemma tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "I hmin hmax \<le>
  |LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(3 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> hmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0) 
     ELSE (x\<acute>= f (-c\<^sub>o) & G hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0)) ) INV I hmin hmax]  
  I hmin hmax"
  apply(rule fbox_loopI, simp_all add: le_fun_def)
  apply(clarsimp simp: le_fun_def local_flow.fbox_g_ode_ivl[OF local_flow_tank assms(1) UNIV_I])
  using assms tank_arith[OF _ assms(2,3)] by auto

no_notation tank_vec_field ("f")
        and tank_flow ("\<phi>")

end