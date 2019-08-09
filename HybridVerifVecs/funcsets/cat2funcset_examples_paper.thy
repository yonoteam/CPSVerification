theory cat2funcset_examples_paper
  imports cat2funcset

begin

subsection\<open> More Examples \<close>


subsubsection\<open> Bouncing Ball \<close>

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
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines linv: "I \<equiv> (\<lambda>s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and>  2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V''x'') = 
    2 \<cdot> g \<cdot> h + (s$(\<restriction>\<^sub>V''v'') \<cdot> s$(\<restriction>\<^sub>V''v'')))"
  shows "{s. s$(\<restriction>\<^sub>V''x'') = h \<and> s$(\<restriction>\<^sub>V''v'') = 0} \<le> fb\<^sub>\<F> 
  (kstar ((x\<acute>=K g & (\<lambda> s. s $ (\<restriction>\<^sub>V ''x'') \<ge> 0)) \<circ>\<^sub>K 
  (IF (\<lambda> s. s$(\<restriction>\<^sub>V''x'') = 0) THEN ((\<restriction>\<^sub>V''v'') ::= (\<lambda>s. - s$(\<restriction>\<^sub>V''v''))) ELSE \<eta> FI)))
  {s. 0 \<le> s$(\<restriction>\<^sub>V''x'') \<and> s$(\<restriction>\<^sub>V''x'') \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. I s}"])
  unfolding linv using \<open>h \<ge> 0\<close> apply(clarsimp, simp only: ffb_kcomp)
   apply(subst local_flow.ffb_g_orbit[OF local_flow_cnst_acc], simp)
  unfolding ffb_if_then_else using assms
  by (auto simp: bb_real_arith to_var_inject)

lemma energy_conservation_invariant: 
  fixes g h :: real
  defines dinv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V''x'') - 2 \<cdot> g \<cdot> h - (s$(\<restriction>\<^sub>V''v'') \<cdot> s$(\<restriction>\<^sub>V''v'')) = 0)"
  shows "diff_invariant I (K g) UNIV UNIV 0 G"
  unfolding dinv apply(rule diff_invariant_rules, simp, simp, clarify)
  apply(frule_tac i="\<restriction>\<^sub>V''v''" in has_vderiv_on_vec_nth)
  apply(drule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth)
  apply(rule_tac S="UNIV" in has_vderiv_on_subset)
  by(auto intro!: poly_derivatives simp: to_var_inject)

lemma bouncing_ball_invariants:
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines dinv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s$(\<restriction>\<^sub>V ''x'') - 2 \<cdot> g \<cdot> h - (s$(\<restriction>\<^sub>V ''v'') \<cdot> s$(\<restriction>\<^sub>V ''v'')) = 0)"
  shows "{s. s$(\<restriction>\<^sub>V ''x'') = h \<and> s$(\<restriction>\<^sub>V ''v'') = 0} \<le> fb\<^sub>\<F> 
  (kstar ((x\<acute>=K g & (\<lambda> s. s $ (\<restriction>\<^sub>V ''x'') \<ge> 0)) \<circ>\<^sub>K 
  (IF (\<lambda> s. s$(\<restriction>\<^sub>V ''x'') = 0) THEN ((\<restriction>\<^sub>V ''v'') ::= (\<lambda>s. - s$(\<restriction>\<^sub>V ''v''))) ELSE \<eta> FI)))
  {s. 0 \<le> s$(\<restriction>\<^sub>V ''x'') \<and> s$(\<restriction>\<^sub>V ''x'') \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. 0 \<le> s$(\<restriction>\<^sub>V ''x'') \<and> I s}"])
  using \<open>h \<ge> 0\<close> apply(subst dinv, clarsimp, simp only: ffb_kcomp)
   apply(rule_tac b="fb\<^sub>\<F> (x\<acute>=(K g) & (\<lambda> s. s$(\<restriction>\<^sub>V ''x'') \<ge> 0)) {s. 0 \<le> s$(\<restriction>\<^sub>V ''x'') \<and> I s}" in order.trans)
  apply(simp add: ffb_g_orbital_guard)
    apply(rule_tac b="{s. I s}" in order.trans, force)
  unfolding ffb_diff_inv apply(simp_all add: dinv)
  using energy_conservation_invariant apply force
   apply(rule ffb_iso)
  using assms unfolding dinv ffb_if_then_else
  by (auto simp: bb_real_arith to_var_inject)

no_notation constant_acceleration_kinematics ("K")

no_notation constant_acceleration_kinematics_flow ("\<phi>\<^sub>K")


subsubsection\<open> Circular Motion \<close>


abbreviation circular_motion_kinematics :: "real^program_vars \<Rightarrow> real^program_vars" 
  where "circular_motion_kinematics s \<equiv> (\<chi> i. if i=(\<restriction>\<^sub>V''x'') then -s$(\<restriction>\<^sub>V''v'') else s$(\<restriction>\<^sub>V''x''))"

notation circular_motion_kinematics ("C")

lemma circle_invariant: 
  "diff_invariant (\<lambda>s. (r::real)\<^sup>2 = (s$(\<restriction>\<^sub>V''x''))\<^sup>2 + (s$(\<restriction>\<^sub>V''v''))\<^sup>2) C UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="\<restriction>\<^sub>V''x''" in has_vderiv_on_vec_nth, drule_tac i="\<restriction>\<^sub>V''v''" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives simp: to_var_inject)

abbreviation "circular_motion_flow t s \<equiv> 
  (\<chi> i. if i=\<restriction>\<^sub>V''x'' then s$(\<restriction>\<^sub>V''x'') \<cdot> cos t - s$(\<restriction>\<^sub>V''v'') \<cdot> sin t 
  else s$(\<restriction>\<^sub>V''x'') \<cdot> sin t + s$(\<restriction>\<^sub>V''v'') \<cdot> cos t)"

notation circular_motion_flow ("\<phi>\<^sub>C")

lemma picard_lindeloef_circ_motion: "picard_lindeloef (\<lambda>t. C) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def program_vars_univD to_var_inject power2_commute)

lemma local_flow_circ_motion: "local_flow C UNIV UNIV \<phi>\<^sub>C"
  unfolding local_flow_def local_flow_axioms_def apply safe
  apply(rule picard_lindeloef_circ_motion, simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = \<restriction>\<^sub>V''x''", simp)
    apply(force intro!: poly_derivatives derivative_intros simp: to_var_inject)
  apply(force intro!: poly_derivatives derivative_intros simp: to_var_inject)
  using program_vars_exhaust by force

lemma circular_motion:
  "{s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''v'')\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>=C & G) {s. r\<^sup>2 = (s$\<restriction>\<^sub>V''x'')\<^sup>2 + (s$\<restriction>\<^sub>V''v'')\<^sup>2}"
  by (subst local_flow.ffb_g_orbit[OF local_flow_circ_motion]) (auto simp: to_var_inject)

no_notation to_var ("\<restriction>\<^sub>V")

no_notation circular_motion_kinematics ("C")

no_notation circular_motion_flow ("\<phi>\<^sub>C")


end