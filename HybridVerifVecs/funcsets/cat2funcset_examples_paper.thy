theory cat2funcset_examples_paper
  imports "../hs_prelims_matrices" cat2funcset

begin


subsection\<open> Examples \<close>

text\<open> Preliminary preparation for the examples.\<close>

\<comment> \<open>Alternative to the finite set of program variables.\<close>

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

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=0 then s$1 else -s $ 0)"

lemma circular_motion_invariant: 
  "diff_invariant (\<lambda>s. (r::real)\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) fpend UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="0" in has_vderiv_on_vec_nth, drule_tac i="1" in has_vderiv_on_vec_nth)
  by (auto intro!: poly_derivatives)

lemma circular_motion_invariants:
  "{s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>=f & G) {s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2}"
  unfolding ffb_diff_inv using circular_motion_invariant by simp

\<comment> \<open>Verified with the flow. \<close>

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 0 then s $ 0 \<cdot> cos t + s $ 1 \<cdot> sin t 
  else - s $ 0 \<cdot> sin t + s $ 1 \<cdot> cos t)"

lemma picard_lindeloef_circ_motion: "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by (simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)

lemma local_flow_circ_motion: "local_flow f UNIV UNIV \<phi>"
  unfolding local_flow_def local_flow_axioms_def apply safe
  apply(rule picard_lindeloef_circ_motion, simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = 0", simp)
    apply(force intro!: poly_derivatives derivative_intros)
   apply(force intro!: poly_derivatives derivative_intros)
  using exhaust_2 two_eq_zero by force

lemma circular_motion:
  "{s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2} \<le> fb\<^sub>\<F> (x\<acute>=f & G) {s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2}"
  by (subst local_flow.ffb_g_orbit[OF local_flow_circ_motion]) auto

no_notation fpend ("f")

no_notation pend_flow ("\<phi>")


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

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f") 
  where "f g s \<equiv> (\<chi> i. if i=(0) then s $ 1 else g)"

lemma energy_conservation_invariant: 
  fixes g h :: real
  defines dinv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s $ 0 - 2 \<cdot> g \<cdot> h - (s $ 1 \<cdot> s $ 1) = 0)"
  shows "diff_invariant I (f g) UNIV UNIV 0 G"
  unfolding dinv apply(rule diff_invariant_rules, simp, simp, clarify)
  apply(frule_tac i="1" in has_vderiv_on_vec_nth)
  apply(drule_tac i="0" in has_vderiv_on_vec_nth)
  by(auto intro!: poly_derivatives)

lemma bouncing_ball_invariants:
  fixes h::real 
  assumes "g < 0" and "h \<ge> 0"
  defines diff_inv: "I \<equiv> (\<lambda>s::real^2. 2 \<cdot> g \<cdot> s $ 0 - 2 \<cdot> g \<cdot> h - s $ 1 \<cdot> s $ 1 = 0)"
  shows "{s. s $ 0 = h \<and> s $ 1 = 0} \<le> fb\<^sub>\<F> 
  (loop ((x\<acute>=(f g) & (\<lambda> s. s $ 0 \<ge> 0)) ; 
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE \<eta>)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. 0 \<le> s $ 0 \<and> I s}"])
  using \<open>h \<ge> 0\<close> apply(subst diff_inv, clarsimp, simp only: ffb_kcomp)
   apply(rule_tac b="fb\<^sub>\<F> (x\<acute>=(f g) & (\<lambda> s. s $ 0 \<ge> 0)) {s. 0 \<le> s $ 0 \<and> I s}" in order.trans)
  apply(simp add: ffb_g_orbital_guard)
    apply(rule_tac b="{s. I s}" in order.trans, force)
  unfolding ffb_diff_inv apply(simp_all add: diff_inv)
  using energy_conservation_invariant apply force
   apply(rule ffb_iso)
  using assms unfolding diff_inv ffb_if_then_else
  by (auto simp: bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma picard_lindeloef_cnst_acc:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. f g) UNIV UNIV 0"
  apply(unfold_locales)
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g t s \<equiv> (\<chi> i. if i=0 then g \<cdot> t ^ 2/2 + s $ 1 \<cdot> t + s $ 0 else g \<cdot> t + s $ 1)"

lemma local_flow_cnst_acc: "local_flow (f g) UNIV UNIV (\<phi> g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_cnst_acc apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = 0")
  using exhaust_2 two_eq_zero by (auto intro!: poly_derivatives simp: vec_eq_iff) force

lemma [bb_real_arith]:
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
    and pos: "g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real) = 0"
  shows "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
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
  defines loop_inv: "I \<equiv> (\<lambda>s::real^2. 0 \<le> s $ 0 \<and> 2 \<cdot> g \<cdot> s $ 0 = 2 \<cdot> g \<cdot> h + (s $ 1 \<cdot> s $ 1))"
  shows "{s. s $ 0 = h \<and> s $ 1 = 0} \<le> fb\<^sub>\<F> 
  (loop ((x\<acute>=(f g) & (\<lambda> s. s $ 0 \<ge> 0)) ; 
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE \<eta>)))
  {s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h}"
  apply(rule ffb_kstarI[of _ "{s. I s}"])
  unfolding loop_inv using \<open>h \<ge> 0\<close> apply(clarsimp, simp only: ffb_kcomp)
   apply(subst local_flow.ffb_g_orbit[OF local_flow_cnst_acc], simp)
  unfolding ffb_if_then_else using assms by (auto simp: bb_real_arith)

no_notation fpend ("f")

no_notation pend_flow ("\<phi>")

end