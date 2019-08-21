theory kat2rel_examples
  imports "../hs_prelims_matrices" kat2rel

begin


subsection\<open> Examples \<close>

text\<open> Preliminary preparation for the examples.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")

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


subsubsection\<open>Pendulum\<close>

\<comment> \<open>Verified with differential invariants. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=0 then s$1 else -s $ 0)"

lemma pendulum_invariant: 
  "diff_invariant (\<lambda>s. (r::real)\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2) fpend UNIV UNIV 0 G"
  apply(rule_tac diff_invariant_rules, clarsimp, simp, clarsimp)
  apply(frule_tac i="0" in has_vderiv_on_vec_nth, drule_tac i="1" in has_vderiv_on_vec_nth)
  by (auto intro!: poly_derivatives)

lemma pendulum_invariants: "rel_kat.H 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  unfolding sH_diff_inv using pendulum_invariant by auto

\<comment> \<open>Verified with the flow. \<close>

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> \<tau> s \<equiv> (\<chi> i. if i = 0 then s $ 0 \<cdot> cos \<tau> + s $ 1 \<cdot> sin \<tau> 
  else - s $ 0 \<cdot> sin \<tau> + s $ 1 \<cdot> cos \<tau>)"

lemma picard_lindeloef_pend: "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
  by (simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  unfolding local_flow_def local_flow_axioms_def apply safe
  apply(rule picard_lindeloef_pend, simp_all add: vec_eq_iff)
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = 0", simp)
    apply(force intro!: poly_derivatives derivative_intros)
   apply(force intro!: poly_derivatives derivative_intros)
  using exhaust_2 two_eq_zero by force

lemma pendulum: "rel_kat.H 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  by (rule local_flow.sH_g_orbit[OF local_flow_pend]) auto

\<comment> \<open>Verified as a linear system (using uniqueness). \<close>

abbreviation pend_sq_mtx :: "2 sq_mtx" ("A")
  where "A \<equiv> sq_mtx_chi (\<chi> i. if i=0 then \<e> 1 else - \<e> 0)"

lemma pend_sq_mtx_exp_eq_flow: "exp (\<tau> *\<^sub>R A) *\<^sub>V s = \<phi> \<tau> s"
  apply(rule local_flow.eq_solution[OF local_flow_exp, symmetric])
    apply(rule ivp_solsI, rule has_vderiv_on_vec_lambda, clarsimp)
  unfolding sq_mtx_vec_prod_def matrix_vector_mult_def apply simp
      apply(force intro!: poly_derivatives simp: matrix_vector_mult_def)
  using exhaust_2 two_eq_zero by (force simp: vec_eq_iff, auto)

lemma pendulum_sq_mtx: "rel_kat.H 
  \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil> (x\<acute>= ((*\<^sub>V) A) & G) \<lceil>\<lambda>s. r\<^sup>2 = (s $ 0)\<^sup>2 + (s $ 1)\<^sup>2\<rceil>"
  apply(rule local_flow.sH_g_orbit[OF local_flow_exp])
  unfolding pend_sq_mtx_exp_eq_flow by auto

no_notation fpend ("f")
        and pend_sq_mtx ("A")
        and pend_flow ("\<phi>")


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
  where "f g s \<equiv> (\<chi> i. if i=0 then s $ 1 else g)"

lemma fball_invariant: 
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
  shows "rel_kat.H  
  \<lceil>\<lambda>s. s $ 0 = h \<and> s $ 1 = 0\<rceil> 
  (loop ((x\<acute>=f g & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN ((1) ::= (\<lambda>s. - s $ 1)) ELSE skip)))
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule sH_loop[of _ "\<lambda>s. 0\<le>s $ 0 \<and> I s"])
  using \<open>h \<ge> 0\<close> apply(simp add: diff_inv)
  using \<open>g < 0\<close> apply(simp add: diff_inv, force simp: bb_real_arith)
   apply(rule sH_relcomp[where R="\<lambda>s. 0\<le>s $ 0 \<and> I s"])
    apply(rule sH_g_evolution_guard, simp)
    apply(rule_tac p'="\<lceil>I\<rceil>" in rel_kat.H_cons_1, simp)
    apply(unfold diff_inv, subst sH_diff_inv)
  using fball_invariant apply force
   apply(rule sH_cond, subst sH_assign_iff, force simp: bb_real_arith)
  using assms by (simp add: sH_H) 

\<comment> \<open>Verified with the flow. \<close>

lemma picard_lindeloef_fball:
  fixes g::real
  shows "picard_lindeloef (\<lambda>t. f g) UNIV UNIV 0"
  apply(unfold_locales)
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  by(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g \<tau> s \<equiv> (\<chi> i. if i=0 then g \<cdot> \<tau> ^ 2/2 + s $ 1 \<cdot> \<tau> + s $ 0 else g \<cdot> \<tau> + s $ 1)"

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  unfolding local_flow_def local_flow_axioms_def apply safe
  using picard_lindeloef_fball apply blast
   apply(rule has_vderiv_on_vec_lambda, clarify)
   apply(case_tac "i = 0")
  using exhaust_2 two_eq_zero by (auto intro!: poly_derivatives simp: vec_eq_iff) force

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
  defines loop_inv: "I \<equiv> (\<lambda>s::real^2. 0 \<le> s $ 0 \<and> 2 \<cdot> g \<cdot> s $ 0 = 2 \<cdot> g \<cdot> h + s $ 1 \<cdot> s $ 1)"
  shows "rel_kat.H  
  \<lceil>\<lambda>s. s $ 0 = h \<and> s $ 1 = 0\<rceil> 
  (loop ((x\<acute>=f g & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN ((1) ::= (\<lambda>s. - s $ 1)) ELSE skip)))
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule sH_loop[of _ "I"])
  using \<open>h \<ge> 0\<close> apply(simp add: loop_inv)
  using \<open>g < 0\<close> apply(simp add: loop_inv, force simp: bb_real_arith)
   apply(rule sH_relcomp[where R="I"])
    apply(rule local_flow.sH_g_orbit[OF local_flow_ball])
    apply(simp add: loop_inv)
    apply(force simp: bb_real_arith)
   apply(rule sH_cond, subst sH_assign_iff)
  using assms by(auto simp: sH_H bb_real_arith)

\<comment> \<open>Verified as a linear system (computing exponential). \<close>

abbreviation ball_sq_mtx :: "3 sq_mtx" ("A")
  where "ball_sq_mtx \<equiv> sq_mtx_chi (\<chi> i. if i=0 then \<e> 1 else if i=1 then \<e> 2 else 0)"

lemma ball_sq_mtx_pow2: "A\<^sup>2 = sq_mtx_chi (\<chi> i. if i=0 then \<e> 2 else 0)"
  unfolding monoid_mult_class.power2_eq_square times_sq_mtx_def
  by (simp add: sq_mtx_chi_inject vec_eq_iff matrix_matrix_mult_def)

lemma ball_sq_mtx_powN: "m > 2 \<Longrightarrow> (\<tau> *\<^sub>R A)^m = 0"
  apply(induct m, simp, case_tac "m \<le> 2")
   apply(simp only: le_less_Suc_eq power_class.power.simps(2), simp)
  by (auto simp: ball_sq_mtx_pow2 sq_mtx_chi_inject vec_eq_iff 
      times_sq_mtx_def zero_sq_mtx_def matrix_matrix_mult_def)

lemma exp_ball_sq_mtx: "exp (\<tau> *\<^sub>R A) = ((\<tau> *\<^sub>R A)\<^sup>2/\<^sub>R 2) + (\<tau> *\<^sub>R A) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using ball_sq_mtx_powN by (simp_all add: numeral_2_eq_2)
 
lemma exp_ball_sq_mtx_simps:
  "exp (\<tau> *\<^sub>R A) $$ 0 $ 0 = 1" "exp (\<tau> *\<^sub>R A) $$ 0 $ 1 = \<tau>" "exp (\<tau> *\<^sub>R A) $$ 0 $ 2 = \<tau>^2/2"
  "exp (\<tau> *\<^sub>R A) $$ 1 $ 0 = 0" "exp (\<tau> *\<^sub>R A) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R A) $$ 1 $ 2 = \<tau>"
  "exp (\<tau> *\<^sub>R A) $$ 2 $ 0 = 0" "exp (\<tau> *\<^sub>R A) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R A) $$ 2 $ 2 = 1"
  unfolding exp_ball_sq_mtx scaleR_power ball_sq_mtx_pow2
  by (auto simp: plus_sq_mtx_def scaleR_sq_mtx_def one_sq_mtx_def 
      mat_def scaleR_vec_def axis_def plus_vec_def)

lemma bouncing_ball_K: "rel_kat.H 
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 = h \<and> s $ 1 = 0 \<and> 0 > s $ 2\<rceil>
  (loop ((x\<acute>=(*\<^sub>V) A & (\<lambda> s. s $ 0 \<ge> 0));
  (IF (\<lambda> s. s $ 0 = 0) THEN (1 ::= (\<lambda>s. - s $ 1)) ELSE skip)))
  \<lceil>\<lambda>s. 0 \<le> s $ 0 \<and> s $ 0 \<le> h\<rceil>"
  apply(rule sH_loop[of _ "\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"])
  apply(simp, simp, force simp: bb_real_arith)
   apply(rule sH_relcomp[where R="\<lambda>s. 0 \<le> s$0 \<and> 0 > s$2 \<and>  2 \<cdot> s$2 \<cdot> s$0 = 2 \<cdot> s$2 \<cdot> h + (s$1 \<cdot> s$1)"])
    apply(subst local_flow.sH_g_orbit[OF local_flow_exp], simp_all add: sq_mtx_vec_prod_eq)
  unfolding UNIV_3 image_le_pred 
    apply(simp add: exp_ball_sq_mtx_simps field_simps monoid_mult_class.power2_eq_square)
  by (auto simp: bb_real_arith sH_H)

no_notation fpend ("f")
        and pend_flow ("\<phi>")
        and ball_sq_mtx ("A")

end