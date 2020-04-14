(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory hs_vc_examples
  imports hs_vc_spartan mtx_flows

begin


subsubsection \<open>Pendulum\<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of 
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i = 1 then s$2 else -s$1)"

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 1 then s$1 * cos t + s$2 * sin t else - s$1 * sin t + s$2 * cos t)"

\<comment> \<open>Verified with annotated dynamics. \<close>

lemma pendulum_dyn: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |EVOL \<phi> G T] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by force

\<comment> \<open>Verified with differential invariants. \<close>

lemma pendulum_inv: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |x\<acute>= f & G] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by (auto intro!: diff_invariant_rules poly_derivatives)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma pendulum_flow: "(\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2) \<le> |x\<acute>=f & G] (\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2)"
  by (force simp: local_flow.fbox_g_ode[OF local_flow_pend])

\<comment> \<open>Verified as a linear system with the flow. \<close>

abbreviation mtx_pend :: "2 sq_mtx" ("A")
  where "A \<equiv> mtx  
   ([0,  1] # 
    [-1, 0] # [])"

lemma mtx_circ_flow_eq: "exp (t *\<^sub>R A) *\<^sub>V s = \<phi> t s"
  apply(rule local_flow.eq_solution[OF local_flow_sq_mtx_linear, symmetric])
    apply(rule ivp_solsI, simp_all add: sq_mtx_vec_mult_eq vec_eq_iff)
  unfolding UNIV_2 using exhaust_2
  by (force intro!: poly_derivatives simp: matrix_vector_mult_def)+

lemma pendulum_linear: "(\<lambda>s. r\<^sup>2 = (s $ 1)\<^sup>2 + (s $ 2)\<^sup>2) \<le> |x\<acute>=(*\<^sub>V) A & G] (\<lambda>s. r\<^sup>2 = (s $ 1)\<^sup>2 + (s $ 2)\<^sup>2)"
  unfolding mtx_circ_flow_eq local_flow.fbox_g_ode[OF local_flow_sq_mtx_linear] by auto

no_notation fpend ("f")
        and pend_flow ("\<phi>")
        and mtx_pend ("A")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with 
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the 
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that 
flips the velocity, thus it is a completely elastic collision with the ground. We use @{text "s$1"} 
to ball's height and @{text "s$2"} for its velocity. We prove that the ball remains above ground
and below its initial resting position. \<close>

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f") 
  where "f g s \<equiv> (\<chi> i. if i = 1 then s$2 else g)"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g t s \<equiv> (\<chi> i. if i = 1 then g * t ^ 2/2 + s$2 * t + s$1 else g * t + s$2)"

\<comment> \<open>Verified with differential invariants. \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma inv_imp_pos_le[bb_real_arith]: 
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

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (x\<acute>=(f g) & (\<lambda> s. s$1 \<ge> 0) DINV (\<lambda>s. 2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)) ; 
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 - 2 * g * h - s$2 * s$2 = 0)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  apply(rule fbox_loopI, simp_all, force, force simp: bb_real_arith)
  by (rule fbox_g_odei) (auto intro!: poly_derivatives diff_invariant_rules)

\<comment> \<open>Verified with annotated dynamics. \<close>

lemma inv_conserv_at_ground[bb_real_arith]:
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

lemma inv_conserv_at_air[bb_real_arith]:
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

lemma bouncing_ball_dyn: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (EVOL (\<phi> g) (\<lambda> s. s$1 \<ge> 0) T) ; 
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 = 2 * g * h + s$2 * s$2)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  by (rule fbox_loopI) (auto simp: bb_real_arith)

\<comment> \<open>Verified with the flow. \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  (\<lambda>s. s$1 = h \<and> s$2 = 0) \<le>
  |LOOP (
    (x\<acute>=(f g) & (\<lambda> s. s$1 \<ge> 0)) ; 
    (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0 \<le> s$1 \<and>2 * g * s$1 = 2 * g * h + s$2 * s$2)]
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  by (rule fbox_loopI) (auto simp: bb_real_arith local_flow.fbox_g_ode[OF local_flow_ball])

\<comment> \<open>Verified as a  non-diagonalizable linear system. \<close>

abbreviation mtx_ball :: "3 sq_mtx" ("A")
  where "A \<equiv> mtx (
  [0,1,0] #
  [0,0,1] # 
  [0,0,0] # [])"

lemma pow2_scaleR_mtx_ball: "(t *\<^sub>R A)\<^sup>2 = mtx (
  [0,0,t\<^sup>2] #
  [0,0,0] # 
  [0,0,0] # [])"
  unfolding power2_eq_square apply(subst sq_mtx_eq_iff)
  unfolding sq_mtx_times_eq UNIV_3 by auto

lemma powN_scaleR_mtx_ball: "n > 2 \<Longrightarrow> (t *\<^sub>R A)^n = 0"
  apply(induct n, simp, case_tac "n \<le> 2")
   apply(subgoal_tac "n = 2", erule ssubst)
  unfolding power_Suc2 pow2_scaleR_mtx_ball sq_mtx_times_eq UNIV_3
  by (auto simp: sq_mtx_eq_iff)

lemma exp_mtx_ball: "exp (t *\<^sub>R A) = ((t *\<^sub>R A)\<^sup>2/\<^sub>R 2) + (t *\<^sub>R A) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using powN_scaleR_mtx_ball by (simp_all add: numeral_2_eq_2)

lemma exp_mtx_ball_vec_mult_eq: "exp (t *\<^sub>R A) *\<^sub>V s = 
  vector [s$3 * t^2/2 + s$2 * t + s$1, s$3 * t + s$2, s$3]"
  apply(simp add: sq_mtx_vec_mult_eq vector_def)
  unfolding UNIV_3 exp_mtx_ball pow2_scaleR_mtx_ball
  using exhaust_3 by (auto simp: one_mtx3 fun_eq_iff)

lemma bouncing_ball_sq_mtx: 
  "(\<lambda>s. 0 \<le> s$1 \<and> s$1 = h \<and> s$2 = 0 \<and> 0 > s$3) \<le> fbox 
  (LOOP ((x\<acute>=(*\<^sub>V) A & (\<lambda> s. s$1 \<ge> 0)) ;
  (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
  INV (\<lambda>s. 0\<le>s$1 \<and> s$3<0 \<and> 2 * s$3 * s$1 = 2 * s$3 * h + (s$2 * s$2)))
  (\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h)"
  apply(rule fbox_loopI, force, force simp: bb_real_arith)
  apply(simp add: local_flow.fbox_g_ode[OF local_flow_sq_mtx_linear])
  unfolding exp_mtx_ball_vec_mult_eq using bb_real_arith by force

lemma docking_station_arith:
  assumes "(d::real) > x" and "v > 0"
  shows "(v = v\<^sup>2 * t / (2 * d - 2 * x)) \<longleftrightarrow> (v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d)"
proof
  assume "v = v\<^sup>2 * t / (2 * d - 2 * x)"
  hence "v * t = 2 * (d - x)"
    using assms by (simp add: eq_divide_eq power2_eq_square) 
  hence "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = 2 * (d - x) - 4 * (d - x)\<^sup>2 / (4 * (d - x)) + x"
    apply(subst power_mult_distrib[symmetric])
    by (erule ssubst, subst power_mult_distrib, simp)
  also have "... = d"
    apply(simp only: mult_divide_mult_cancel_left_if)
    using assms by (auto simp: power2_eq_square)
  finally show "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d" .
next
  assume "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d"
  hence "0 = v\<^sup>2 * t\<^sup>2 / (4 * (d - x)) + (d - x) - v * t"
    by auto
  hence "0 = (4 * (d - x)) * (v\<^sup>2 * t\<^sup>2 / (4 * (d - x)) + (d - x) - v * t)"
    by auto
  also have "... = v\<^sup>2 * t\<^sup>2 + 4 * (d - x)\<^sup>2  - (4 * (d - x)) * (v * t)"
    using assms apply(simp add: distrib_left right_diff_distrib)
    apply(subst right_diff_distrib[symmetric])+
    by (simp add: power2_eq_square)
  also have "... = (v * t - 2 * (d - x))\<^sup>2"
    by (simp only: power2_diff, auto simp: field_simps power2_diff)
  finally have "0 = (v * t - 2 * (d - x))\<^sup>2" .
  hence "v * t = 2 * (d - x)"
    by auto
  thus "v = v\<^sup>2 * t / (2 * d - 2 * x)"
    apply(subst power2_eq_square, subst mult.assoc)
    apply(erule ssubst, subst right_diff_distrib[symmetric])
    using assms by auto
qed

subsubsection \<open> Docking station \<close>

text \<open> For a more realistic example of a hybrid system with this vector field, consider a spaceship
at initial position @{term x\<^sub>0} that is approaching a station @{term d} at constant velocity 
@{term "v\<^sub>0 > 0"}. The ship calculates that it needs to deccelerate at @{term "a = -(v\<^sub>0^2/(2*(d-x\<^sub>0)))"} 
in order to anchor itself to the station. As before, we use @{text "s$1"} for the ship's position, 
@{text "s$2"} for its velocity, and @{text "s$3"} for its acceleration to prove that it will stop 
moving @{term "s$2=0"} if and only if its in anchoring position @{term "s$1=d"}.\<close>

\<comment> \<open>Verified as a  non-diagonalizable linear system. \<close>

lemma docking_station:
  assumes "d > x\<^sub>0" and "v\<^sub>0 > 0"
  shows "(\<lambda>s. s$1 = x\<^sub>0 \<and> s$2 = v\<^sub>0) \<le> 
  |(3 ::= (\<lambda>s. -(v\<^sub>0^2/(2*(d-x\<^sub>0))))); x\<acute>=(*\<^sub>V) A & G] 
  (\<lambda>s. s$2 = 0 \<longleftrightarrow> s$1 = d)"
  apply(clarsimp simp: le_fun_def local_flow.fbox_g_ode[OF local_flow_sq_mtx_linear[of A]])
  unfolding exp_mtx_ball_vec_mult_eq using assms by (simp add: docking_station_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")
        and mtx_ball ("A")


subsubsection \<open> Door mechanism  \<close>

\<comment> \<open>Verified as a diagonalizable linear system. \<close>

abbreviation mtx_door :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" ("A")
  where "A a b \<equiv> mtx  
   ([0, 1] # 
    [a, b] # [])"

abbreviation mtx_chB_door :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" ("P")
  where "P a b \<equiv> mtx
   ([a, b] # 
    [1, 1] # [])"

lemma inv_mtx_chB_door: 
  "a \<noteq> b \<Longrightarrow> (P a b)\<^sup>-\<^sup>1 = (1/(a - b)) *\<^sub>R mtx 
   ([ 1, -b] # 
    [-1,  a] # [])"
  apply(rule sq_mtx_inv_unique, unfold scaleR_mtx2 times_mtx2)
  by (simp add: diff_divide_distrib[symmetric] one_mtx2)+

lemma invertible_mtx_chB_door: "a \<noteq> b \<Longrightarrow> mtx_invertible (P a b)"
  apply(rule mtx_invertibleI[of _ "(P a b)\<^sup>-\<^sup>1"])
   apply(unfold inv_mtx_chB_door scaleR_mtx2 times_mtx2 one_mtx2)
  by (subst sq_mtx_eq_iff, simp add: vector_def frac_diff_eq1)+

lemma mtx_door_diagonalizable:
  fixes a b :: real
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b^2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b^2+4*a))/2"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "A a b = P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. if i = 1 then \<iota>\<^sub>1 else \<iota>\<^sub>2) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1"
  unfolding assms apply(subst inv_mtx_chB_door)
  using assms(3,4) apply(simp_all add: diag2_eq[symmetric])
  unfolding sq_mtx_times_eq sq_mtx_scaleR_eq UNIV_2 apply(subst sq_mtx_eq_iff)
  using exhaust_2 assms by (auto simp: field_simps, auto simp: field_power_simps)

lemma mtx_door_solution_eq:
  fixes a b :: real
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b\<^sup>2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b\<^sup>2+4*a))/2"
  defines "\<Phi> t \<equiv> mtx (
   [\<iota>\<^sub>2*exp(t*\<iota>\<^sub>1) - \<iota>\<^sub>1*exp(t*\<iota>\<^sub>2),     exp(t*\<iota>\<^sub>2)-exp(t*\<iota>\<^sub>1)]#
   [a*exp(t*\<iota>\<^sub>2) - a*exp(t*\<iota>\<^sub>1), \<iota>\<^sub>2*exp(t*\<iota>\<^sub>2)-\<iota>\<^sub>1*exp(t*\<iota>\<^sub>1)]#[])"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. exp (t * (if i=1 then \<iota>\<^sub>1 else \<iota>\<^sub>2))) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1 
  = (1/sqrt (b\<^sup>2 + a * 4)) *\<^sub>R (\<Phi> t)"
  unfolding assms apply(subst inv_mtx_chB_door)
  using assms apply(simp_all add: mtx_times_scaleR_commute, subst sq_mtx_eq_iff)
  unfolding UNIV_2 sq_mtx_times_eq sq_mtx_scaleR_eq sq_mtx_uminus_eq apply(simp_all add: axis_def)
  by (auto simp: field_simps, auto simp: field_power_simps)+
 
lemma local_flow_mtx_door:
  fixes a b
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b^2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b^2+4*a))/2"
  defines "\<Phi> t \<equiv> mtx (
   [\<iota>\<^sub>2*exp(t*\<iota>\<^sub>1) - \<iota>\<^sub>1*exp(t*\<iota>\<^sub>2),     exp(t*\<iota>\<^sub>2)-exp(t*\<iota>\<^sub>1)]#
   [a*exp(t*\<iota>\<^sub>2) - a*exp(t*\<iota>\<^sub>1), \<iota>\<^sub>2*exp(t*\<iota>\<^sub>2)-\<iota>\<^sub>1*exp(t*\<iota>\<^sub>1)]#[])"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "local_flow ((*\<^sub>V) (A a b)) UNIV UNIV (\<lambda>t. (*\<^sub>V) ((1/sqrt (b\<^sup>2 + a * 4)) *\<^sub>R \<Phi> t))"
  unfolding assms using local_flow_sq_mtx_linear[of "A a b"] assms
  apply(subst (asm) exp_scaleR_diagonal2[OF invertible_mtx_chB_door mtx_door_diagonalizable])
     apply(simp, simp, simp)
  by (subst (asm) mtx_door_solution_eq) simp_all

lemma overdamped_door_arith:
  assumes "b\<^sup>2 + a * 4 > 0" and "a < 0" and "b \<le> 0" and "t \<ge> 0" and "s1 > 0"
  shows "0 \<le> ((b + sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b - sqrt (b\<^sup>2 + 4 * a)) / 2) / 2 - 
(b - sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b + sqrt (b\<^sup>2 + 4 * a)) / 2) / 2) * s1 / sqrt (b\<^sup>2 + a * 4)"
proof(subst diff_divide_distrib[symmetric], simp)
  have f0: "s1 / (2 * sqrt (b\<^sup>2 + a * 4)) > 0"  (is "s1/?c3 > 0")
    using assms(1,5) by simp
  have f1: "(b - sqrt (b\<^sup>2 + 4 * a)) < (b + sqrt (b\<^sup>2 + 4 * a))" (is "?c2 < ?c1") 
    and f2: "(b + sqrt (b\<^sup>2 + 4 * a)) < 0"
    by (smt assms sqrt_ge_absD real_sqrt_gt_zero)+
  hence f3: "exp (t * ?c2 / 2) \<le> exp (t * ?c1 / 2)" (is "exp ?t1 \<le> exp ?t2")
    using assms(4) by (smt arith_geo_mean_sqrt exp_le_cancel_iff mult_left_mono 
        real_sqrt_zero right_diff_distrib times_divide_eq_left) 
  hence "?c2 * exp ?t2 \<le> ?c2 * exp ?t1"
    using f1 f2 by (smt mult_less_cancel_left) 
  also have "... < ?c1 * exp ?t1"
    using f1 by auto
  also have"... \<le> ?c1 * exp ?t1"
    using f1 f2 by auto
  ultimately show "0 \<le> (?c1 * exp ?t1 - ?c2 * exp ?t2) * s1 / ?c3"
    using f0 f1 assms(5) by auto
qed

lemma overdamped_door:
  assumes "b\<^sup>2 + a * 4 > 0" and "a < 0" and "b \<le> 0" and "0 \<le> t"
  shows "(\<lambda>s. s$1 = 0) \<le>
  |LOOP 
     (\<lambda>s. {s. s$1 > 0 \<and> s$2 = 0});
     (x\<acute>=(*\<^sub>V) (A a b) & G on {0..t} UNIV @ 0) 
   INV (\<lambda>s. 0 \<le> s$1)]
  (\<lambda>s. 0 \<le> s $ 1)"
  apply(rule fbox_loopI, simp_all add: le_fun_def)
  apply(subst local_flow.fbox_g_ode_ivl[OF local_flow_mtx_door[OF assms(1)]])
  using assms apply(simp_all add: le_fun_def fbox_def)
  unfolding sq_mtx_scaleR_eq UNIV_2 sq_mtx_vec_mult_eq
  by (clarsimp simp: overdamped_door_arith)


no_notation mtx_door ("A")
        and mtx_chB_door ("P")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater 
is on, and @{text "0"} when it is off. We use @{term "1::4"} to denote the room's temperature, 
@{term "2::4"} is time as measured by the thermostat's chronometer, @{term "3::4"} is the 
temperature detected by the thermometer, and @{term "4::4"} states whether the heater is on 
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the thermostat keeps the room's 
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L t s \<equiv> (\<chi> i. if i = 1 then - exp(-a * t) * (L - s$1) + L else 
  (if i = 2 then t + s$2 else s$i))"

\<comment> \<open>Verified with the flow. \<close>

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$1 + - L) + - (a * (s\<^sub>2$1 + - L))\<bar> = a * \<bar>s\<^sub>1$1 + - s\<^sub>2$1\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$1 - L) - a * (s\<^sub>1$1 - L)\<bar> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_temp_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms
  apply(simp add: norm_diff_temp_dyn)
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: poly_derivatives local_lipschitz_temp_dyn simp: forall_4 vec_eq_iff)

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

lemmas fbox_temp_dyn = local_flow.fbox_g_ode_ivl[OF local_flow_temp _ UNIV_I]

lemma thermostat: 
  assumes "a > 0" and "0 \<le> t" and "0 < Tmin" and "Tmax < L"
  shows "(\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$4 = 0) \<le> 
  |LOOP 
    \<comment> \<open>control\<close>
    ((2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..t} UNIV @ 0) 
    ELSE (x\<acute>=(f a L) & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a) on {0..t} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1))]
  (\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax)"
  apply(rule fbox_loopI, simp_all add: fbox_temp_dyn[OF assms(1,2)] le_fun_def)
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")


subsubsection\<open> Tank \<close>

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
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")
        and tank_guard ("G")

end