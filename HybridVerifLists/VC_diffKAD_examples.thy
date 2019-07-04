theory VC_diffKAD_examples
imports "VC_diffKAD"

begin

subsection\<open> Rules Testing \<close>
text\<open> In this section we test the recently developed rules with simple dynamical systems. \<close>

\<comment> \<open>Example of hybrid program verified with the rule dSolve and a single differential equation: $x'=v$.\<close>
lemma motion_with_constant_velocity:
      "PRE (\<lambda> s. s ''y'' < s ''x''  \<and> s ''v'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''y'' < s ''x''))"
apply(rule_tac uInput="[\<lambda> t s. s ''v'' \<cdot> t + s ''x'']" in dSolve_toSolveUBC)
prefer 9 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
apply(simp_all add: vdiff_def varDiffs_def)
prefer 2 apply(simp add: solvesStoreIVP_def vdiff_def varDiffs_def)
apply(clarify, rule_tac f'1="\<lambda> x. s ''v''" and g'1="\<lambda> x. 0" in derivative_intros(191))
apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(194))
by(auto intro: derivative_intros)

text\<open>Same hybrid program verified with dSolve and the system of ODEs: $x'=v, v'= a$. The uniqueness
part of the proof requires a preliminary lemma.\<close>
lemma flow_vel_is_galilean_vel:
assumes solHyp:"\<phi>\<^sub>s solvesTheStoreIVP [(x, \<lambda>s. s v), (v, \<lambda>s. s a)] withInitState s"
    and tHyp:"r \<le> t" and rHyp:"0 \<le> r" and distinct:"x \<noteq> v \<and> v \<noteq> a \<and> x \<noteq> a \<and> a \<notin> varDiffs"
shows "\<phi>\<^sub>s r v = s a \<cdot> r + s v"
proof-
from assms have 1:"((\<lambda>t. \<phi>\<^sub>s t v) solves_ode (\<lambda>t r. \<phi>\<^sub>s t a)) {0..t} UNIV \<and> \<phi>\<^sub>s 0 v = s v" 
  by (simp add: solvesStoreIVP_def)
from assms have obs:"\<forall> r \<in> {0..t}. \<phi>\<^sub>s r a = s a"
  by(auto simp: solvesStoreIVP_def varDiffs_def)
have 2:"((\<lambda>t. s a \<cdot> t + s v) solves_ode (\<lambda>t r. \<phi>\<^sub>s t a)) {0..t} UNIV"
  unfolding solves_ode_def apply(subgoal_tac "((\<lambda>x. s a \<cdot> x + s v) has_vderiv_on (\<lambda>x. s a)) {0..t}")
  using obs apply (simp add: has_vderiv_on_def) by(rule galilean_transform)
have 3:"unique_on_bounded_closed 0 {0..t} (s v) (\<lambda>t r. \<phi>\<^sub>s t a) UNIV (if t = 0 then 1 else 1/(t+1))"
   apply(simp add: ubc_definitions del: comp_apply, rule conjI)
   using rHyp tHyp obs apply(simp_all del: comp_apply)
   apply(clarify, rule continuous_intros) prefer 3 apply safe
   apply(rule continuous_intros)
   apply(auto intro: continuous_intros)
   by (metis continuous_on_const continuous_on_eq)
thus "\<phi>\<^sub>s r v = s a \<cdot> r + s v"
   apply(rule_tac unique_on_bounded_closed.unique_solution[of 0 "{0..t}" "s v" 
   "(\<lambda>t r. \<phi>\<^sub>s t a)" UNIV "(if t = 0 then 1 else 1 / (t + 1))" "(\<lambda>t. \<phi>\<^sub>s t v)"])
   using rHyp tHyp 1 2 and 3 by auto
qed

lemma motion_with_constant_acceleration:
      "PRE (\<lambda> s. s ''y'' < s ''x''  \<and> s ''v'' \<ge> 0 \<and> s ''a'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v'')),(''v'',(\<lambda> s. s ''a''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''y'' < s ''x''))"
apply(rule_tac uInput="[\<lambda> t s. s ''a'' \<cdot> t ^ 2/2 + s ''v'' \<cdot> t + s ''x'', 
  \<lambda> t s. s ''a'' \<cdot> t + s ''v'']" in dSolve_toSolveUBC)
prefer 9 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
prefer 6 subgoal (* DERIVATIVES *)
    apply(simp add: vdiff_def, clarify, rule conjI)
    by(rule galilean_transform)+
prefer 6 subgoal (* CONTINUITY *)
    apply(simp add: vdiff_def, safe)
    by(rule continuous_intros)+
prefer 6 subgoal (* UNIQUENESS *)
    apply(simp add: vdiff_def, safe)
    subgoal for s "\<phi>\<^sub>s" t r apply(rule flow_vel_is_galilean_vel[of "\<phi>\<^sub>s" "''x''" _ _ _ _ t])
      by(simp_all add: varDiffs_def vdiff_def)
    apply(simp add: solvesStoreIVP_def vdiff_def varDiffs_def) done
by(auto simp: varDiffs_def vdiff_def)

text\<open> Example of a hybrid system with two modes verified with the equality dS. 
We also need to provide a previous (similar) lemma.\<close>
lemma flow_vel_is_galilean_vel2:
assumes solHyp:"\<phi>\<^sub>s solvesTheStoreIVP [(x, \<lambda>s. s v), (v, \<lambda>s. - s a)] withInitState s"
    and tHyp:"r \<le> t" and rHyp:"0 \<le> r" and distinct:"x \<noteq> v \<and> v \<noteq> a \<and> x \<noteq> a \<and> a \<notin> varDiffs"
shows "\<phi>\<^sub>s r v = s v - s a \<cdot> r"
proof-
from assms have 1:"((\<lambda>t. \<phi>\<^sub>s t v) solves_ode (\<lambda>t r. - \<phi>\<^sub>s t a)) {0..t} UNIV \<and> \<phi>\<^sub>s 0 v = s v" 
  by (simp add: solvesStoreIVP_def)
from assms have obs:"\<forall> r \<in> {0..t}. \<phi>\<^sub>s r a = s a"
  by(auto simp: solvesStoreIVP_def varDiffs_def)
have 2:"((\<lambda>t. - s a \<cdot> t + s v) solves_ode (\<lambda>t r. - \<phi>\<^sub>s t a)) {0..t} UNIV"
  unfolding solves_ode_def apply(subgoal_tac "((\<lambda>x. - s a \<cdot> x + s v) has_vderiv_on (\<lambda>x. - s a)) {0..t}")
  using obs apply (simp add: has_vderiv_on_def) by(rule galilean_transform)
have 3:"unique_on_bounded_closed 0 {0..t} (s v) (\<lambda>t r. - \<phi>\<^sub>s t a) UNIV (if t = 0 then 1 else 1/(t+1))"
   apply(simp add: ubc_definitions del: comp_apply, rule conjI)
   using rHyp tHyp obs apply(simp_all del: comp_apply)
   apply(clarify, rule continuous_intros) prefer 3 apply safe
   apply(rule continuous_intros)+
   apply(auto intro: continuous_intros)
   by (metis continuous_on_const continuous_on_eq) (* More than 8 seconds.*)
thus "\<phi>\<^sub>s r v = s v - s a \<cdot> r"
   apply(rule_tac unique_on_bounded_closed.unique_solution[of 0 "{0..t}" "s v" 
   "(\<lambda>t r. - \<phi>\<^sub>s t a)" UNIV "(if t = 0 then 1 else 1 / (t + 1))" "(\<lambda>t. \<phi>\<^sub>s t v)"])
   using rHyp tHyp 1 2 and 3 by auto
qed
  
lemma single_hop_ball:
      "PRE (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' = H \<and> s ''v'' = 0 \<and> s ''g'' > 0 \<and> 1 \<ge> c \<and> c \<ge> 0)  
      (((ODEsystem [(''x'', \<lambda> s. s ''v''),(''v'',\<lambda> s. - s ''g'')] with (\<lambda> s. 0 \<le> s ''x'')));
      (IF (\<lambda> s. s ''x'' = 0) THEN (''v'' ::= (\<lambda> s. - c \<cdot> s ''v'')) ELSE (''v'' ::= (\<lambda> s. s ''v'')) FI))
      POST (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' \<le> H)"
      apply(simp, subst dS[of "[\<lambda> t s. - s ''g'' \<cdot> t ^ 2/2 + s ''v'' \<cdot> t + s ''x'', \<lambda> t s. - s ''g'' \<cdot> t + s ''v'']"])
      \<comment> \<open>Given solution is actually a solution.\<close>
      apply(simp add: vdiff_def varDiffs_def solvesStoreIVP_def solves_ode_def has_vderiv_on_singleton, safe)
      apply(rule galilean_transform_eq, simp)+
      apply(rule galilean_transform)+
      \<comment> \<open>Uniqueness of the flow.\<close>
      apply(rule ubcStoreUniqueSol, simp)
      apply(simp add: vdiff_def del: comp_apply)
      apply(auto intro: continuous_intros del: comp_apply)[1]
      apply(rule continuous_intros)+
      apply(simp add: vdiff_def, safe)
      apply(clarsimp) subgoal for s X t "\<tau>"
      apply(rule flow_vel_is_galilean_vel2[of X "''x''"])
      by(simp_all add: varDiffs_def vdiff_def)
      apply(simp add: vdiff_def varDiffs_def solvesStoreIVP_def)
      apply(simp add: vdiff_def varDiffs_def solvesStoreIVP_def solves_ode_def 
        has_vderiv_on_singleton galilean_transform_eq galilean_transform)
      \<comment> \<open>Relation Between the guard and the postcondition.\<close>
      by(auto simp: vdiff_def p2r_def)

\<comment> \<open>Example of hybrid program verified with differential weakening.\<close>
lemma system_where_the_guard_implies_the_postcondition:
      "PRE (\<lambda> s. s ''x'' = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' \<ge> 0))
      POST (\<lambda> s. s ''x'' \<ge> 0)"
using dWeakening by blast

lemma system_where_the_guard_implies_the_postcondition2:
      "PRE (\<lambda> s. s ''x'' = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' \<ge> 0))
      POST (\<lambda> s. s ''x'' \<ge> 0)"
apply(clarify, simp add: p2r_def)
apply(simp add: rel_ad_def rel_antidomain_kleene_algebra.addual.ars_r_def)
apply(simp add: rel_antidomain_kleene_algebra.fbox_def)
apply(simp add: relcomp_def rel_ad_def guarDiffEqtn_def solvesStoreIVP_def)
by auto

\<comment> \<open>Example of system proved with a differential invariant.\<close>
lemma circular_motion:
      "PRE (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''y'')),(''y'',(\<lambda> s. - s ''x''))] with G)
      POST (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)"
apply(rule_tac \<eta>="(t\<^sub>V ''x'')\<odot>(t\<^sub>V ''x'') \<oplus> (t\<^sub>V ''y'')\<odot>(t\<^sub>V ''y'') \<oplus> (\<ominus>(t\<^sub>V ''r'')\<odot>(t\<^sub>V ''r''))" 
  and uInput="[t\<^sub>V ''y'', \<ominus> (t\<^sub>V ''x'')]" in dInvForTrms)
apply(simp_all add: vdiff_def varDiffs_def) 
apply(clarsimp, erule_tac x="''r''" in allE)
by simp

\<comment> \<open>Example of systems proved with differential invariants, cuts and weakenings.\<close>
declare d_p2r [simp del]
lemma motion_with_constant_velocity_and_invariants:
      "PRE (\<lambda> s. s ''x'' > s ''y'' \<and> s ''v'' > 0)
      (ODEsystem [(''x'', \<lambda> s. s ''v'')] with (\<lambda> s. True))
      POST (\<lambda> s. s ''x''>  s ''y'')"
apply(rule_tac C = "\<lambda> s.  s ''v'' > 0" in dCut)
apply(rule_tac \<phi> = "(t\<^sub>C 0) \<prec> (t\<^sub>V ''v'')" and uInput="[t\<^sub>V ''v'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''v''" in allE, simp)
apply(rule_tac C = "\<lambda> s.  s ''x'' > s ''y''" in dCut)
apply(rule_tac \<phi>="(t\<^sub>V ''y'') \<prec> (t\<^sub>V ''x'')" and uInput="[t\<^sub>V ''v'']" and 
  F="\<lambda> s.  s ''x'' > s ''y''" in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''y''" in allE, simp)
using dWeakening by simp

lemma motion_with_constant_acceleration_and_invariants:
      "PRE (\<lambda> s. s ''y'' < s ''x''  \<and> s ''v'' \<ge> 0 \<and> s ''a'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v'')),(''v'',(\<lambda> s. s ''a''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''y'' < s ''x''))"
apply(rule_tac C = "\<lambda> s.  s ''a'' > 0" in dCut) 
apply(rule_tac \<phi> = "(t\<^sub>C 0) \<prec> (t\<^sub>V ''a'')" and uInput="[t\<^sub>V ''v'', t\<^sub>V ''a'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''a''" in allE, simp)
apply(rule_tac C = "\<lambda> s.  s ''v'' \<ge> 0" in dCut)
apply(rule_tac \<phi> = "(t\<^sub>C 0) \<preceq> (t\<^sub>V ''v'')" and uInput="[t\<^sub>V ''v'', t\<^sub>V ''a'']" in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def)
apply(rule_tac C = "\<lambda> s.  s ''x'' >  s ''y''" in dCut)
apply(rule_tac \<phi> = "(t\<^sub>V ''y'') \<prec> (t\<^sub>V ''x'')" and uInput="[t\<^sub>V ''v'', t\<^sub>V ''a'']"in dInvFinal)
apply(simp_all add: varDiffs_def vdiff_def, clarify, erule_tac x="''y''" in allE, simp)
using dWeakening by simp

\<comment> \<open>We revisit the two modes example from before, and prove it with invariants.\<close>
lemma single_hop_ball_and_invariants:
      "PRE (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' = H \<and> s ''v'' = 0 \<and> s ''g'' > 0 \<and> 1 \<ge> c \<and> c \<ge> 0)  
      (((ODEsystem [(''x'', \<lambda> s. s ''v''),(''v'',\<lambda> s. - s ''g'')] with (\<lambda> s. 0 \<le> s ''x'')));
      (IF (\<lambda> s. s ''x'' = 0) THEN (''v'' ::= (\<lambda> s. - c \<cdot> s ''v'')) ELSE (''v'' ::= (\<lambda> s. s ''v'')) FI))
      POST (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' \<le> H)"
      apply(simp add: d_p2r, subgoal_tac "rdom \<lceil>\<lambda>s. 0 \<le> s ''x'' \<and> s ''x'' = H \<and> s ''v'' = 0 \<and> 0 < s ''g'' \<and> c \<le> 1 \<and> 0 \<le> c\<rceil>
    \<subseteq> wp (ODEsystem [(''x'', \<lambda>s. s ''v''), (''v'', \<lambda>s. - s ''g'')] with (\<lambda>s. 0 \<le> s ''x'') )
        \<lceil>inf (sup (- (\<lambda>s. s ''x'' = 0)) (\<lambda>s. 0 \<le> s ''x'' \<and> s ''x'' \<le> H)) (sup (\<lambda>s. s ''x'' = 0) (\<lambda>s. 0 \<le> s ''x'' \<and> s ''x'' \<le> H))\<rceil>") 
      apply(simp add: d_p2r, rule_tac C = "\<lambda> s.  s ''g'' > 0" in dCut)
      apply(rule_tac \<phi> = "(t\<^sub>C 0) \<prec> (t\<^sub>V ''g'')" and uInput="[t\<^sub>V ''v'', \<ominus> t\<^sub>V ''g'']"in dInvFinal)
      apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''g''" in allE, simp)
      apply(rule_tac C ="\<lambda> s.  s ''v'' \<le> 0" in dCut)
      apply(rule_tac \<phi> = "(t\<^sub>V ''v'') \<preceq> (t\<^sub>C 0)" and uInput="[t\<^sub>V ''v'', \<ominus> t\<^sub>V ''g'']" in dInvFinal)
      apply(simp_all add: vdiff_def varDiffs_def)
      apply(rule_tac C = "\<lambda> s.  s ''x'' \<le>  H" in dCut)
      apply(rule_tac \<phi> = "(t\<^sub>V ''x'') \<preceq> (t\<^sub>C H)" and uInput="[t\<^sub>V ''v'', \<ominus> t\<^sub>V ''g'']"in dInvFinal)
      apply(simp_all add: varDiffs_def vdiff_def)
      using dWeakening by simp

\<comment> \<open>Finally, we add a well known example in the hybrid systems community, the bouncing ball.\<close>
lemma bouncing_ball_invariant:"0 \<le> x \<Longrightarrow> 0 < g \<Longrightarrow> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H - v \<cdot> v \<Longrightarrow> (x::real) \<le> H"
proof-
assume "0 \<le> x" and "0 < g" and "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> H - v \<cdot> v"
then have "v \<cdot> v = 2 \<cdot> g \<cdot> H - 2 \<cdot> g \<cdot> x \<and> 0 < g" by auto
hence *:"v \<cdot> v = 2 \<cdot> g \<cdot> (H - x) \<and> 0 < g \<and> v \<cdot> v \<ge> 0" 
  using left_diff_distrib mult.commute by (metis zero_le_square) 
from this have "(v \<cdot> v)/(2 \<cdot> g) = (H - x)" by auto 
also from * have "(v \<cdot> v)/(2 \<cdot> g) \<ge> 0"
by (meson divide_nonneg_pos linordered_field_class.sign_simps(44) zero_less_numeral) 
ultimately have "H - x \<ge> 0" by linarith
thus ?thesis by auto
qed

lemma bouncing_ball:
"PRE (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' = H \<and> s ''v'' = 0 \<and> s ''g'' > 0)  
((ODEsystem [(''x'', \<lambda> s. s ''v''),(''v'',\<lambda> s. - s ''g'')] with (\<lambda> s. 0 \<le> s ''x''));
(IF (\<lambda> s. s ''x'' = 0) THEN (''v'' ::= (\<lambda> s. - s ''v'')) ELSE (Id) FI))\<^sup>*
POST (\<lambda> s. 0 \<le> s ''x'' \<and> s ''x'' \<le> H)"
apply(rule rel_antidomain_kleene_algebra.fbox_starI[of _ "\<lceil>\<lambda>s. 0 \<le> s ''x'' \<and> 0 < s ''g'' \<and> 
2 \<cdot> s ''g'' \<cdot> s ''x'' = 2 \<cdot> s ''g'' \<cdot> H - (s ''v'' \<cdot> s ''v'')\<rceil>"])
apply(simp, simp add: d_p2r)
apply(subgoal_tac 
  "rdom \<lceil>\<lambda>s. 0 \<le> s ''x'' \<and> 0 < s ''g'' \<and> 2 \<cdot> s ''g'' \<cdot> s ''x'' = 2 \<cdot> s ''g'' \<cdot> H - s ''v'' \<cdot> s ''v''\<rceil>
  \<subseteq> wp (ODEsystem [(''x'', \<lambda>s. s ''v''), (''v'', \<lambda>s. - s ''g'')] with (\<lambda>s. 0 \<le> s ''x'') )
  \<lceil>inf  (sup (- (\<lambda>s. s ''x'' = 0)) (\<lambda>s. 0 \<le> s ''x'' \<and> 0 < s ''g'' \<and> 2 \<cdot> s ''g'' \<cdot> s ''x'' = 
          2 \<cdot> s ''g'' \<cdot> H - s ''v'' \<cdot> s ''v''))
        (sup (\<lambda>s. s ''x'' = 0) (\<lambda>s. 0 \<le> s ''x'' \<and> 0 < s ''g'' \<and> 2 \<cdot> s ''g'' \<cdot> s ''x'' = 
          2 \<cdot> s ''g'' \<cdot> H - s ''v'' \<cdot> s ''v''))\<rceil>")
apply(simp add: d_p2r)
apply(rule_tac C = "\<lambda> s.  s ''g'' > 0" in dCut)
apply(rule_tac \<phi> = "((t\<^sub>C 0) \<prec> (t\<^sub>V ''g''))" and uInput="[t\<^sub>V ''v'', \<ominus> t\<^sub>V ''g'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''g''" in allE, simp)
apply(rule_tac C = "\<lambda> s. 2 \<cdot> s ''g'' \<cdot> s ''x'' = 2 \<cdot> s ''g'' \<cdot> H - s ''v'' \<cdot> s ''v''" in dCut)
apply(rule_tac \<phi> = "(t\<^sub>C 2) \<odot> (t\<^sub>V ''g'') \<odot> (t\<^sub>C H) \<oplus> (\<ominus> ((t\<^sub>V ''v'') \<odot> (t\<^sub>V ''v''))) 
  \<doteq> (t\<^sub>C 2) \<odot> (t\<^sub>V ''g'') \<odot> (t\<^sub>V ''x'')" and uInput="[t\<^sub>V ''v'', \<ominus> t\<^sub>V ''g'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''g''" in allE, simp)
apply(rule dWeakening, clarsimp)
using bouncing_ball_invariant by auto

declare d_p2r [simp]

end