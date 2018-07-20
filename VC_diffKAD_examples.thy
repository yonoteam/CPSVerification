theory VC_diffKAD_examples
imports "VC_diffKAD"

begin
subsection{* Rules Testing *}
text{* In this section we test the recently developed rules with simple dynamical systems. *}

-- "Example of hybrid program verified with the rule dSolve."
lemma motion_with_constant_velocity:
      "PRE (\<lambda> s. s ''y'' < s ''x''  \<and> s ''v'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''y'' < s ''x''))"
apply(rule_tac uInput="[\<lambda> t s. s ''v'' \<cdot> t + s ''x'']" in dSolve_toSolveUBC)
prefer 9 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
apply(simp_all add: vdiff_def varDiffs_def)
prefer 2 apply(clarify, rule continuous_intros)
prefer 2 apply(simp add: solvesStoreIVP_def vdiff_def varDiffs_def)
apply(clarify, rule_tac f'1="\<lambda> x. s ''v''" and g'1="\<lambda> x. 0" in derivative_intros(173))
apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))
by(auto intro: derivative_intros)

-- "Example of hybrid program verified with differential weakening."
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

-- "Example of system proved with a differential invariant."
lemma circular_motion:
      "PRE (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''y'')),(''y'',(\<lambda> s. - s ''x''))] with G)
      POST (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)"
apply(rule_tac \<eta>="(t\<^sub>V ''x'')\<odot>(t\<^sub>V ''x'') \<oplus> (t\<^sub>V ''y'')\<odot>(t\<^sub>V ''y'') \<oplus> (\<ominus>(t\<^sub>V ''r'')\<odot>(t\<^sub>V ''r''))" 
  and uInput="[t\<^sub>V ''y'', \<ominus> (t\<^sub>V ''x'')]" in dInvForTrms)
apply(simp_all add: vdiff_def varDiffs_def) 
apply(clarsimp, erule_tac x="''r''" in allE)
by simp

-- "Example of systems proved with differential invariants, cuts and weakenings."
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

-- "Example of a hybrid system with two modes."
lemma single_hoop_ball:
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
declare d_p2r [simp]

end