theory VC_diffKAD
imports "VC_diffKAD_auxiliarities"

begin
subsection{* Phase Space Relational Semantics *}

definition solvesStoreIVP :: "(real \<Rightarrow> real store) \<Rightarrow> (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real store \<Rightarrow> bool" 
("(_ solvesTheStoreIVP _ withInitState _ )" [70, 70, 70] 68) where
"solvesStoreIVP \<phi>\<^sub>S xfList s \<equiv> 
\<comment> \<open>F sends vdiffs-in-list to derivs.\<close>
(\<forall> t \<ge> 0. (\<forall> xf \<in> set xfList. \<phi>\<^sub>S t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (\<phi>\<^sub>S t)) \<and> 
\<comment> \<open>F preserves the rest of the variables and F sends derivs of constants to 0.\<close>
(\<forall> y. (y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<union> varDiffs \<longrightarrow> \<phi>\<^sub>S t y = s y) \<and> 
      (y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> \<phi>\<^sub>S t (\<partial> y) = 0)) \<and> 
\<comment> \<open>F solves the induced IVP.\<close>
(\<forall> xf \<in> set xfList. ((\<lambda> t. \<phi>\<^sub>S t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda> t.\<lambda> r.(\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t))) {0..t} UNIV \<and>
\<phi>\<^sub>S 0 (\<pi>\<^sub>1 xf) = s(\<pi>\<^sub>1 xf)))"
  
lemma solves_store_ivpI:
assumes "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (\<phi>\<^sub>S t (\<partial> (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t)"
  and "\<forall> t \<ge> 0.\<forall> y. y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>)\<union>varDiffs \<longrightarrow> \<phi>\<^sub>S t y = s y"
  and "\<forall> t \<ge> 0.\<forall> y. y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> \<phi>\<^sub>S t (\<partial> y) = 0" 
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. \<phi>\<^sub>S t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda> t.\<lambda> r.(\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t))) {0..t} UNIV"
  and "\<forall> xf \<in> set xfList. \<phi>\<^sub>S 0 (\<pi>\<^sub>1 xf) = s(\<pi>\<^sub>1 xf)"
shows "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
apply(simp add: solvesStoreIVP_def, safe)
using assms apply simp_all
by(force,force,force)

named_theorems solves_store_ivpE "elimination rules for solvesStoreIVP"

lemma [solves_store_ivpE]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
shows "\<forall> t \<ge> 0.\<forall> y. y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>)\<union>varDiffs \<longrightarrow> \<phi>\<^sub>S t y = s y"
  and "\<forall> t \<ge> 0.\<forall> y. y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> \<phi>\<^sub>S t (\<partial> y) = 0"
  and "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (\<phi>\<^sub>S t (\<partial> (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t)"
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. \<phi>\<^sub>S t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda> t.\<lambda> r.(\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t))) {0..t} UNIV"
  and "\<forall> xf \<in> set xfList. \<phi>\<^sub>S 0 (\<pi>\<^sub>1 xf) = s(\<pi>\<^sub>1 xf)"
using assms solvesStoreIVP_def by auto

lemma [solves_store_ivpE]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
shows "\<forall> y. y \<notin> varDiffs \<longrightarrow> \<phi>\<^sub>S 0 y = s y"
proof(clarify, rename_tac x)
fix x assume "x \<notin> varDiffs"
from assms and solves_store_ivpE(5) have "x \<in> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<Longrightarrow> \<phi>\<^sub>S 0 x = s x" by fastforce
also have "x \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<union> varDiffs \<Longrightarrow> \<phi>\<^sub>S 0 x = s x" 
using assms and solves_store_ivpE(1) by simp
ultimately show "\<phi>\<^sub>S 0 x = s x" using \<open>x \<notin> varDiffs\<close> by auto
qed

named_theorems solves_store_ivpD "computation rules for solvesStoreIVP"

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "t \<ge> 0"
  and "y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>)\<union>varDiffs"
shows "\<phi>\<^sub>S t y = s y"
using assms solves_store_ivpE(1) by simp

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "t \<ge> 0"
  and "y \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>)"
shows "\<phi>\<^sub>S t (\<partial> y) = 0"
using assms solves_store_ivpE(2) by simp

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "t \<ge> 0"
  and "xf \<in> set xfList"
shows "(\<phi>\<^sub>S t (\<partial> (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t)"
using assms solves_store_ivpE(3) by simp

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "t \<ge> 0"
  and "xf \<in> set xfList"
shows "((\<lambda> t. \<phi>\<^sub>S t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda> t.\<lambda> r.(\<pi>\<^sub>2 xf) (\<phi>\<^sub>S t))) {0..t} UNIV" 
using assms solves_store_ivpE(4) by simp

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "(x,f) \<in> set xfList"
shows "\<phi>\<^sub>S 0 x = s x" 
using assms solves_store_ivpE(5) by fastforce

lemma [solves_store_ivpD]:
assumes "\<phi>\<^sub>S solvesTheStoreIVP xfList withInitState s"
  and "y \<notin> varDiffs"
shows "\<phi>\<^sub>S 0 y = s y" 
using assms solves_store_ivpE(6) by simp

definition guarDiffEqtn :: "(string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> (real store pred) \<Rightarrow> 
real store rel" ("ODEsystem _ with _ " [70, 70] 61) where
"ODEsystem xfList with G = {(s,\<phi>\<^sub>S t) |s t \<phi>\<^sub>S. t \<ge> 0 \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r)) \<and> solvesStoreIVP \<phi>\<^sub>S xfList s}"

subsection{* Derivation of Differential Dynamic Logic Rules *}

subsubsection{*"Differential Weakening"*}
lemma wlp_evol_guard:"Id \<subseteq> wp (ODEsystem xfList with G) \<lceil>G\<rceil>"
by(simp add: rel_antidomain_kleene_algebra.fbox_def rel_ad_def guarDiffEqtn_def p2r_def, force)

theorem dWeakening: 
assumes guardImpliesPost: "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE P (ODEsystem xfList with G) POST Q"
using assms and wlp_evol_guard by (metis (no_types, hide_lams) d_p2r 
order_trans p2r_subid rel_antidomain_kleene_algebra.fbox_iso)

theorem dW: "wp (ODEsystem xfList with G) \<lceil>Q\<rceil> = wp (ODEsystem xfList with G) \<lceil>\<lambda>s. G s \<longrightarrow> Q s\<rceil>"
unfolding rel_antidomain_kleene_algebra.fbox_def rel_ad_def guarDiffEqtn_def
by(simp add: relcomp.simps p2r_def, fastforce)

subsubsection{*"Differential Cut"*}

lemma all_interval_guarDiffEqtn:
assumes "solvesStoreIVP \<phi>\<^sub>S xfList s \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r)) \<and> 0 \<le> t"
shows "\<forall> r \<in> {0..t}. (s, \<phi>\<^sub>S r) \<in> (ODEsystem xfList with G)"
unfolding guarDiffEqtn_def using atLeastAtMost_iff apply clarsimp
apply(rule_tac x="r" in exI, rule_tac x="\<phi>\<^sub>S" in exI) using assms by simp

lemma condAfterEvol_remainsAlongEvol:
assumes boxDiffC:"(s, s) \<in> wp (ODEsystem xfList with G) \<lceil>C\<rceil>"
and FisSol:"solvesStoreIVP \<phi>\<^sub>S xfList s \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r)) \<and> 0 \<le> t"
shows "\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r) \<and> C (\<phi>\<^sub>S r)"
proof-
from boxDiffC have "\<forall> c. (s,c) \<in> (ODEsystem xfList with G) \<longrightarrow> C c"
  by (simp add: boxProgrPred_chrctrztn)
also from FisSol have "\<forall> r \<in> {0..t}. (s, \<phi>\<^sub>S r) \<in> (ODEsystem xfList with G)" 
  using all_interval_guarDiffEqtn by blast 
ultimately show ?thesis
  using FisSol atLeastAtMost_iff guarDiffEqtn_def by fastforce
qed

theorem dCut:
assumes pBoxDiffCut:"(PRE P (ODEsystem xfList with G) POST C)"
assumes pBoxCutQ:"(PRE P (ODEsystem xfList with (\<lambda> s. G s \<and> C s)) POST Q)"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(clarify, subgoal_tac "a = b") defer
proof(metis d_p2r rdom_p2r_contents, simp, subst boxProgrPred_chrctrztn, clarify)
fix b y assume "(b, b) \<in> \<lceil>P\<rceil>" and "(b, y) \<in> ODEsystem xfList with G"
then obtain \<phi>\<^sub>S t where *:"solvesStoreIVP \<phi>\<^sub>S xfList b \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r)) \<and> 0 \<le> t \<and> \<phi>\<^sub>S t = y"
  using guarDiffEqtn_def by auto
hence "\<forall> r \<in> {0..t}. (b, \<phi>\<^sub>S r) \<in> (ODEsystem xfList with G)" 
  using all_interval_guarDiffEqtn by blast
from this and pBoxDiffCut have "\<forall> r \<in> {0..t}. C (\<phi>\<^sub>S r)" 
  using  boxProgrPred_chrctrztn \<open>(b, b) \<in> \<lceil>P\<rceil>\<close> by (metis (no_types, lifting) d_p2r subsetCE)
then have "\<forall> r \<in> {0..t}. (b, \<phi>\<^sub>S r) \<in> (ODEsystem xfList with (\<lambda> s. G s \<and> C s))" 
  using * all_interval_guarDiffEqtn by (metis (mono_tags, lifting))
from this and pBoxCutQ have "\<forall> r \<in> {0..t}. Q (\<phi>\<^sub>S r)" 
  using  boxProgrPred_chrctrztn \<open>(b, b) \<in> \<lceil>P\<rceil>\<close> by (metis (no_types, lifting) d_p2r subsetCE)
thus "Q y" using * by auto 
qed

theorem dC:
assumes "Id \<subseteq>  wp (ODEsystem xfList with G) \<lceil>C\<rceil>"
shows "wp (ODEsystem xfList with G ) \<lceil>Q\<rceil> = wp (ODEsystem xfList with (\<lambda> s. G s \<and> C s)) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, safe)
  fix a b assume "(a, b) \<in> ODEsystem xfList with G" 
  then obtain \<phi>\<^sub>S t where *:"solvesStoreIVP \<phi>\<^sub>S xfList a \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r)) \<and> 0 \<le> t \<and> \<phi>\<^sub>S t = b"
    using guarDiffEqtn_def by auto
  hence 1:"\<forall> r \<in> {0..t}. (a, \<phi>\<^sub>S r) \<in> ODEsystem xfList with G"
    by (meson all_interval_guarDiffEqtn)
  from this have "\<forall> r \<in> {0..t}. C (\<phi>\<^sub>S r)" using assms boxProgrPred_chrctrztn
    by (metis IdI boxProgrPred_IsProp subset_antisym)
  thus "(a, b) \<in> ODEsystem xfList with (\<lambda>s. G s \<and> C s)" 
    using * guarDiffEqtn_def by blast 
next
  fix a b assume "(a, b) \<in> ODEsystem xfList with (\<lambda>s. G s \<and> C s)" 
  then show "(a, b) \<in> ODEsystem xfList with G"
  unfolding guarDiffEqtn_def by(clarsimp, rule_tac x="t" in exI, rule_tac x="\<phi>\<^sub>S" in exI, simp)
qed


subsubsection{*"Solve Differential Equation"*}
lemma prelim_dSolve:
assumes solHyp:"(\<lambda>t. sol s[xfList\<leftarrow>uInput] t) solvesTheStoreIVP xfList withInitState s"
and uniqHyp:"\<forall> X. solvesStoreIVP X xfList s \<longrightarrow> (\<forall> t \<ge> 0. (sol s[xfList\<leftarrow>uInput] t) = X t)"
and diffAssgn: "\<forall>t\<ge>0. G (sol s[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol s[xfList\<leftarrow>uInput] t)"
shows "\<forall> c. (s,c) \<in> (ODEsystem xfList with G) \<longrightarrow> Q c"
proof(clarify)
fix c assume "(s,c) \<in> (ODEsystem xfList with G)"
from this obtain t::"real" and \<phi>\<^sub>S::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> \<phi>\<^sub>S t = c \<and> solvesStoreIVP \<phi>\<^sub>S xfList s \<and> (\<forall> r \<in> {0..t}. G (\<phi>\<^sub>S r))" 
using guarDiffEqtn_def by auto 
from this and uniqHyp have "(sol s[xfList\<leftarrow>uInput] t) = \<phi>\<^sub>S t" by blast
then have cHyp:"c = (sol s[xfList\<leftarrow>uInput] t)" using FHyp by simp
from this have "G (sol s[xfList\<leftarrow>uInput] t)" using FHyp by force
then show "Q c" using diffAssgn FHyp cHyp by auto
qed

theorem dS:
assumes solHyp:"\<forall> s. solvesStoreIVP (\<lambda>t. sol s[xfList\<leftarrow>uInput] t) xfList s"
and uniqHyp:"\<forall> s X. solvesStoreIVP X xfList s \<longrightarrow> (\<forall> t \<ge> 0. (sol s[xfList\<leftarrow>uInput] t) = X t)"
shows "wp (ODEsystem xfList with G) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<ge>0. (\<forall>r\<in>{0..t}. G (sol s[xfList\<leftarrow>uInput] r)) \<longrightarrow> Q (sol s[xfList\<leftarrow>uInput] t)\<rceil>"
apply(simp add: p2r_def, rule subset_antisym)
unfolding guarDiffEqtn_def rel_antidomain_kleene_algebra.fbox_def rel_ad_def
using solHyp apply(simp add: relcomp.simps) apply clarify
apply(rule_tac x="x" in exI, clarsimp)
apply(erule_tac x="sol x[xfList\<leftarrow>uInput] t" in allE, erule disjE)
apply(erule_tac x="x" in allE, erule_tac x="t" in allE)
apply(erule impE, simp, erule_tac x="\<lambda>t. sol x[xfList\<leftarrow>uInput] t" in allE)
apply(simp_all, clarify, rule_tac x="s" in exI, simp add: relcomp.simps)
using uniqHyp by fastforce

theorem dSolve:
assumes solHyp:"\<forall>s. solvesStoreIVP (\<lambda>t. sol s[xfList\<leftarrow>uInput] t) xfList s"
and uniqHyp:"\<forall> s. \<forall> X. solvesStoreIVP X xfList s \<longrightarrow> (\<forall> t \<ge> 0.(sol s[xfList\<leftarrow>uInput] t) = X t)"
and diffAssgn: "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. G (sol s[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol s[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(clarsimp, subgoal_tac "a=b")
apply(clarify, subst boxProgrPred_chrctrztn)
apply(simp_all add: p2r_def)
apply(rule_tac uInput="uInput" in prelim_dSolve)
apply(simp add: solHyp, simp add: uniqHyp)
by (metis (no_types, lifting) diffAssgn)

\<comment> \<open>We proceed to refine the previous rule by finding the necessary restrictions on 
varFunList and uInput so that the solution to the store-IVP is guaranteed.\<close>
(* THIS SECTION SHOULD BE DONE WITH A LOCALE... CLEARLY IT CAN BE IMPROVED. *)
lemma conds4vdiffs_prelim:
assumes funcsHyp:"\<forall>s g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and solHyp1:"\<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and solHyp2:"\<forall>t\<ge>0. ((\<lambda>\<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>) x) 
has_vderiv_on (\<lambda>\<tau>. f (sol s[xfList\<leftarrow>uInput] \<tau>))) {0..t}" 
and xfHyp:"(x, f) \<in> set xfList" and tHyp:"t \<ge> 0"
shows "(sol s[xfList\<leftarrow>uInput] t) (\<partial> x) = f (sol s[xfList\<leftarrow>uInput] t)"
proof-
from xfHyp obtain u where xfuHyp: "(u,x,f) \<in> set (uInput \<otimes> xfList)"
by (metis in_set_impl_in_set_zip2 lengthHyp)
show "(sol s[xfList\<leftarrow>uInput] t) (\<partial> x) =f (sol s[xfList\<leftarrow>uInput] t)"
  proof(cases "t=0")
  case True
    have "(sol s[xfList\<leftarrow>uInput] 0) (\<partial> x) = f (sol s[xfList\<leftarrow>uInput] 0)"
    using assms and to_sol_zero_its_dvars by blast
    then show ?thesis using True by blast
  next
    case False
    from this have "t > 0" using tHyp by simp
    hence "(sol s[xfList\<leftarrow>uInput] t) (\<partial> x) = vderiv_of (\<lambda> r. u r (sol s)) {0<..< (2 *\<^sub>R t)} t" 
    using xfuHyp assms to_sol_greater_than_zero_its_dvars by blast
    also have "vderiv_of (\<lambda>r. u r (sol s)) {0<..< (2 *\<^sub>R t)} t = f (sol s[xfList\<leftarrow>uInput] t)" 
    using  assms xfuHyp \<open>t > 0\<close> and vderiv_of_to_sol_its_vars by blast
    ultimately show ?thesis by simp
  qed
qed

lemma conds4vdiffs:
assumes funcsHyp:"\<forall>s g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and solHyp1:"\<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and solHyp2:"\<forall>t\<ge>0. \<forall> xf \<in> set xfList. ((\<lambda>\<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>\<tau>. (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] \<tau>))) {0..t}" 
shows "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. (sol s[xfList\<leftarrow>uInput] t) (\<partial> (\<pi>\<^sub>1 xf)) = (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t)"
apply(rule allI, rule impI, rule ballI, rule conds4vdiffs_prelim)
using assms by simp_all

lemma conds4Consts:
assumes varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
shows "\<forall> x. x \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> (sol s[xfList\<leftarrow>uInput] t) (\<partial> x) = 0"
using varsHyp apply(induct xfList uInput rule: list_induct2')
apply(simp_all add: override_on_def varDiffs_def vdiff_def)
by clarsimp

lemma conds4InitState:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and xfHyp:"(x, f) \<in> set xfList"
shows "(sol s[xfList\<leftarrow>uInput] 0) x = s x"
proof-
from xfHyp obtain u where uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)"
by (metis in_set_impl_in_set_zip2 lengthHyp)
from varsHyp have toZeroHyp:"(sol s) x = s x" using override_on_def xfHyp by auto
from uxfHyp and solHyp1 have "u 0 (sol s) = (sol s) x" by fastforce
also have "(sol s[xfList\<leftarrow>uInput] 0) x = u 0 (sol s)" 
using state_list_cross_upd_its_vars uxfHyp and assms by blast 
ultimately show "(sol s[xfList\<leftarrow>uInput] 0) x = s x" using toZeroHyp by simp
qed

lemma conds4RestOfStrings: (* NONE, the transformed solution respects the rest of the variables. *)
assumes "x \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<union> varDiffs"
shows "(sol s[xfList\<leftarrow>uInput] t) x = s x"
using assms apply(induct xfList uInput rule: list_induct2')
by(auto simp: varDiffs_def)

lemma conds4storeIVP_on_toSol:
assumes funcsHyp:"\<forall>s g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)"
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and solHyp2:"\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol s[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol s[xfList\<leftarrow>uInput] t))) {0..t}"
shows "solvesStoreIVP (\<lambda> t. (sol s[xfList\<leftarrow>uInput] t)) xfList s"
apply(rule solves_store_ivpI)
subgoal using conds4vdiffs assms by blast
subgoal using conds4RestOfStrings by blast
subgoal using conds4Consts varsHyp by blast
subgoal apply(rule allI, rule impI, rule ballI, rule solves_odeI)
  using solHyp2 by simp_all
subgoal using conds4InitState and assms by force 
done

theorem dSolve_toSolve:
assumes funcsHyp:"\<forall>s g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)"
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> s.\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and solHyp2:"\<forall> s.\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol s[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol s[xfList\<leftarrow>uInput] t))) {0..t}"
and uniqHyp:"\<forall> s.\<forall> X. solvesStoreIVP X xfList s \<longrightarrow> (\<forall> t \<ge> 0. (sol s[xfList\<leftarrow>uInput] t) = X t)"
and postCondHyp:"\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. Q (sol s[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
subgoal using assms and conds4storeIVP_on_toSol by simp
subgoal by (simp add: uniqHyp)
using postCondHyp postCondHyp by simp

\<comment> \<open>As before, we keep refining the rule dSolve. This time we find the necessary restrictions 
to attain uniqueness.\<close>

lemma conds4UniqSol:
fixes f::"real store \<Rightarrow> real"
assumes tHyp:"t \<ge> 0"
and contHyp:"continuous_on ({0..t} \<times> UNIV) (\<lambda>(t, (r::real)). f (\<phi>\<^sub>s t))"
shows "unique_on_bounded_closed 0 {0..t} \<tau> (\<lambda>t r. f (\<phi>\<^sub>s t)) UNIV (if t = 0 then 1 else 1/(t+1))"
apply(simp add: ubc_definitions, rule conjI)
subgoal using contHyp continuous_rhs_def by fastforce 
subgoal using assms continuous_rhs_def by fastforce 
done

lemma solves_store_ivp_at_beginning_overrides:
assumes "solvesStoreIVP \<phi>\<^sub>s xfList a"
shows "\<phi>\<^sub>s 0 = override_on a (\<phi>\<^sub>s 0) varDiffs"
apply(rule ext, subgoal_tac "x \<notin> varDiffs \<longrightarrow> \<phi>\<^sub>s 0 x = a x")
subgoal by (simp add: override_on_def)
using assms and solves_store_ivpD(6) by simp

lemma ubcStoreUniqueSol:(* Can it still be refined??? *)
assumes tHyp:"t \<ge> 0"
assumes contHyp:"\<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t))"
and eqDerivs:"\<forall> xf \<in> set xfList. \<forall> \<tau> \<in> {0..t}. (\<pi>\<^sub>2 xf) (\<phi>\<^sub>s \<tau>) = (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] \<tau>)"
and Fsolves:"solvesStoreIVP \<phi>\<^sub>s xfList s"
and solHyp:"solvesStoreIVP (\<lambda> \<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>)) xfList s"
shows "(sol s[xfList\<leftarrow>uInput] t) = \<phi>\<^sub>s t"
proof
  fix x::"string" show "(sol s[xfList\<leftarrow>uInput] t) x = \<phi>\<^sub>s t x"
  proof(cases "x \<in> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<union> varDiffs")
  case False
    then have notInVars:"x \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<union> varDiffs" by simp
    from solHyp have "(sol s[xfList\<leftarrow>uInput] t) x = s x" 
    using tHyp notInVars solves_store_ivpD(1) by blast
    also from Fsolves have "\<phi>\<^sub>s t x = s x" using tHyp notInVars solves_store_ivpD(1) by blast
    ultimately show "(sol s[xfList\<leftarrow>uInput] t) x = \<phi>\<^sub>s t x" by simp
  next case True
    then have "x \<in> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<or> x \<in> varDiffs" by simp
    from this show ?thesis
    proof
      assume "x \<in> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>)" 
      from this obtain f where xfHyp:"(x, f) \<in> set xfList" by fastforce
      (* Expand hypothesis for arbitrary solution. *)
      then have expand1:"\<forall> xf \<in> set xfList.((\<lambda>\<tau>. \<phi>\<^sub>s \<tau> (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>\<tau> r. (\<pi>\<^sub>2 xf) (\<phi>\<^sub>s \<tau>))){0..t} UNIV \<and> \<phi>\<^sub>s 0 (\<pi>\<^sub>1 xf) = s (\<pi>\<^sub>1 xf)" 
      using Fsolves tHyp by (simp add:solvesStoreIVP_def)
      hence expand2:"\<forall> xf \<in> set xfList. \<forall> \<tau> \<in> {0..t}. ((\<lambda>r. \<phi>\<^sub>s r (\<pi>\<^sub>1 xf)) 
      has_vector_derivative (\<lambda>r. (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] \<tau>)) \<tau>) (at \<tau> within {0..t})" 
      using eqDerivs by (simp add: solves_ode_def has_vderiv_on_def)
      (* Re-express hypothesis for arbitrary solution in terms of user solution.*)
      then have "\<forall> xf \<in> set xfList. ((\<lambda>\<tau>. \<phi>\<^sub>s \<tau> (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>\<tau> r. (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] \<tau>))){0..t} UNIV \<and> \<phi>\<^sub>s 0 (\<pi>\<^sub>1 xf) = s (\<pi>\<^sub>1 xf)" 
      by (simp add: has_vderiv_on_def solves_ode_def expand1 expand2) 
      then have 1:"((\<lambda>\<tau>. \<phi>\<^sub>s \<tau> x) solves_ode (\<lambda>\<tau> r. f (sol s[xfList\<leftarrow>uInput] \<tau>))){0..t} UNIV \<and> 
      \<phi>\<^sub>s 0 x = s x" using xfHyp by fastforce
      (* Expand hypothesis for user's solution. *)
      from solHyp and xfHyp have 2:"((\<lambda> \<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>) x) solves_ode 
      (\<lambda>\<tau> r. f (sol s[xfList\<leftarrow>uInput] \<tau>))) {0..t} UNIV \<and> (sol s[xfList\<leftarrow>uInput] 0) x = s x" 
      using solvesStoreIVP_def tHyp by fastforce
      (* Show user's solution and arbitrary solution are the same. *)
      from tHyp and contHyp have "\<forall> xf \<in> set xfList. unique_on_bounded_closed 0 {0..t} (s (\<pi>\<^sub>1 xf)) 
      (\<lambda>\<tau> r. (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] \<tau>)) UNIV (if t = 0 then 1 else 1/(t+1))" 
      apply(clarify) apply(rule conds4UniqSol) by(auto)
      from this have 3:"unique_on_bounded_closed 0 {0..t} (s x) (\<lambda>\<tau> r. f (sol s[xfList\<leftarrow>uInput] \<tau>)) 
      UNIV (if t = 0 then 1 else 1/(t+1))" using xfHyp by fastforce
      from 1 2 and 3 show "(sol s[xfList\<leftarrow>uInput] t) x = \<phi>\<^sub>s t x"
      using unique_on_bounded_closed.unique_solution using real_Icc_closed_segment tHyp by blast
    next
      assume "x \<in> varDiffs"
      then obtain y where xDef:"x = \<partial> y" by (auto simp: varDiffs_def)
      show "(sol s[xfList\<leftarrow>uInput] t) x = \<phi>\<^sub>s t x "
      proof(cases "y \<in> set (map \<pi>\<^sub>1 xfList)")
      case True
        then obtain f where xfHyp:"(y, f) \<in> set xfList" by fastforce
        from tHyp and Fsolves have "\<phi>\<^sub>s t x = f (\<phi>\<^sub>s t)"
        using solves_store_ivpD(3) xfHyp xDef by force
        also have "(sol s[xfList\<leftarrow>uInput] t) x = f (sol s[xfList\<leftarrow>uInput] t)" 
        using solves_store_ivpD(3) xfHyp xDef solHyp tHyp by force
        ultimately show ?thesis using eqDerivs xfHyp tHyp by auto
      next case False
        then have "\<phi>\<^sub>s t x = 0" 
        using xDef solves_store_ivpD(2) Fsolves tHyp by simp
        also have "(sol s[xfList\<leftarrow>uInput] t) x = 0" 
        using False solHyp tHyp solves_store_ivpD(2) xDef by fastforce 
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

theorem dSolveUBC:
assumes contHyp:"\<forall> s. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t))"
and solHyp:"\<forall> s. solvesStoreIVP (\<lambda> t. (sol s[xfList\<leftarrow>uInput] t)) xfList s"
and uniqHyp:"\<forall> s. \<forall> \<phi>\<^sub>s. \<phi>\<^sub>s solvesTheStoreIVP xfList withInitState s \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0..t}. (\<pi>\<^sub>2 xf) (\<phi>\<^sub>s r) = (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] r))"
and diffAssgn: "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. G (sol s[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol s[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
prefer 2 subgoal proof(clarify)
fix s::"real store" and \<phi>\<^sub>s::"real \<Rightarrow> real store" and t::"real"
assume isSol:"solvesStoreIVP \<phi>\<^sub>s xfList s" and sHyp:"0 \<le> t"
from this and uniqHyp have "\<forall> xf \<in> set xfList. \<forall> t \<in> {0..t}. 
(\<pi>\<^sub>2 xf) (\<phi>\<^sub>s t) = (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t)" by auto
also have "\<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t))" using contHyp sHyp by blast
ultimately show "(sol s[xfList\<leftarrow>uInput] t) = \<phi>\<^sub>s t" 
using sHyp isSol ubcStoreUniqueSol solHyp by simp
qed using assms by simp_all

theorem dSolve_toSolveUBC:
assumes funcsHyp:"\<forall>s g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall>s. \<forall>uxf\<in>set (uInput \<otimes> xfList). \<pi>\<^sub>1 uxf 0 (sol s) = sol s (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))" 
and solHyp2:"\<forall> s. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. ((\<lambda>t. (sol s[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on 
(\<lambda>t. \<pi>\<^sub>2 xf (sol s[xfList\<leftarrow>uInput] t))) {0..t}"
and contHyp:"\<forall> s. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] t))"
and uniqHyp:"\<forall> s. \<forall> \<phi>\<^sub>s. \<phi>\<^sub>s solvesTheStoreIVP xfList withInitState s \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0..t}. (\<pi>\<^sub>2 xf) (\<phi>\<^sub>s r) = (\<pi>\<^sub>2 xf) (sol s[xfList\<leftarrow>uInput] r))"
and postCondHyp:"\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. Q (sol s[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolveUBC)
using contHyp apply simp
apply(rule allI, rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
using assms by auto

subsubsection{*"Differential Invariant."*}
lemma solvesStoreIVP_couldBeModified:
fixes F::"real \<Rightarrow> real store"
assumes vars:"\<forall>t\<ge>0. \<forall>xf\<in>set xfList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda>t r. \<pi>\<^sub>2 xf (F t))) {0..t} UNIV"
and dvars:"\<forall> t \<ge> 0. \<forall>xf\<in>set xfList. (F t (\<partial> (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
shows "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. 
((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (\<partial> (\<pi>\<^sub>1 xf))) (at r within {0..t})"
proof(clarify, rename_tac t r x f)
fix x f and t r::real
assume tHyp:"0 \<le> t" and xfHyp:"(x, f) \<in> set xfList" and rHyp:"r \<in> {0..t}"
from this and vars have "((\<lambda>t. F t x) solves_ode (\<lambda>t r. f (F t))) {0..t} UNIV" using tHyp by fastforce
hence *:"\<forall>r\<in>{0..t}. ((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) r) (at r within {0..t})" 
by (simp add: solves_ode_def has_vderiv_on_def tHyp)
have "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. (F r (\<partial> (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)" using assms by auto
from this rHyp and xfHyp have "(F r (\<partial> x)) = f (F r)" by force
then show "((\<lambda>t. F t (\<pi>\<^sub>1 (x, f))) has_vector_derivative F r (\<partial> (\<pi>\<^sub>1 (x, f)))) (at r within {0..t})" 
using * rHyp by auto
qed

lemma derivationLemma_baseCase:
fixes F::"real \<Rightarrow> real store"
assumes solves:"solvesStoreIVP F xfList a"
shows "\<forall> x \<in> (UNIV - varDiffs). \<forall> t \<ge> 0. \<forall>r\<in>{0..t}.
((\<lambda> t. F t x) has_vector_derivative F r (\<partial> x)) (at r within {0..t})"
proof
fix x
assume "x \<in> UNIV - varDiffs"
then have notVarDiff:"\<forall> z. x \<noteq> \<partial> z" using varDiffs_def by fastforce
  show "\<forall>t\<ge>0. \<forall>r\<in>{0..t}. ((\<lambda>t. F t x) has_vector_derivative F r (\<partial> x)) (at r within {0..t})"
  proof(cases "x \<in> set (map \<pi>\<^sub>1 xfList)")
    case True
    from this and solves have "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. 
    ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (\<partial> (\<pi>\<^sub>1 xf))) (at r within {0..t})"
    apply(rule_tac solvesStoreIVP_couldBeModified) using solves solves_store_ivpD by auto
    from this show ?thesis using True by auto
  next
    case False
    from this notVarDiff and solves have const:"\<forall> t \<ge> 0. F t x = a x" 
    using solves_store_ivpD(1) by (simp add: varDiffs_def)
    have constD:"\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. ((\<lambda> r. a x) has_vector_derivative 0) (at r within {0..t})"
    by (auto intro: derivative_eq_intros)
    {fix t r::real 
      assume "t\<ge>0" and "r \<in> {0..t}" 
      hence "((\<lambda> s. a x) has_vector_derivative 0) (at r within {0..t})" by (simp add: constD)
      moreover have "\<And>s. s \<in> {0..t} \<Longrightarrow> (\<lambda> r. F r x) s = (\<lambda> r. a x) s" 
      using const by (simp add: \<open>0 \<le> t\<close>)
      ultimately have "((\<lambda> s. F s x) has_vector_derivative 0) (at r within {0..t})"
      using has_vector_derivative_transform by (metis \<open>r \<in> {0..t}\<close>)}
    hence isZero:"\<forall>t\<ge>0.\<forall>r\<in>{0..t}.((\<lambda> t. F t x)has_vector_derivative 0)(at r within {0..t})"by blast
    from False solves and notVarDiff have "\<forall> t \<ge> 0. F t (\<partial> x) = 0"
    using solves_store_ivpD(2) by simp
    then show ?thesis using isZero by simp
  qed
qed

lemma derivationLemma:
assumes "solvesStoreIVP F xfList a"
and tHyp:"t \<ge> 0"
and termVarsHyp:"\<forall> x \<in> trmVars \<eta>. x \<in> (UNIV - varDiffs)"
shows "\<forall>r\<in>{0..t}. ((\<lambda> s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s))has_vector_derivative \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)) (at r within {0..t})"
using termVarsHyp  proof(induction \<eta>)
  case (Const r)
  then show ?case by simp
next
  case (Var y)
  then have yHyp:"y \<in> UNIV - varDiffs" by auto
  from this tHyp and assms(1) show ?case
  using derivationLemma_baseCase by auto
next
  case (Mns \<eta>)   
  then show ?case 
  apply(clarsimp)
  by(rule derivative_intros, simp)
next
  case (Sum \<eta>1 \<eta>2)
  then show ?case 
  apply(clarsimp)
  by(rule derivative_intros, simp_all)
next
  case (Mult \<eta>1 \<eta>2)
  then show ?case 
  apply(clarsimp)
  apply(subgoal_tac "((\<lambda>s. \<lbrakk>\<eta>1\<rbrakk>\<^sub>t (F s) *\<^sub>R \<lbrakk>\<eta>2\<rbrakk>\<^sub>t (F s)) has_vector_derivative 
  \<lbrakk>\<partial>\<^sub>t \<eta>1\<rbrakk>\<^sub>t (F r) \<cdot> \<lbrakk>\<eta>2\<rbrakk>\<^sub>t (F r) + \<lbrakk>\<eta>1\<rbrakk>\<^sub>t (F r) \<cdot> \<lbrakk>\<partial>\<^sub>t \<eta>2\<rbrakk>\<^sub>t (F r)) (at r within {0..t})",simp)
  apply(rule_tac f'1="\<lbrakk>\<partial>\<^sub>t \<eta>1\<rbrakk>\<^sub>t (F r)" and g'1="\<lbrakk>\<partial>\<^sub>t \<eta>2\<rbrakk>\<^sub>t (F r)" in derivative_eq_intros(25))
  by (simp_all add: has_field_derivative_iff_has_vector_derivative)
qed

lemma diff_subst_prprty_4terms:
assumes solves:"\<forall> xf \<in> set xfList. F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
and tHyp:"(t::real) \<ge> 0"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F t) = \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F t)"
using termVarsHyp apply(induction \<eta>) apply(simp_all add: substList_help2)
using listsHyp and solves apply(induct xfList uInput rule: list_induct2', simp, simp, simp)
proof(clarify, rename_tac y g xfTail \<theta> trmTail x)
fix x y::string and \<theta>::trms and g and xfTail::"((string \<times> (real store \<Rightarrow> real)) list)" and trmTail
assume IH:"\<And>x. x \<notin> varDiffs \<Longrightarrow> map \<pi>\<^sub>2 xfTail = map tval trmTail \<Longrightarrow>
\<forall>xf\<in>set xfTail. F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t) \<Longrightarrow>
F t (\<partial> x) = \<lbrakk>(map (vdiff \<circ> \<pi>\<^sub>1) xfTail \<otimes> trmTail)\<langle>t\<^sub>V (\<partial> x)\<rangle>\<rbrakk>\<^sub>t (F t)"
and 1:"x \<notin> varDiffs" and 2:"map \<pi>\<^sub>2 ((y, g) # xfTail) = map tval (\<theta> # trmTail)" 
and 3:"\<forall>xf\<in>set ((y, g) # xfTail). F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
hence *:"\<lbrakk>(map (vdiff \<circ> \<pi>\<^sub>1) xfTail \<otimes> trmTail)\<langle>Var (\<partial> x)\<rangle>\<rbrakk>\<^sub>t (F t) = F t (\<partial> x)" using tHyp by auto
show "F t (\<partial> x) = \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) \<langle>t\<^sub>V (\<partial> x)\<rangle>\<rbrakk>\<^sub>t (F t)"
  proof(cases "x \<in> set (map \<pi>\<^sub>1 ((y, g) # xfTail))")
    case True
    then have "x = y \<or> (x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail))" by auto
    moreover
    {assume "x = y"
      from this have "((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail))\<langle>t\<^sub>V (\<partial> x)\<rangle> = \<theta>" by simp
      also from 3 tHyp have "F t (\<partial> y) = g (F t)" by simp
      moreover from 2 have "\<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t) = g (F t)" by simp
      ultimately have ?thesis by (simp add: \<open>x = y\<close>)}
    moreover
    {assume "x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail)"
      then have "\<partial> x \<noteq> \<partial> y" using vdiff_inj by auto
      from this have "((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) \<langle>t\<^sub>V (\<partial> x)\<rangle> = 
      ((map (vdiff \<circ> \<pi>\<^sub>1) xfTail) \<otimes> trmTail) \<langle>t\<^sub>V (\<partial> x)\<rangle>" by simp
      hence ?thesis using * by simp}
    ultimately show ?thesis by blast
  next
    case False
    then have "((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) \<langle>t\<^sub>V (\<partial> x)\<rangle> = t\<^sub>V (\<partial> x)" 
    using substList_cross_vdiff_on_non_ocurring_var by(metis(no_types, lifting) List.map.compositionality)
    thus ?thesis by simp
  qed
qed

lemma eqInVars_impl_eqInTrms:
assumes termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and initHyp:"\<forall>x. x \<notin> varDiffs \<longrightarrow> b x = a x"
shows "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = \<lbrakk>\<eta>\<rbrakk>\<^sub>t b"
using assms by(induction \<eta>, simp_all)

lemma non_empty_funList_implies_non_empty_trmList:
shows "\<forall> list.(x,f) \<in> set list \<and> map \<pi>\<^sub>2 list = map tval tList \<longrightarrow> (\<exists> \<theta>.\<lbrakk>\<theta>\<rbrakk>\<^sub>t = f \<and> \<theta> \<in> set tList)"
by(induction tList, auto)

lemma dInvForTrms_prelim:
assumes substHyp:
"\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
shows "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c = 0)"
proof(clarify)
fix c assume aHyp:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a \<and> (\<forall>r\<in>{0..t}. G (F r))" 
using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = 0" using aHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_vector_derivative 
\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "\<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. F r (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)" 
using tcHyp solves_store_ivpD(3) by fastforce
hence "\<forall>r\<in>{0..t}. \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) = \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r)"
using tcHyp diff_subst_prprty_4terms termVarsHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r) = 0" 
using solves_store_ivpD(2) tcHyp by fastforce
ultimately have "\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_vector_derivative 0) (at r within {0..t})" 
using obs2 by auto
from this and tcHyp have "\<forall>s\<in>{0..t}. ((\<lambda>x. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F x)) has_derivative (\<lambda>x. x *\<^sub>R 0)) 
(at s within {0..t})" by (metis has_vector_derivative_def)
hence "\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) - \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = (\<lambda>x. x *\<^sub>R 0) (t - 0)" 
using mvt_very_simple and tcHyp by fastforce 
then show "\<lbrakk>\<eta>\<rbrakk>\<^sub>t c = 0" using obs1 tcHyp by auto 
qed

theorem dInvForTrms:
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
and eta_f:"f = \<lbrakk>\<eta>\<rbrakk>\<^sub>t"
shows " PRE (\<lambda> s. f s = 0) (ODEsystem xfList with G) POST (\<lambda> s. f s = 0)"
using eta_f proof(clarsimp)
fix a b
assume "(a, b) \<in> \<lceil>\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t s = 0\<rceil>" and "f = \<lbrakk>\<eta>\<rbrakk>\<^sub>t"
from this have aHyp:"a = b \<and> \<lbrakk>\<eta>\<rbrakk>\<^sub>t a = 0" by (metis (full_types) d_p2r rdom_p2r_contents)
have "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c = 0)"
using assms dInvForTrms_prelim by metis 
from this and aHyp have "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c = 0" by blast
thus "(a, b) \<in> wp (ODEsystem xfList with G ) \<lceil>\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t s = 0\<rceil>"
using aHyp by (simp add: boxProgrPred_chrctrztn) 
qed

lemma diff_subst_prprty_4props:
assumes solves:"\<forall> xf \<in> set xfList. F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
and tHyp:"t \<ge> 0"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
shows "\<lbrakk>\<partial>\<^sub>P \<phi>\<rbrakk>\<^sub>P (F t) = \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P \<phi>\<restriction>\<rbrakk>\<^sub>P (F t)"
using propVarsHyp apply(induction \<phi>, simp_all)
using assms diff_subst_prprty_4terms apply fastforce
using assms diff_subst_prprty_4terms apply fastforce
using assms diff_subst_prprty_4terms by fastforce

lemma dInvForProps_prelim:
assumes substHyp:
"\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t st \<ge> 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
shows "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a > 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c > 0)"
and "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a \<ge> 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c \<ge> 0)"
proof(clarify)
fix c assume aHyp:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t a > 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a \<and> (\<forall>r\<in>{0..t}. G (F r))" 
using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) > 0" using aHyp tcHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_vector_derivative 
\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "(\<forall>t\<ge>0. \<forall> xf \<in> set xfList. F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t))"
using tcHyp solves_store_ivpD(3) by blast
hence "\<forall>r\<in>{0..t}. \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) = \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r)"
using diff_subst_prprty_4terms termVarsHyp tcHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r) \<ge> 0" 
using solves_store_ivpD(2) tcHyp by (metis atLeastAtMost_iff)
ultimately have *:"\<forall>r\<in>{0..t}. \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) \<ge> 0" by (simp)
from obs2 and tcHyp have "\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_derivative 
(\<lambda>x. x *\<^sub>R (\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)))) (at r within {0..t})" by (simp add: has_vector_derivative_def) 
hence "\<exists>r\<in>{0..t}. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) - \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = t \<cdot> (\<lbrakk>(\<partial>\<^sub>t \<eta>)\<rbrakk>\<^sub>t) (F r)" 
using mvt_very_simple and tcHyp by fastforce
then obtain r where "\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) \<ge> 0 \<and> 0 \<le> r \<and> r \<le> t \<and> \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F t) \<ge> 0
\<and> \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) - \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = t \<cdot> (\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r))" 
using * tcHyp by (meson atLeastAtMost_iff order_refl) 
thus "\<lbrakk>\<eta>\<rbrakk>\<^sub>t c > 0"
using obs1 tcHyp by (metis cancel_comm_monoid_add_class.diff_cancel diff_ge_0_iff_ge 
diff_strict_mono linorder_neqE_linordered_idom linordered_field_class.sign_simps(45) not_le) 
next
show "0 \<le> \<lbrakk>\<eta>\<rbrakk>\<^sub>t a \<longrightarrow> (\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> 0 \<le> \<lbrakk>\<eta>\<rbrakk>\<^sub>t c)"
proof(clarify)
fix c assume aHyp:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t a \<ge> 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a \<and> (\<forall>r\<in>{0..t}. G (F r))" 
using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "\<lbrakk>\<eta>\<rbrakk>\<^sub>t a = \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) \<ge> 0" using aHyp tcHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_vector_derivative 
\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "(\<forall>t\<ge>0. \<forall> xf \<in> set xfList. F t (\<partial> (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t))"
using tcHyp solves_store_ivpD(3) by blast
from this and tcHyp have "\<forall>r\<in>{0..t}. \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) =
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r)"
using diff_subst_prprty_4terms termVarsHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. \<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<langle>\<partial>\<^sub>t \<eta>\<rangle>\<rbrakk>\<^sub>t (F r) \<ge> 0" 
using solves_store_ivpD(2) tcHyp by (metis atLeastAtMost_iff)
ultimately have *:"\<forall>r\<in>{0..t}. \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) \<ge> 0" by (simp)
from obs2 and tcHyp have "\<forall>r\<in>{0..t}. ((\<lambda>s. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F s)) has_derivative 
(\<lambda>x. x *\<^sub>R (\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r)))) (at r within {0..t})" by (simp add: has_vector_derivative_def) 
hence "\<exists>r\<in>{0..t}. \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) - \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = t \<cdot> (\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r))" 
using mvt_very_simple and tcHyp by fastforce
then obtain r where "\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r) \<ge> 0 \<and> 0 \<le> r \<and> r \<le> t \<and> \<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F t) \<ge> 0
\<and> \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) - \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F 0) = t \<cdot> (\<lbrakk>\<partial>\<^sub>t \<eta>\<rbrakk>\<^sub>t (F r))" 
using * tcHyp by (meson atLeastAtMost_iff order_refl) 
thus "\<lbrakk>\<eta>\<rbrakk>\<^sub>t c \<ge> 0" 
using obs1 tcHyp by (metis cancel_comm_monoid_add_class.diff_cancel diff_ge_0_iff_ge 
diff_strict_mono linorder_neqE_linordered_idom linordered_field_class.sign_simps(45) not_le)  
qed
qed

lemma less_pval_to_tval:
assumes "\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P (\<theta> \<prec> \<eta>)\<restriction>\<rbrakk>\<^sub>P st"
shows "\<lbrakk>((map (vdiff\<circ>\<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<partial>\<^sub>t (\<eta> \<oplus> (\<ominus> \<theta>))\<rangle>\<rbrakk>\<^sub>t st \<ge> 0"
using assms by(auto)

lemma leq_pval_to_tval:
assumes "\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P (\<theta> \<preceq> \<eta>)\<restriction>\<rbrakk>\<^sub>P st"
shows "\<lbrakk>((map (vdiff\<circ>\<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<partial>\<^sub>t (\<eta> \<oplus> (\<ominus> \<theta>))\<rangle>\<rbrakk>\<^sub>t st \<ge> 0"
using assms by(auto)

lemma dInv_prelim:
assumes substHyp:"\<forall> st. G st \<longrightarrow>  (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P \<phi>\<restriction>\<rbrakk>\<^sub>P st"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
shows "\<lbrakk>\<phi>\<rbrakk>\<^sub>P a \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> \<lbrakk>\<phi>\<rbrakk>\<^sub>P c)"
proof(clarify)
fix c assume aHyp:"\<lbrakk>\<phi>\<rbrakk>\<^sub>P a" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a" using guarDiffEqtn_def by auto 
from aHyp propVarsHyp and substHyp show "\<lbrakk>\<phi>\<rbrakk>\<^sub>P c"
proof(induction \<phi>)
case (Eq \<theta> \<eta>)
hence hyp:"\<forall>st. G st \<longrightarrow>  (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow> 
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P (\<theta> \<doteq> \<eta>)\<restriction>\<rbrakk>\<^sub>P st" by blast
then have "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow> 
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<partial>\<^sub>t (\<theta> \<oplus> (\<ominus> \<eta>))\<rangle>\<rbrakk>\<^sub>t st = 0" by simp
also have "trmVars (\<theta> \<oplus> (\<ominus> \<eta>)) \<subseteq> UNIV - varDiffs" using Eq.prems(2) by simp
moreover have "\<lbrakk>\<theta> \<oplus> (\<ominus> \<eta>)\<rbrakk>\<^sub>t a = 0" using Eq.prems(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> \<lbrakk>\<theta> \<oplus> (\<ominus> \<eta>)\<rbrakk>\<^sub>t c = 0)"
using dInvForTrms_prelim listsHyp by blast
hence "\<lbrakk>\<theta> \<oplus> (\<ominus> \<eta>)\<rbrakk>\<^sub>t (F t) = 0" using tcHyp cHyp by simp
from this have "\<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t) = \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t)" by simp
also have "(\<lbrakk>\<theta> \<doteq> \<eta>\<rbrakk>\<^sub>P) c = (\<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t) = \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t))" using tcHyp by simp
ultimately show ?case by simp
next
case (Less \<theta> \<eta>)
hence "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow> 
0 \<le> (\<lbrakk>(map (vdiff \<circ> \<pi>\<^sub>1) xfList \<otimes> uInput)\<langle>\<partial>\<^sub>t (\<eta> \<oplus> (\<ominus> \<theta>))\<rangle>\<rbrakk>\<^sub>t) st" 
using less_pval_to_tval by metis
also from "Less.prems"(2)have "trmVars (\<eta> \<oplus> (\<ominus> \<theta>)) \<subseteq> UNIV - varDiffs" by simp
moreover have "\<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t a > 0" using "Less.prems"(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> \<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t c > 0)"
using dInvForProps_prelim(1) listsHyp by blast
hence "\<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t (F t) > 0" using tcHyp cHyp by simp
from this have "\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) > \<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t)" by simp
also have "\<lbrakk>\<theta> \<prec> \<eta>\<rbrakk>\<^sub>P c = (\<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t) < \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t))" using tcHyp by simp
ultimately show ?case by simp
next
case (Leq \<theta> \<eta>)
hence "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow> 
0 \<le> (\<lbrakk>(map (vdiff \<circ> \<pi>\<^sub>1) xfList \<otimes> uInput)\<langle>\<partial>\<^sub>t (\<eta> \<oplus> (\<ominus> \<theta>))\<rangle>\<rbrakk>\<^sub>t) st" using leq_pval_to_tval by metis
also from "Leq.prems"(2)have "trmVars (\<eta> \<oplus> (\<ominus> \<theta>)) \<subseteq> UNIV - varDiffs" by simp
moreover have "\<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t a \<ge> 0" using "Leq.prems"(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> \<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t c \<ge> 0)"
using dInvForProps_prelim(2) listsHyp by blast
hence "\<lbrakk>\<eta> \<oplus> (\<ominus> \<theta>)\<rbrakk>\<^sub>t (F t) \<ge> 0" using tcHyp cHyp by simp
from this have "(\<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t) \<ge> \<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t))" by simp
also have "\<lbrakk>\<theta> \<preceq> \<eta>\<rbrakk>\<^sub>P c = (\<lbrakk>\<theta>\<rbrakk>\<^sub>t (F t) \<le> \<lbrakk>\<eta>\<rbrakk>\<^sub>t (F t))" using tcHyp by simp
ultimately show ?case by simp
next
case (And \<phi>1 \<phi>2)
then show ?case by(simp)
next
case (Or \<phi>1 \<phi>2)
from this show ?case by auto
qed
qed

theorem dInv:
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P \<phi>\<restriction>\<rbrakk>\<^sub>P st"
and termVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
and phi_p:"P = \<lbrakk>\<phi>\<rbrakk>\<^sub>P"
shows "PRE P (ODEsystem xfList with G) POST P"
proof(clarsimp)
fix a b
assume "(a, b) \<in> \<lceil>P\<rceil>"
from this have aHyp:"a = b \<and> P a" by (metis (full_types) d_p2r rdom_p2r_contents)
have "P a \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> P c)"
using assms dInv_prelim by metis 
from this and aHyp have "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> P c" by blast
thus "(a, b) \<in> wp (ODEsystem xfList with G ) \<lceil>P\<rceil>"
using aHyp by (simp add: boxProgrPred_chrctrztn) 
qed

theorem dInvFinal:
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lparr>set xfList\<rparr>) \<longrightarrow> st (\<partial> str) = 0) \<longrightarrow>
\<lbrakk>((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<restriction>\<partial>\<^sub>P \<phi>\<restriction>\<rbrakk>\<^sub>P st"
and termVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map tval uInput"
and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>F\<rceil> \<and> \<lceil>F\<rceil> \<subseteq> \<lceil>Q\<rceil>"
and phi_f:"F = \<lbrakk>\<phi>\<rbrakk>\<^sub>P"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac C="\<lbrakk>\<phi>\<rbrakk>\<^sub>P" in dCut)
apply(subgoal_tac "\<lceil>F\<rceil> \<subseteq> wp (ODEsystem xfList with G) \<lceil>F\<rceil>", simp)
using impls and phi_f apply blast
apply(subgoal_tac "PRE F (ODEsystem xfList with G) POST F", simp)
apply(rule_tac \<phi>="\<phi>" and uInput="uInput" in dInv)
prefer 5 apply(subgoal_tac "PRE P (ODEsystem xfList with (\<lambda>s. G s \<and> F s)) POST Q", simp add: phi_f)
apply(rule dWeakening)
using impls apply simp
using assms by simp_all

end