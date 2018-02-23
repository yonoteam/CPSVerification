theory VC_diffKAD1
imports
Main
"HOL.Transcendental"
"afpModified/VC_KAD"
"Ordinary_Differential_Equations/IVP/Initial_Value_Problem"
(*"HOL-Analysis.Henstock_Kurzweil_Integration" (* <- Fundamental Theorem of Calculus here *)*)
(*"../afp-2017-10-18/thys/Ordinary_Differential_Equations/IVP/Initial_Value_Problem"*)
(*"../afp-2017-10-18/thys/Algebraic_VCs/AVC_KAD/VC_KAD"*)

begin
-- "Notation."
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
no_notation Archimedean_Field.floor ("\<lfloor>_\<rfloor>")
no_notation Set.image (" ` ")
no_notation Range_Semiring.antirange_semiring_class.ars_r ("r")

notation p2r ("\<lceil>_\<rceil>")
notation r2p ("\<lfloor>_\<rfloor>")
notation Set.image("_\<lbrakk>_\<rbrakk>")
notation Product_Type.prod.fst ("\<pi>\<^sub>1")
notation Product_Type.prod.snd ("\<pi>\<^sub>2")
notation rel_ad ("\<Delta>\<^sup>c\<^sub>1")

-- "Preliminary lemmas."
(* Observations *)
thm p2r_def
thm r2p_def
thm rel_ad_def
term "Set.Collect" (* p2s *)
term "Domain R"    (* r2s *)
thm fbox_def       (* wp  *)
thm rel_antidomain_kleene_algebra.fbox_def

lemma rel_ad_chrctrztn:"\<Delta>\<^sup>c\<^sub>1 R = Id - (\<lceil>\<lambda> x. x \<in> (\<pi>\<^sub>1\<lbrakk>R\<rbrakk>)\<rceil>)"
by(simp add: p2r_def image_def fst_def rel_ad_def, fastforce)

lemma boxProgrPred_IsProp: "wp R \<lceil>P\<rceil> \<subseteq> Id"
by (simp add: rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def)

lemma rdom_p2r_contents[simp]:"(a, b) \<in> rdom \<lceil>P\<rceil> = ((a = b) \<and> P a)" 
proof-
have "(a, b) \<in> rdom (p2r P) = ((a = b) \<and> (a, a) \<in> rdom (p2r P))" using p2r_subid by fastforce 
also have "((a = b) \<and> (a, a) \<in> rdom (p2r P)) = ((a = b) \<and> (a, a) \<in> (p2r P))" by simp
also have "((a = b) \<and> (a, a) \<in> (p2r P)) = ((a = b) \<and> P a)" by (simp add: p2r_def) 
ultimately show ?thesis by simp
qed

(* Should not add these "complement_rule's" to simp... *)
lemma complement_rule1: "(x,x) \<notin> \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> \<Longrightarrow> P x"
  by (auto simp: rel_ad_def p2r_subid p2r_def)

lemma complement_rule2: "(x,x) \<in> \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> \<Longrightarrow> \<not> P x"
by (metis ComplD VC_KAD.p2r_neg_hom complement_rule1 empty_iff mem_Collect_eq p2s_neg_hom 
rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.am1 relcomp.relcompI)

lemma complement_rule3: "R \<subseteq> Id \<Longrightarrow> (x,x) \<notin> R \<Longrightarrow> (x,x) \<in> \<Delta>\<^sup>c\<^sub>1 R"
by (metis IdI Un_iff d_p2r rel_antidomain_kleene_algebra.addual.ars3 
rel_antidomain_kleene_algebra.addual.ars_r_def rpr)

lemma complement_rule4: "(x,x) \<in> R \<Longrightarrow> (x,x) \<notin> \<Delta>\<^sup>c\<^sub>1 R"
by (metis empty_iff rel_antidomain_kleene_algebra.addual.ars1 relcomp.relcompI)

lemma boxProgrPred_chrctrztn:"(x,x) \<in> wp R \<lceil>P\<rceil> = (\<forall> y. (x,y) \<in> R \<longrightarrow> P y)"
by (metis boxProgrPred_IsProp complement_rule1 complement_rule2 complement_rule3 
complement_rule4 d_p2r wp_simp wp_trafo)

lemma boxProgrRel_chrctrztn1:"P \<subseteq> Id \<Longrightarrow> (x,x) \<in> wp R P = (\<forall> y. (x,y) \<in> R \<longrightarrow> \<lfloor>P\<rfloor> y)"
by (metis boxProgrPred_chrctrztn rpr)

lemma boxProgrRel_chrctrztn2:"x \<in> r2s (wp R P) = (\<forall>y. (x, y) \<in> R \<longrightarrow> \<lfloor>P\<rfloor> y)"
apply(auto simp: r2p_def rel_antidomain_kleene_algebra.fbox_def rel_ad_def)
subgoal by blast
subgoal by blast
done

-- {* dL CALCULUS. *}

(*  When people specify an initial value problem (IVP) like:
       x' = f(t,x)    x(0) = x\<^sub>0 \<in> \<real>\<^sup>n
    They are assuming many things and abusing notation strongly. Formally, the following holds:
       f:\<real>\<^sup>n\<^sup>+\<^sup>1\<rightarrow>\<real>\<^sup>n (or f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n) and x:\<real>\<rightarrow>\<real>\<^sup>n, hence x':\<real>\<rightarrow>\<real>\<^sup>n such that 
       x'=f\<circ>(id,x) (alternatively, x'= (\<lambda>s.f s (x s))) where
       (id,x):t\<mapsto>(t, \<pi>\<^sub>1(x(t)), \<pi>\<^sub>2(x(t)),\<dots>,\<pi>\<^sub>n(x(t))) and \<pi>\<^sub>i is the ith projection.*)
definition solves_ivp :: "(real \<Rightarrow> 'a::banach) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 
real set \<Rightarrow> 'a set \<Rightarrow> bool" 
("solvesTheIVP: D _ = _ withInitCond  _ \<mapsto> _" [70, 70, 70, 70] 68) where
"(solvesTheIVP: D x = f withInitCond t0 \<mapsto> x0) Domf Codf \<equiv> (x solves_ode f) Domf Codf \<and> x t0 = x0"

lemma solves_ivpI:
assumes "(x solves_ode f) A B"
assumes "x t0 = x0"
shows "(solvesTheIVP: D x = f withInitCond t0 \<mapsto> x0) A B"
using assms by (simp add: solves_ivp_def)

lemma solves_ivpD:
assumes "(solvesTheIVP: D x = f withInitCond t0 \<mapsto> x0) A B"
shows "(x solves_ode f) A B"
and "x t0 = x0"
using assms by (auto simp: solves_ivp_def)

theorem(in unique_on_bounded_closed) ivp_unique_solution:
assumes xIsSol:"(solvesTheIVP: D x = f withInitCond t0 \<mapsto> x0) T X"
assumes yIsSol:"(solvesTheIVP: D y = f withInitCond t0 \<mapsto> x0) T X"
shows "\<forall> t \<in> T. x t = y t"
proof
fix t assume "t \<in> T"
from this and assms show "x t = y t" 
using unique_solution solves_ivp_def by blast 
qed

(* Observations *)
term "closed_segment a (b::real)"
term "open_segment a b"

(* In our store implementation:
    · The solution "x:\<real>\<rightarrow>\<real>\<^sup>n" is changed for "F::real \<Rightarrow> real store" (i.e. real \<Rightarrow> string \<Rightarrow> real).
      The letter "x" is reserved for strings.
    · Instead of "f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n)" we use "f::real store \<Rightarrow> real". This is for consistency with the
      "expressions" in assignments in VC_KAD.thy and because we mainly focus on "autonomous systems
      of ODE'S (i.e. systems of the form x'(t)=f(x(t))). *)
definition solvesStoreIVP :: 
"(real \<Rightarrow> real store) \<Rightarrow> string \<Rightarrow> (real store \<Rightarrow> real) \<Rightarrow> real store \<Rightarrow> (real store pred) \<Rightarrow> bool" 
("(_ solvesTheStoreIVP: D _ = _ withInitState _ andGuard _)" [70, 70, 70, 70, 70] 68) where
"(F solvesTheStoreIVP: D x = f withInitState st andGuard G) \<equiv> 
  (F 0 = st) \<and> 
  (\<forall> s \<ge> 0. \<forall> t \<in> {0 -- s}. G (F t) \<and> (\<forall> y. y\<noteq>x \<longrightarrow> F t y = st y)) \<and>
  (\<forall> s \<ge> 0. (solvesTheIVP: D (\<lambda> t. F t x) = (\<lambda> t. \<lambda> r. f (F t)) withInitCond 0 \<mapsto> (st x)) {0 -- s} UNIV)"

definition guarDiffEqtn :: "string \<Rightarrow> (real store \<Rightarrow> real) \<Rightarrow> (real store pred) \<Rightarrow> 
real store rel" ("D [ _ ] = _ with _ " [70, 70, 70] 61) where
"D [x] = f with G = {(st,(F::real \<Rightarrow> real store) t) |st t F. t \<ge> 0 \<and> solvesStoreIVP F x f st G}"

-- "Differential Weakening."
(* Sketch of dW's proof: 
    \<pi>\<^sub>2[\<alpha>] \<subseteq> \<phi> \<Longrightarrow> (\<alpha> \<circ> \<phi>\<^sup>C) = \<emptyset> \<Longleftrightarrow> Univ = (\<alpha> \<circ> \<phi>\<^sup>C)\<^sup>C = \<not> <\<alpha>> \<not> \<phi>  = [\<alpha>] \<phi> *)
lemma dEvolutionImpliesGuard:"\<pi>\<^sub>2\<lbrakk>D [ x ] = f with G\<rbrakk> \<subseteq> p2s G"
  by (auto simp: guarDiffEqtn_def solvesStoreIVP_def)

lemma relAdNullComposIfCodSubset:"\<pi>\<^sub>2\<lbrakk>R\<rbrakk> \<subseteq> p2s P \<Longrightarrow> R ; \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> = {}"
  by (auto simp: p2r_def p2r_subid rel_ad_def)

theorem dWeakening: 
assumes guardImpliesPost: "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE P (D[x] = f with G) POST Q"
proof-
  have "\<pi>\<^sub>2\<lbrakk>D [ x ] = f with G\<rbrakk> \<subseteq> p2s Q" using
  guardImpliesPost dEvolutionImpliesGuard
    by (metis (mono_tags, lifting) contra_subsetD impl_prop mem_Collect_eq subsetI) 
  then have "(D[x] = f with G) ; \<Delta>\<^sup>c\<^sub>1 \<lceil>Q\<rceil> = {}" 
    by (meson relAdNullComposIfCodSubset)
  from this show ?thesis
    by (simp add: p2r_subid rel_antidomain_kleene_algebra.addual.bbox_def) 
qed

(* Example of hybrid program verified with differential weakening. *)  
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> s. s ''x'' + 1) with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
using dWeakening by simp
      
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> s. s ''x'' + 1) with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
apply(clarify, simp add: p2r_def)
apply(simp add: rel_ad_def rel_antidomain_kleene_algebra.addual.ars_r_def)
apply(simp add: rel_antidomain_kleene_algebra.fbox_def)
apply(simp add: relcomp_def rel_ad_def guarDiffEqtn_def solvesStoreIVP_def)
apply(auto)
done

-- "Differential Cut."
lemma condAfterEvol_remainsAlongEvol:
  assumes boxDiffC:"(a, a) \<in> wp (D [ x ] = f with G) \<lceil>C\<rceil>"
  assumes FisSol:"(F solvesTheStoreIVP: D x = f withInitState a andGuard G)"
  shows "(F solvesTheStoreIVP: D x = f withInitState a andGuard (\<lambda>s. G s \<and> C s))"
  apply(simp add: solvesStoreIVP_def, safe)
  subgoal using FisSol solvesStoreIVP_def by simp
  subgoal using FisSol solvesStoreIVP_def by simp
  subgoal proof-
  from boxDiffC have diffHyp:"\<forall> c. (a,c) \<in> (D [ x ] = f with G) \<longrightarrow> C c"
  using guarDiffEqtn_def wp_trafo by (metis (no_types, lifting) Domain.intros r2p_def)
  fix s t::real
  assume "0 \<le> s" and "t \<in> {0 -- s}"
  hence "(a,F t) \<in> (D [ x ] = f with G)" 
  using closed_segment_eq_real_ivl FisSol guarDiffEqtn_def by auto 
  then show "C (F t)" using diffHyp by blast  
  qed
  subgoal using FisSol solvesStoreIVP_def by simp
  subgoal using FisSol solvesStoreIVP_def by simp
  done

lemma boxDiffCond_impliesAllTimeInCond:
  assumes allTime: "(t::real)\<ge> 0"
  assumes boxDifCond:"(a,a) \<in> wp (D [ x ] = f with G) \<lceil>C\<rceil>"
  assumes FisSol:"(F solvesTheStoreIVP: D x = f withInitState a andGuard G)"
  shows "(a,F t) \<in> (D [ x ] = f with (\<lambda>s. G s \<and> C s))"
  apply(simp add: guarDiffEqtn_def)
  apply(rule_tac x="t" in exI, rule_tac x="F" in exI, simp add: allTime)
  apply(rule condAfterEvol_remainsAlongEvol)
  using boxDifCond guarDiffEqtn_def FisSol by safe

theorem dCut: 
  assumes pBoxDiffCut:"(PRE P (D[x] = f with G) POST C)"
  assumes pBoxCutQ:"(PRE P (D[x] = f with (\<lambda> s. G s \<and> C s)) POST Q)"
  shows "PRE P (D[x] = f with G) POST Q"
proof(clarify)
  fix a b::"real store" assume abHyp:"(a,b) \<in> rdom \<lceil>P\<rceil>"
  from this have "a = b \<and> P a" by (metis rdom_p2r_contents)
  from this abHyp and pBoxDiffCut have "(a,a) \<in> wp (D [ x ] = f with G) \<lceil>C\<rceil>" by blast
  moreover from pBoxCutQ and abHyp have "\<forall> c. (a,c) \<in> (D [ x ] = f with (\<lambda>s. G s \<and> C s)) \<longrightarrow> Q c"
    by (metis (no_types, lifting) \<open>a = b \<and> P a\<close> boxProgrPred_chrctrztn set_mp)
  ultimately have "\<forall> c. (a,c) \<in> (D [ x ] = f with G) \<longrightarrow> Q c" using
      guarDiffEqtn_def boxDiffCond_impliesAllTimeInCond by auto
  from this and \<open>a = b \<and> P a\<close> show "(a,b) \<in> wp (D [ x ] = f with G) \<lceil>Q\<rceil>" 
    by (simp add: boxProgrPred_chrctrztn)
qed 

-- "Solve Differential Equation."
(* The rule "dSolve" requires an input from the user, i.e. the unique solution of the ODE
x::"real \<Rightarrow> (real store) \<Rightarrow> real". For that reason, in this section the Isabelle-variable
"xvar" represents the string, while "x" is the user input. *)
lemma prelim_dSolve:
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real"
assumes xIsSolutionOnA:"solvesStoreIVP (\<lambda> t. a(xvar := (x t a))) xvar f a G"
assumes uniqOnA:"\<forall> X. solvesStoreIVP X xvar f a G \<longrightarrow> (\<forall> t \<ge> 0. a(xvar := (x t a))= X t)"
assumes guardPreservedImpliesPost: 
"(\<forall>t\<ge>0. (\<forall>r \<in> {0 -- t}. G (a(xvar := (x r a)))) \<longrightarrow> (\<forall> c. (a,c) \<in> (xvar ::= x t) \<longrightarrow> Q c))"
shows "\<forall> c. (a,c) \<in> (D [ xvar ] = f with G) \<longrightarrow> Q c"
proof(clarify)
fix c assume "(a,c) \<in> (D [ xvar ] = f with G)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xvar f a G" using guarDiffEqtn_def by auto 
from this and uniqOnA have "(\<lambda> r. a(xvar := (x r a))) t = F t" by blast
hence eq1:"F t xvar = (a(xvar := (x t a))) xvar" by simp
moreover have "\<forall>s\<ge>0.(\<forall>r \<in> {0 -- s}. \<forall>str. str \<noteq> xvar \<longrightarrow> F r str = a str)" 
using FHyp solvesStoreIVP_def by simp
then have eq2:"\<forall>str. str \<noteq> xvar \<longrightarrow> F t str = a str" using FHyp by blast
ultimately have "F t = a (xvar := x t a)" by auto
then have "(a, F t) \<in> (xvar ::= x t)" using gets_def by blast 
thus "Q c" using xIsSolutionOnA guardPreservedImpliesPost FHyp
by (metis solvesStoreIVP_def) 
qed

theorem dSolve:
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real"
assumes xSolves:"\<forall> st. solvesStoreIVP (\<lambda> t. st(xvar := (x t st))) xvar f st G"
assumes solIsUniq:"\<forall> st. \<forall> X. solvesStoreIVP X xvar f st G \<longrightarrow> (\<forall> t \<ge> 0. st(xvar := (x t st)) = X t)"
assumes diffAssgn:
"\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r \<in> {0 -- t}. G (st(xvar := x r st))) \<longrightarrow> \<lfloor>wp (xvar ::= x t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (D[xvar] = f with G) POST Q" 
proof
fix pair assume "pair \<in> rdom \<lceil>P\<rceil>" 
from this obtain a::"real store" where aHyp:"pair = (a,a) \<and> P a" 
by (metis IdE contra_subsetD d_p2r p2r_subid rdom_p2r_contents)
from xSolves have pre1:"solvesStoreIVP (\<lambda> t. a(xvar := (x t a))) xvar f a G" by simp
from this have pre2:"\<forall> X. solvesStoreIVP X xvar f a G \<longrightarrow> (\<forall> t \<ge> 0. a(xvar := (x t a))= X t)" 
using solIsUniq by metis
from diffAssgn and aHyp have pre3: "(\<forall>t\<ge>0. (\<forall>r \<in> {0 -- t}. G (a(xvar := (x r a)))) \<longrightarrow> 
(\<forall> c. (a,c) \<in> (xvar ::= x t) \<longrightarrow> Q c))" by (metis wp_trafo)
from pre1 pre2 and pre3 have "\<forall> c. (a,c) \<in> (D [ xvar ] = f with G) \<longrightarrow> Q c" by (rule prelim_dSolve)
thus "pair \<in> wp (D [ xvar ] = f with G ) (p2r Q)" by (simp add: aHyp boxProgrPred_chrctrztn)
qed

(* OBSERVATIONS *)
term "unique_on_bounded_closed t0 T x0 f X L"
thm unique_on_bounded_closed_def
thm unique_on_bounded_closed_axioms_def
thm unique_on_closed_def

lemma condsForUniqSol:
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real" and F::"real \<Rightarrow> real store" and f::"real store \<Rightarrow> real"
assumes sHyp:"s \<ge> 0"
assumes contHyp:"continuous_on ({0--s} \<times> UNIV) (\<lambda>(t, (r::real)). f (a(xvar := x t a)))"
shows "unique_on_bounded_closed 0 {0--s} (a xvar) (\<lambda>t r. f (a(xvar := (x t a)))) 
UNIV (if s = 0 then 1 else 1/(s+1))"
apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def 
unique_on_closed_def compact_interval_def compact_interval_axioms_def nonempty_set_def 
interval_def self_mapping_def self_mapping_axioms_def closed_domain_def global_lipschitz_def 
lipschitz_def, safe)
subgoal using contHyp continuous_rhs_def by auto
subgoal using contHyp continuous_rhs_def by auto
using closed_segment_eq_real_ivl sHyp by auto

lemma ubcStoreUniqueSol:
fixes x:: "real \<Rightarrow> (real store) \<Rightarrow> real"
assumes sHyp:"s \<ge> 0"
assumes contHyp:"continuous_on ({0--s} \<times> UNIV) (\<lambda>(t, (r::real)). f (a(xvar := x t a)))"
assumes eqDerivs:"\<forall> t \<in>{0--s}. f (F t) = f (a(xvar := (x t a)))"
assumes Fsolves:"solvesStoreIVP F xvar f a G"
assumes xSolves:"solvesStoreIVP (\<lambda> t. a(xvar := (x t a))) xvar f a G"
shows "(a(xvar := x s a)) = F s"
proof
  fix str::"string" show "(a(xvar := x s a)) str = F s str"
  proof(cases "str=xvar")
  case False
    then have notXvar:"str \<noteq> xvar" by simp
    from xSolves have "\<forall>s\<ge>0. \<forall>t\<in>{0--s}. \<forall>str. str \<noteq> xvar \<longrightarrow> (a(xvar := (x t a))) str = a str"
    by (simp add: solvesStoreIVP_def) 
    hence 1:"(a(xvar := (x s a))) str = a str" using sHyp notXvar by blast
    from Fsolves have "\<forall>s\<ge>0. \<forall>t\<in>{0--s}. \<forall>str. str \<noteq> xvar \<longrightarrow> F t str = a str" 
    by (simp add: solvesStoreIVP_def) 
    then have 2:"F s str = a str" using sHyp notXvar by blast
    thus "(a(xvar := x s a)) str = F s str" using 1 and 2 by simp
  next case True
    then have strIsXvar:"str = xvar" by simp
    (* Expand hypothesis for arbitrary solution. *)
    from Fsolves and sHyp have "solves_ivp (\<lambda>t. F t xvar) (\<lambda>t r. f (F t)) 0 (a xvar) {0--s} UNIV" 
    by (simp add: solvesStoreIVP_def)
    then have "((\<lambda>t. F t xvar) solves_ode (\<lambda>t r. f (F t))){0--s} UNIV \<and> F 0 xvar = a xvar" 
    by (simp add: solves_ivp_def)
    (* Re-express hypothesis for arbitrary solution in terms of connection.*)
    hence "((\<lambda>t. F t xvar) solves_ode (\<lambda>t r. f (a(xvar := (x t a))))){0--s} UNIV \<and> 
    F 0 xvar = a xvar" by (auto simp: solves_ode_def eqDerivs)
    then have 1:"solves_ivp (\<lambda>t. F t xvar) (\<lambda>t r. f (a(xvar := (x t a)))) 0 (a xvar) {0--s} UNIV"
    by (simp add: solves_ivp_def)
    (* Expand hypothesis for user's solution. *)
    from xSolves have 2:"solves_ivp (\<lambda>t. x t a) (\<lambda>t r. f (a(xvar := (x t a)))) 0 (a xvar) {0--s} UNIV"
    by (simp add: solvesStoreIVP_def sHyp)
    (* Show user's solution and arbitrary solution are the same. *)
    from sHyp and contHyp have 3:"unique_on_bounded_closed 0 {0--s} (a xvar) 
    (\<lambda>t r. f (a(xvar := (x t a)))) UNIV (if s = 0 then 1 else 1/(s+1))" using condsForUniqSol by simp
    from 1 2 and 3 have "F s xvar = x s a"
    using unique_on_bounded_closed.ivp_unique_solution by blast 
    thus "(a(xvar := x s a)) str = F s str" using strIsXvar by simp 
  qed
  qed

theorem dSolveUBC:
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real"
assumes contHyp:"\<forall> st. \<forall> r \<ge> 0. continuous_on ({0--r} \<times> UNIV) (\<lambda>(t, (s::real)). f (st(xvar := x t st)))"
assumes xSolves:"\<forall> st. solvesStoreIVP (\<lambda> t. st(xvar := (x t st))) xvar f st G"
assumes solIsUniq:
"\<forall> st. \<forall> X. solvesStoreIVP X xvar f st G \<longrightarrow> (\<forall> t \<ge> 0. f (X t) = f (st(xvar := (x t st))))"
assumes diffAssgn:
"\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r \<in> {0 -- t}. G (st(xvar := x r st))) \<longrightarrow> \<lfloor>wp (xvar ::= x t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (D[xvar] = f with G) POST Q"
apply(rule_tac x="x" in dSolve)
subgoal using xSolves by simp
subgoal proof(clarify)
fix a::"real store" and X::"real \<Rightarrow> real store" and s::"real"
assume XisSol:"solvesStoreIVP X xvar f a G" and sHyp:"0 \<le> s"
from this and solIsUniq have "\<forall> t \<in> {0--s}. f (X t) = f (a(xvar := (x t a)))" 
by(simp add: closed_segment_eq_real_ivl) (* This equivalence helps Isabelle a lot. *)
moreover have "continuous_on ({0--s} \<times> UNIV) (\<lambda>(t, (r::real)). f (a(xvar := x t a)))"
using contHyp and sHyp by blast
moreover from xSolves have "solvesStoreIVP (\<lambda> t. a(xvar := (x t a))) xvar f a G" by simp
ultimately show "(a(xvar := x s a)) = X s" using sHyp XisSol ubcStoreUniqueSol by simp
qed
subgoal using diffAssgn by simp
done

(* OBSERVATIONS *)
thm derivative_intros(173)
thm derivative_intros
thm derivative_intros(176)
thm derivative_eq_intros(22)
thm derivative_eq_intros
thm continuous_intros

(* Example of hybrid program verified with differential weakening. *)  
lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (D[''pos''] = (\<lambda> s. s ''vel'') with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
apply(rule_tac x ="(\<lambda> t. \<lambda> s. s ''vel'' \<cdot> t + s ''pos'')" in dSolveUBC) (* 4 goal appear. *)
subgoal by (clarsimp, rule continuous_intros)
subgoal
apply(simp add: solvesStoreIVP_def solves_ivp_def solves_ode_def,clarify)
  apply(rule_tac f'1="\<lambda> x. st ''vel''" and g'1="\<lambda> x. 0" in derivative_intros(173))(* 3 goals appear. *)
  apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))           (* 3 goals appear. *)
  by(auto intro: derivative_intros)
subgoal by(simp add: solvesStoreIVP_def)
subgoal 
  apply(clarsimp, simp add: p2r_def r2p_def)
  by(simp add: Domain_iff add_strict_increasing2)
done

-- "Differential Invariant."
(* So the problem here is that we need to define the following operation over real-store-predicates:
  D(f=g) \<equiv> D(f)=D(g)      D(f<g)\<equiv>D(f)\<le>D(g)      D(f\<le>g)\<equiv>D(f)\<le>D(g)
  D(\<not>P) \<equiv> D(P)            D(P\<and>Q)\<equiv>D(P)\<and>D(Q)      D(P\<or>Q)\<equiv>D(P)\<and>D(Q)
   So that we have in isabelle the following theorem:
          P,G \<turnstile> Q        G \<turnstile>[x'::=f(x)]D(Q)
        ------------------------------------dInv
              P \<turnstile> [x' = f(x) & G]Q

   I have thought of two solutions and a wishful-solution:
    1. Define inductive datatypes that allow me to define my operation on them. Then use them to
    prove the rule, and later on add syntax theorems so that the user does not experience the 
    datatype.
    2. Prove the dInv rule for each one of the possible cases. Then make a general case that 
    invoques all of these rules.
    3. (Wishful) Magically, some Isabelle command/theorem lets me do what I want easily, for example 
    typedef or function, which reduces my problem to just proving properties...

    IN THIS VERSION WE ARE GOING TO TRY THE FIRST (1) APPROACH
*)
definition stringDiff ::"string \<Rightarrow> string" ("vdiff _" [99] 100) where
"vdiff x = ''d''@x"

datatype trms = Const real | Var string | Inv trms | Sum trms trms | Mult trms trms

primrec rval ::"trms \<Rightarrow> (real store \<Rightarrow> real)" where
"rval (Const r) = (\<lambda> s. r)"|
"rval (Var x) = (\<lambda> s. s x)"|
"rval (Inv \<theta>) = (\<lambda> s. 1/(rval \<theta> s))"|
"rval (Sum \<theta> \<eta>) = (\<lambda> s. rval \<theta> s + rval \<eta> s)"|
"rval (Mult \<theta> \<eta>) = (\<lambda> s. rval \<theta> s \<cdot> rval \<eta> s)"

datatype props = Eq trms trms | Less trms trms | Neg props | And props props | Or props props

primrec pval ::"props \<Rightarrow> (real store \<Rightarrow> bool)" where
"pval (Eq \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s = (rval \<eta>) s)"|
"pval (Less \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s < (rval \<eta>) s)"|
"pval (Neg \<phi>) = (\<lambda> s. \<not> (pval \<phi>) s)"|
"pval (And \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<and> (pval \<psi>) s)"|
"pval (Or \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<or> (pval \<psi>) s)"

primrec rdiff ::"trms \<Rightarrow> (real store \<Rightarrow> real)" where
"rdiff (Const r) = (\<lambda> s. 0)"|
"rdiff (Var x) = (\<lambda> s. s (vdiff x))"|
"rdiff (Inv \<theta>) = (\<lambda> s. - (rdiff \<theta>) s \<cdot> (rval (Inv (Mult \<theta> \<theta>))) s)"|
"rdiff (Sum \<theta> \<eta>) = (\<lambda> s. (rdiff \<theta>) s + (rdiff \<eta>) s)"|
"rdiff (Mult \<theta> \<eta>) = (\<lambda> s. ((rdiff \<theta>) s \<cdot> (rval \<eta>) s) + ((rval \<theta>) s \<cdot> (rdiff \<eta>) s))"

value "rval (Sum (Mult (Var ''x'') (Const c)) (Inv (Var ''y'')))"
value "rdiff (Sum (Mult (Var ''x'') (Const c)) (Inv (Var ''y'')))"
value "rval (Sum (Mult (Var ''y'') (Inv (Var ''x''))) (Const c) )"
value "rdiff (Sum (Mult (Var ''y'') (Inv (Var ''x''))) (Const c) )"

primrec pdiff ::"props \<Rightarrow> (real store \<Rightarrow> bool)" where
"pdiff (Eq \<theta> \<eta>) = (\<lambda> s. (rdiff \<theta>) s = (rdiff \<eta>) s)"|
"pdiff (Less \<theta> \<eta>) = (\<lambda> s. (rdiff \<theta>) s < (rdiff \<eta>) s \<or> (rdiff \<theta>) s = (rdiff \<eta>) s)"|
"pdiff (Neg \<phi>) = (\<lambda> s. (pdiff \<phi>) s)"|
"pdiff (And \<phi> \<psi>) = (\<lambda> s. (pdiff \<phi>) s \<and> (pdiff \<psi>) s)"|
"pdiff (Or \<phi> \<psi>) = (\<lambda> s. (pdiff \<phi>) s \<and> (pdiff \<psi>) s)"

value "pval (Eq (Mult (Var ''x'') (Const c)) (Sum (Var ''y'') (Var ''z'')))"
value "pdiff (Eq (Mult (Var ''x'') (Const c)) (Sum (Var ''y'') (Var ''z'')))"
value "(pval (Less (Var ''x'') (Var ''z''))) (\<lambda> str. if str = ''x'' then 0 else 1)"
value "(pdiff (Less (Var ''x'') (Var ''z''))) (\<lambda> str. if str = ''x'' then 0 else 1)"
value "pval (And (Or (Less (Var ''x'') (Const c)) (Less (Const c) (Var ''x''))) 
                (Neg (Eq (Mult (Var ''x'') (Const c)) (Sum (Inv (Var ''y'')) (Var ''z'')))))"
value "pdiff (And (Or (Less (Var ''x'') (Const c)) (Less (Const c) (Var ''x''))) 
                (Neg (Eq (Mult (Var ''x'') (Const c)) (Sum (Inv (Var ''y'')) (Var ''z'')))))"

typedef realStoreTerm = "{f :: real store \<Rightarrow> real. \<exists> \<theta>. rval \<theta> = f}"
  by auto

typedef realStorePred = "{P :: real store \<Rightarrow> bool. \<exists> \<phi>. pval \<phi> = P}"
  by auto

(* Prove Platzer's derivation lemmas 5 and 6... *)
  
lemma
fixes f::"realStoreTerm"
assumes "rval \<eta> = (Rep f)"
assumes "\<forall> c. rdiff \<eta> c = 0"
shows "(Rep f) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (D [x] = (Rep f) with (\<lambda> s. True)) \<longrightarrow> (Rep f) c = 0)"
proof(clarify)
fix c assume fHyp:"Rep f a = 0" and "(a, c) \<in> D [ x ] = Rep f with (\<lambda>s. True)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" where 
FHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F x (Rep f) a (\<lambda> s. True)" using guarDiffEqtn_def by auto
then show "Rep f c = 0"
proof(cases "t=0")
case True
then have "F t = a" using solvesStoreIVP_def FHyp by blast 
thus ?thesis using fHyp FHyp by simp
next
case False hence tHyp:"t > 0" using FHyp by simp
from FHyp have "((\<lambda>t. F t x) has_vderiv_on (\<lambda>t. (Rep f) (F t))) {0 -- t}"
by (simp add: solvesStoreIVP_def solves_ivp_def solves_ode_def)
then show ?thesis sorry
qed
qed

lemma 
assumes "\<forall> c. (a,c) \<in> ((''d''@x) ::= f) \<longrightarrow> (\<lambda> s. s (''d''@y)) c = 0"
shows "(\<lambda> s. s y) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (D [x] = f with (\<lambda> s. s = s)) \<longrightarrow> (\<lambda> s. s y) c = 0)"
proof(clarify)
fix c assume "a y = 0" and cHyp:"(a, c) \<in> D [ x ] = f with (\<lambda>s. s = s)"
from this show "c y = 0"
proof(cases "y=x")
case True
then have "a x = 0" using \<open>a y = 0\<close> by blast 
from cHyp have "c = a ((''d''@x) := f a)" sorry
hence "(a,c) \<in> ((''d''@x) ::= f)" by (simp add: gets_def)
from this and assms have "c (''d''@y) = 0" by simp
hence "c (''d''@x) = 0" using \<open>y=x\<close> by simp
show ?thesis sorry
next
case False
then show ?thesis sorry
qed
qed


lemma pelim_dInv:
assumes "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE Q (D [x] = f with G) POST Q"
sorry

theorem dInv:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st x" (* Notice that the conjunction below is not valid. *)
assumes "PRE G ((''d''@x) ::= f) POST (\<lambda> s. Q s (''d''@x))"
shows " PRE P (D [x] = f with G) POST (\<lambda> s. Q s x)"
proof(clarify)
fix a b assume "(a, b) \<in> rdom \<lceil>P\<rceil>"
from this have "a = b \<and> P a" by (metis rdom_p2r_contents)
have "\<forall> c. (a,c) \<in> (D [ x ] = f with G) \<longrightarrow> Q c x"
proof(clarify)
fix c assume "(a, c) \<in> D [ x ] = f with G"
show "Q c x"
sorry
qed
thus "(a, b) \<in> wp (D [ x ] = f with G ) \<lceil>\<lambda>s. Q s x\<rceil>" sorry
qed


theorem dInv2:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st x" (* Notice that the conjunction below is not valid. *)
assumes "PRE (\<lambda> s. P s \<and> G s) ((''d''@x) ::= f) POST (\<lambda> s. Q s (''d''@x))"
shows " PRE P (D [x] = f with G) POST (\<lambda> s. Q s x)"
sorry

theorem dInv3:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st"
assumes "PRE G ((''d''@x) ::= f) POST (deriv_Pred Q)"
shows " PRE P (D [x] = f with G) POST Q"
sorry

lemma "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      ((D[''x''] = (\<lambda> s. s ''v'') with (\<lambda> s. True)))
      POST (\<lambda> s. s ''x''> 0)"
      apply(rule_tac C = "\<lambda> s. s ''v'' > 0" in dCut)
      apply(rule dInv)
      subgoal by simp
      apply(simp)
      defer
      apply(rule_tac C = "\<lambda> s. s ''x'' > 0" in dCut)
      apply(rule dInv)
      subgoal by simp
      subgoal by simp
      subgoal by(rule dWeakening, simp)
      oops

lemma "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      ((D[''x''] = (\<lambda> s. s ''v'') with (\<lambda> s. True)))
      POST (\<lambda> s. s ''x''> 0)"
      apply(rule_tac C = "\<lambda> s. s ''v'' > 0" in dCut)
      apply(rule dInv2)
      subgoal by simp
      subgoal by simp
      apply(rule_tac C = "\<lambda> s. s ''x'' > 0" in dCut)
      apply(rule dInv2)
      subgoal by simp
      subgoal by simp
      by(rule dWeakening, simp)

lemma "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      ((D[''x''] = (\<lambda> s. s ''v'') with (\<lambda> s. True)))
      POST (\<lambda> s. s ''x''> 0)"
      apply(rule_tac C = "\<lambda> s. s ''v'' > 0" in dCut)
      apply(rule dInv3)
      subgoal by simp
      apply(simp, clarify)
      defer
      apply(rule_tac C = "\<lambda> s. s ''x'' > 0" in dCut)
      apply(rule dInv3)
      subgoal by simp
      apply(simp, clarify)
      defer
      subgoal by(rule dWeakening, simp)
      oops


(* Verification Examples. *)

lemma firstMastersVerification:
      "PRE (\<lambda> s. s ''station'' > s ''pos'' \<and> s ''vel'' > 0)  
      (
      (''acc'' ::= (\<lambda>s. - (s ''vel'')*(s ''vel'') / (2 * (s ''station'' - s ''pos''))));
      ((D[''pos''] = (\<lambda> s. s ''vel'') with (\<lambda> s. True))\<inter>
      (D[''vel''] = (\<lambda> s. s ''acc'') with (\<lambda> s. s ''vel'' \<ge> 0)) )
      )
      POST (\<lambda> s. (s ''station'' \<ge> s ''pos'') \<and> (s ''vel'' = 0 \<longleftrightarrow> s ''station'' = s ''pos''))"
      apply(simp)
      oops

declare [[show_types]]
declare [[show_sorts]]

      
end