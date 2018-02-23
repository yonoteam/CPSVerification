theory VC_diffKAD2
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

-- "Preliminary lemmas and definitions."
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

(* A cartesian product of lists. *)
fun cross_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"cross_list [] list = []"|
"cross_list list [] = []"|
"cross_list (x#xtail) (y#ytail) = (x,y)#(cross_list xtail ytail)"

primrec swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a" where "swap (x,y) = (y,x)"

primrec listSwap :: "('a \<times> 'b) list \<Rightarrow> ('b \<times> 'a) list" where
"listSwap [] = []" |
"listSwap (head # tail) = swap head # (listSwap tail)"

lemma listSwap_isMapSwap:"listSwap l = map swap l"
by(induct_tac l, auto)

lemma listSwap_crossList[simp]: "listSwap (cross_list l2 l1) = cross_list l1 l2"
apply(induction l1 l2 rule: cross_list.induct)
apply(metis cross_list.elims cross_list.simps(1) cross_list.simps(2) listSwap.simps(1))
apply(metis cross_list.simps(1) cross_list.simps(2) listSwap.simps(1))
by simp

lemma empty_crossListElim:
"[] = cross_list xList yList \<Longrightarrow>  [] = xList \<or> [] = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma tail_crossListElim:
"(x, y) # tail = cross_list xList yList \<Longrightarrow>  \<exists>xTail yTail. x # xTail = xList \<and> y # yTail = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma non_empty_crossListElim:
"(x, y) \<in> set (cross_list xList yList) \<Longrightarrow> x \<in> set xList \<and> y \<in> set yList"
by(induction xList yList rule: cross_list.induct, auto)

lemma crossList_map_projElim[simp]:"cross_list (map \<pi>\<^sub>1 list) (map \<pi>\<^sub>2 list) = list"
by(induct_tac list, auto)

lemma tail_crossList_map_projElim: 
"(x,y)#list = cross_list (map \<pi>\<^sub>1 l1) l2 \<Longrightarrow> \<exists> z tail. (x, z) # tail = l1"
proof-
assume hyp:"(x, y) # list = cross_list (map \<pi>\<^sub>1 l1) l2"
then have noEmpt:"(map \<pi>\<^sub>1 l1) \<noteq> [] \<and> l2 \<noteq> []" by (metis cross_list.elims list.discI) 
from this obtain hd1 hd2 tl1 and tl2 where hd1Def:"(map \<pi>\<^sub>1 l1) = hd1 # tl1 \<and> l2 = hd2 # tl2" 
by (meson list.exhaust) 
then obtain z and tail where tailDef:"l1 = (hd1,z) # tail \<and> (map \<pi>\<^sub>1 tail) = tl1" by auto
moreover have "(x, y) # list = (hd1,hd2)#(cross_list tl1 tl2)" by (simp add: hd1Def hyp)
ultimately show ?thesis by simp
qed

lemma non_empty_crossList_map_projEx:
"\<forall> xzList. xzList = cross_list (map \<pi>\<^sub>1 xyList) zList \<longrightarrow> 
(y, z) \<in> set (cross_list (map \<pi>\<^sub>2 xyList) zList) \<longrightarrow> 
(\<exists> x. (x,y) \<in> set xyList \<and> (x,z) \<in> set xzList)"
by(simp, induction xyList zList rule: cross_list.induct, auto)

lemma crossList_length:
"length xList = length yList \<Longrightarrow> length (cross_list xList yList) = length xList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma crossList_lengthEx:
"length xList = length yList \<Longrightarrow> 
\<forall> x \<in> set xList. \<exists> y \<in> set yList. (x,y) \<in> set (cross_list xList yList)"
apply(induction xList yList rule: cross_list.induct)
subgoal by simp
subgoal by simp
apply(rule ballI, simp, erule disjE, simp) 
by blast

lemma tail_crossList_length:
"length (cross_list xList yList) = length (z # zTail) \<longrightarrow> 
(\<exists> x y xTail yTail. (xList = x # xTail) \<and> (yList = y # yTail) \<and> 
length (cross_list xTail yTail) = length zTail)"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma length_crossListProj1:
"length xList = length yList \<Longrightarrow> map \<pi>\<^sub>1 (cross_list xList yList) = xList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma length_crossListProj2:
"length xList = length yList \<Longrightarrow> map \<pi>\<^sub>2 (cross_list xList yList) = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma legnth_crossListEx1:
"length (cross_list xList yList) = length yList \<Longrightarrow> 
\<forall> y \<in> set yList. \<exists> x \<in> set xList. (x, y) \<in> set (cross_list xList yList)"
apply(induction xList yList rule: cross_list.induct, simp, simp)
by(rule ballI, simp, erule disjE, simp, blast)

lemma legnth_crossListEx2:
"length (cross_list (x#xTail) (y#yTail)) = length zList \<Longrightarrow> 
\<exists> z zTail. zList = z # zTail \<and> length zTail = length (cross_list xTail yTail)"
by(induction zList, simp_all)

lemma legnth_crossListEx3:
"\<forall> zList x y. length (cross_list xList yList) = length zList \<longrightarrow> 
              (x, y) \<in> set (cross_list xList yList) \<longrightarrow> 
        (\<exists> z. (x, z) \<in> set (cross_list xList zList) \<and> 
              (y, z) \<in> set (cross_list (map \<pi>\<^sub>2 (cross_list xList yList)) zList))"
apply(induction xList yList rule: cross_list.induct, simp, simp, clarify)
apply(rename_tac x xTail y yTail zList u v)
apply(subgoal_tac "(u,v) = (x,y) \<or> (u,v) \<in> set (cross_list xTail yTail)")
apply(subgoal_tac "\<exists> z zTail. (zList = z # zTail) \<and> 
(length(cross_list xTail yTail) = length zTail)")
apply(erule disjE)
subgoal by auto
subgoal by fastforce
subgoal by (metis cross_list.simps(3) length_Suc_conv)
subgoal by simp
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
("_ solvesTheIVP _ withInitCond  _ \<mapsto> _" [70, 70, 70, 70] 68) where
"(x solvesTheIVP f withInitCond t0 \<mapsto> x0) Domf Codf \<equiv> (x solves_ode f) Domf Codf \<and> x t0 = x0"

lemma solves_ivpI:
assumes "(x solves_ode f) A B"
assumes "x t0 = x0"
shows "(x solvesTheIVP f withInitCond t0 \<mapsto> x0) A B"
using assms by (simp add: solves_ivp_def)

lemma solves_ivpD:
assumes "(x solvesTheIVP f withInitCond t0 \<mapsto> x0) A B"
shows "(x solves_ode f) A B"
and "x t0 = x0"
using assms by (auto simp: solves_ivp_def)

theorem(in unique_on_bounded_closed) ivp_unique_solution:
assumes xIsSol:"(x solvesTheIVP f withInitCond t0 \<mapsto> x0) T X"
assumes yIsSol:"(y solvesTheIVP f withInitCond t0 \<mapsto> x0) T X"
shows "\<forall> t \<in> T. x t = y t"
proof
fix t assume "t \<in> T"
from this and assms show "x t = y t" 
using unique_solution solves_ivp_def by blast 
qed

(* Observations *)
term "closed_segment a (b::real)"
term "open_segment a b"
thm closed_segment_def
term "atLeastAtMost a (b::real)"
term "greaterThanLessThan a b"
thm atLeast_def
term "box a (b::real)"
thm box_def
thm solves_ode_def
thm has_vderiv_on_def

(* In our store implementation:
    · The solution "x:\<real>\<rightarrow>\<real>\<^sup>n" is changed for "F::real \<Rightarrow> real store" (i.e. real \<Rightarrow> string \<Rightarrow> real).
      The letter "x" is reserved for strings.
    · Instead of "f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n" we use "f::real store \<Rightarrow> real". This is for consistency with the
      "expressions" in assignments in VC_KAD.thy and because we mainly focus on "autonomous systems
      of ODE'S (i.e. systems of the form x'(t)=f(x(t))). *)

definition vdiff ::"string \<Rightarrow> string" where
"vdiff x = ''d[''@x@'']''" (* Alternatively, we could use: "''d''@x@''/dt''" *)

definition varDiffs :: "string set" where
"varDiffs = {str. \<exists> x. str = vdiff x}"

lemma vdiff_inj:"\<forall> x y. vdiff x = vdiff y \<longrightarrow> x = y"
by(simp add: vdiff_def)

lemma vdiff_noFixPoints:"\<forall> str. str \<noteq> vdiff str"
by(simp add: vdiff_def)

lemma varDiffsI:"x = vdiff z \<Longrightarrow> x \<in> varDiffs"
by(simp add: varDiffs_def, rule_tac x="z" in exI, simp)

lemma vdiff_invarDiffs:"\<forall> str. vdiff str \<in> varDiffs"
by (simp add: varDiffsI)

definition solvesStoreIVP :: "(real \<Rightarrow> real store) \<Rightarrow> (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real store \<Rightarrow> (real store pred) \<Rightarrow> bool" 
("(_ solvesTheStoreIVP _ withInitState _ andGuard _)" [70, 70, 70, 70] 68) where
"solvesStoreIVP F xfList st G \<equiv>
(* At the beginning F is (almost) the initial state. *)
(\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str) \<and>
(* F preserves the guard statement and F sends varDiffs to derivs. *)
(\<forall> t \<ge> 0. G (F t) \<and>  (\<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)) \<and> 
(* F preserves the rest of the variables and F sends derivs of constants to 0. *)
  (\<forall> str. (str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str) \<and> 
          (str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)) \<longrightarrow> F t str = 0)) \<and> 
(* F solves the induced IVP. *)
  (\<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
  withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0<--<t} UNIV))"

lemma storeIVP_def_isSound:
assumes "x 0 = x0"
shows "(x solvesTheIVP f  withInitCond 0 \<mapsto> x0) {0<--<0} UNIV"
apply(simp add: solves_ivp_def solves_ode_def)
using assms by simp

lemma storeIVP_def_couldBeModified:
assumes "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0<--<t} UNIV"
assumes "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
shows "\<forall> xf \<in> set xfList. \<forall> r>0. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative 
(\<lambda> t. F t (vdiff (\<pi>\<^sub>1 xf))) r) (at r within {0<--<2 \<cdot> r})"
proof(clarify)
fix x f and r::real
assume "0 < r" then have rHyp:"0 < 2 \<cdot> r" by auto
assume xfHyp:"(x, f) \<in> set xfList" 
from this and assms(1) have "((\<lambda> t. F t (\<pi>\<^sub>1 (x, f))) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 (x, f)) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 (x, f)))) {0<--<2 \<cdot> r} UNIV"  using less_eq_real_def rHyp by blast 
then have "((\<lambda> t. F t x) has_vderiv_on (\<lambda> t. f (F t))) {0<--<2 \<cdot> r}" 
by (simp add: solves_ode_def solves_ivp_def)
hence dHyp:"\<forall> s \<in> {0<--<2 \<cdot> r}. ((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) s) 
(at s within {0<--<2 \<cdot> r})" by (simp add: has_vderiv_on_def rHyp real_Icc_closed_segment) 
have "0 \<le> 2 \<cdot> r" using rHyp by linarith
from this assms(2) xfHyp  have "\<forall> t \<in> {0<--<2 \<cdot> r}. (F t (vdiff x)) = f (F t)"
using open_segment_eq_real_ivl less_eq_real_def by fastforce 
from this and dHyp show "((\<lambda>t. F t (\<pi>\<^sub>1 (x, f))) has_vector_derivative F r 
(vdiff (\<pi>\<^sub>1 (x, f)))) (at r within {0<--<2 \<cdot> r})"
using \<open>0 < r\<close> open_segment_eq_real_ivl by auto
qed

  
lemma solves_store_ivpI:
  assumes "\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str"
  assumes "\<forall> t \<ge> 0. G (F t)"
  assumes "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
  assumes "\<forall> t \<ge> 0.\<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)). F t str = 0" 
  assumes "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
  assumes "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0<--<t} UNIV"
  shows "F solvesTheStoreIVP xfList withInitState st andGuard G"
  using assms solvesStoreIVP_def by auto

lemma solves_store_ivpD:
  assumes "F solvesTheStoreIVP xfList withInitState st andGuard G"
  shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str"
and "\<forall> t \<ge> 0. G (F t)"
and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
and "\<forall> t \<ge> 0.\<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)). F t str = 0"
and "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0<--<t} UNIV"
  using assms solvesStoreIVP_def by auto

definition guarDiffEqtn :: "(string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> (real store pred) \<Rightarrow> 
real store rel" ("ODEsystem _ with _ " [70, 70] 61) where
"ODEsystem xfList with G = {(st,F t) |st t F. t \<ge> 0 \<and> solvesStoreIVP F xfList st G}"

-- "Differential Weakening."
(* Sketch of dW's proof: 
    \<pi>\<^sub>2[\<alpha>] \<subseteq> \<phi> \<Longrightarrow> (\<alpha> \<circ> \<phi>\<^sup>C) = \<emptyset> \<Longleftrightarrow> Univ = (\<alpha> \<circ> \<phi>\<^sup>C)\<^sup>C = \<not> <\<alpha>> \<not> \<phi>  = [\<alpha>] \<phi> *)
lemma dEvolutionImpliesGuard:"\<pi>\<^sub>2\<lbrakk>ODEsystem xfList with G\<rbrakk> \<subseteq> p2s G"
  by (auto simp: guarDiffEqtn_def solves_store_ivpD)

lemma relAdNullComposIfCodSubset:"\<pi>\<^sub>2\<lbrakk>R\<rbrakk> \<subseteq> p2s P \<Longrightarrow> R ; \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> = {}"
  by (auto simp: p2r_def p2r_subid rel_ad_def)

theorem dWeakening: 
assumes guardImpliesPost: "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE P (ODEsystem xfList with G) POST Q"
proof-
  have "\<pi>\<^sub>2\<lbrakk>ODEsystem xfList with G\<rbrakk> \<subseteq> p2s Q" using
  guardImpliesPost dEvolutionImpliesGuard
    by (metis (mono_tags, lifting) contra_subsetD impl_prop mem_Collect_eq subsetI) 
  then have "(ODEsystem xfList with G) ; \<Delta>\<^sup>c\<^sub>1 \<lceil>Q\<rceil> = {}" 
    by (meson relAdNullComposIfCodSubset)
  from this show ?thesis
    by (simp add: p2r_subid rel_antidomain_kleene_algebra.addual.bbox_def) 
qed

(* Example of hybrid program verified with differential weakening. *)  
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
  using dWeakening by simp
      
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
  apply(clarify, simp add: p2r_def)
  apply(simp add: rel_ad_def rel_antidomain_kleene_algebra.addual.ars_r_def)
  apply(simp add: rel_antidomain_kleene_algebra.fbox_def)
  apply(simp add: relcomp_def rel_ad_def guarDiffEqtn_def)
  apply(simp add: solvesStoreIVP_def)
  apply(auto)
  done

-- "Differential Cut."
lemma condAfterEvol_remainsAlongEvol:
  assumes boxDiffC:"(a, a) \<in> wp (ODEsystem xfList with G) \<lceil>C\<rceil>"
  assumes FisSol:"solvesStoreIVP F xfList a G"
  shows "solvesStoreIVP F xfList a (\<lambda>s. G s \<and> C s)"
  apply(rule solves_store_ivpI)
  defer   subgoal proof(clarify)
  from boxDiffC have diffHyp:"\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> C c"
  using guarDiffEqtn_def wp_trafo by (metis (no_types, lifting) Domain.intros r2p_def)
  fix t::real assume tHyp:"0 \<le> t"
  then have odeF:"(a,F t) \<in> (ODEsystem xfList with G)" using FisSol guarDiffEqtn_def by auto 
  from this diffHyp and tHyp show "G (F t) \<and> C (F t)" using solves_store_ivpD(2) FisSol by blast
  qed
  using FisSol solvesStoreIVP_def by auto

lemma boxDiffCond_impliesAllTimeInCond:
  assumes allTime: "(t::real)\<ge> 0"
  assumes boxDifCond:"(a,a) \<in> wp (ODEsystem xfList with G) \<lceil>C\<rceil>"
  assumes FisSol:"solvesStoreIVP F xfList a G"
  shows "(a,F t) \<in> (ODEsystem xfList with (\<lambda>s. G s \<and> C s))"
  apply(simp add: guarDiffEqtn_def)
  apply(rule_tac x="t" in exI, rule_tac x="F" in exI, simp add: allTime)
  apply(rule condAfterEvol_remainsAlongEvol)
  using boxDifCond guarDiffEqtn_def FisSol by safe

theorem dCut: 
  assumes pBoxDiffCut:"(PRE P (ODEsystem xfList with G) POST C)"
  assumes pBoxCutQ:"(PRE P (ODEsystem xfList with (\<lambda> s. G s \<and> C s)) POST Q)"
  shows "PRE P (ODEsystem xfList with G) POST Q"
proof(clarify)
  fix a b::"real store" assume abHyp:"(a,b) \<in> rdom \<lceil>P\<rceil>"
  from this have "a = b \<and> P a" by (metis rdom_p2r_contents)
  from this abHyp and pBoxDiffCut have "(a,a) \<in> wp (ODEsystem xfList with G) \<lceil>C\<rceil>" by blast
  moreover 
    from pBoxCutQ and abHyp have "\<forall> c. (a,c) \<in> (ODEsystem xfList with (\<lambda>s. G s \<and> C s)) \<longrightarrow> Q c"
    by (metis (no_types, lifting) \<open>a = b \<and> P a\<close> boxProgrPred_chrctrztn set_mp)
  ultimately have "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> Q c" using
      guarDiffEqtn_def boxDiffCond_impliesAllTimeInCond by auto
  from this and \<open>a = b \<and> P a\<close> show "(a,b) \<in> wp (ODEsystem xfList with G) \<lceil>Q\<rceil>" 
    by (simp add: boxProgrPred_chrctrztn)
qed 

-- "Solve Differential Equation."
(* The rule "dSolve" requires an input from the user, i.e. the unique list of solutions to the 
system of ODE's, i.e. uInput::"(real \<Rightarrow> (real store) \<Rightarrow> real) list". This fact forces us to handle
several lists. For that reason, in this section we change the name "xfList" for "varFunList".
Moreover, we combine the user input with the list of variables in a single list "varSolList" to
compute the corresponding solution to the store-IVP. *)

abbreviation toInit :: "('a::zero) store \<Rightarrow> 'a store" where
"toInit a \<equiv> (override_on a (\<lambda> str. 0) varDiffs)"

lemma toInit_begins[simp]: "take 2 x \<noteq> ''d['' \<Longrightarrow> toInit a x = a x"
apply(simp add: varDiffs_def vdiff_def override_on_def)
by(fastforce)

thm frechet_derivative_def
primrec toSol :: "(string \<times> (('a::real_normed_vector) \<Rightarrow> 'a store \<Rightarrow> 'a)) list \<Rightarrow> 'a \<Rightarrow> 
'a store \<Rightarrow> 'a store" where
"toSol [] t a  = a"|
"toSol (varSol#tail) t a =
(toSol tail t a)(\<pi>\<^sub>1 varSol := (\<pi>\<^sub>2 varSol) t a, 
         vdiff (\<pi>\<^sub>1 varSol) := frechet_derivative (\<lambda> r. (\<pi>\<^sub>2 varSol) r a) (at t within {0<--< (2 *\<^sub>R t)}) t)"

(*"(if t>0
then (toSol tail t a)
(     (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (\<pi>\<^sub>1 uxf) t a, 
vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<--< (2 *\<^sub>R t)} t) 
else a)"*)

definition mass_gets :: "string list \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a store \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow>
'a store rel" ("_ :::= _" [70, 65] 61) where
"(varList :::= solList) t = {(s,toSol (cross_list varList solList) t (toInit s)) |s. True}"

lemma prelim_dSolve:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and solHyp:"solvesStoreIVP (\<lambda> t. toSol varSolList t (toInit a)) varFunList a G"
and uniqHyp:"\<forall> X. solvesStoreIVP X varFunList a G \<longrightarrow> 
(\<forall> t \<ge> 0. (toSol varSolList t (toInit a)) = X t)"
and guardPreservedImpliesPost: 
"\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol varSolList r (toInit a))) \<longrightarrow> 
(\<forall> c. (a,c) \<in> ((map \<pi>\<^sub>1 varFunList) :::= uInput) t \<longrightarrow> Q c)"
shows "\<forall> c. (a,c) \<in> (ODEsystem varFunList with G) \<longrightarrow> Q c"
proof(clarify)
fix c assume "(a,c) \<in> (ODEsystem varFunList with G)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F varFunList a G" using guarDiffEqtn_def by auto 
from this and uniqHyp have "toSol varSolList t (toInit a) = F t" by blast
then have cHyp:"c = (toSol varSolList t (toInit a))" using FHyp by simp
hence "(a,c) \<in> (((map \<pi>\<^sub>1 varFunList) :::= uInput) t)"
by (simp add: mass_gets_def varSolDef) 
moreover from solHyp have "\<forall>r \<in> {0<--< t}. G (toSol varSolList r (toInit a))"
by (simp add: open_segment_eq_real_ivl solvesStoreIVP_def FHyp)
ultimately show "Q c" using guardPreservedImpliesPost FHyp by blast
qed

theorem dSolve:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and solves:"\<forall> st. solvesStoreIVP (\<lambda> t. toSol varSolList t (toInit st)) varFunList st G"
and isUniq:
"\<forall> st. \<forall> X. solvesStoreIVP X varFunList st G \<longrightarrow> (\<forall> t \<ge> 0. (toSol varSolList t (toInit st)) = X t)"
and diffAssgn: "\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol varSolList r (toInit st))) \<longrightarrow> 
\<lfloor>wp (((map \<pi>\<^sub>1 varFunList) :::= uInput) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem varFunList with G) POST Q"
apply(clarsimp)
apply(subgoal_tac "a=b")
apply(clarify, subst boxProgrPred_chrctrztn)
apply(simp_all add: p2r_def)
apply(rule_tac varSolList="varSolList" and uInput="uInput" in prelim_dSolve)
apply(simp add: varSolDef, simp add: solves, simp add: isUniq)
by(metis diffAssgn wp_trafo_var)

(* We proceed to refine the previous rule by finding the necessary restrictions on "varSolLIst",
"varFunList" and "uInput" so that the solution to the store-IVP is guaranteed. *)
lemma toSol_keepsInitStateAt0:
"(\<forall> st. \<forall> varSol \<in> set varSolList. (\<pi>\<^sub>2 varSol) 0 st = st (\<pi>\<^sub>1 varSol)) \<longrightarrow> 
(\<forall> str. str \<notin> varDiffs \<longrightarrow> toSol varSolList 0 (toInit a) str = a str)"
apply(induct_tac varSolList)
apply(simp_all, clarify, safe)
by (auto simp: varDiffs_def vdiff_invarDiffs)

lemma conds4InitState:
assumes initHyp:"\<forall> st. \<forall> varSol \<in> set varSolList. (\<pi>\<^sub>2 varSol) 0 st = st (\<pi>\<^sub>1 varSol)"
shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> toSol varSolList 0 (toInit a) str = a str"
using initHyp toSol_keepsInitStateAt0 by blast

lemma toSol_correctInPrimes:
"\<forall> varSolList. varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput \<longrightarrow> 
distinct (map \<pi>\<^sub>1 varFunList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs) \<longrightarrow>
length (varFunList::(string \<times> (real store \<Rightarrow> real))list) = length uInput \<longrightarrow> 
(\<forall> xs \<in>set varSolList. (toSol varSolList t (toInit a)) (vdiff (\<pi>\<^sub>1 xs)) = 
  frechet_derivative (\<lambda> r. (\<pi>\<^sub>2 xs) r (toInit (a::real store))) (at t within {0<--< (2 *\<^sub>R t)}) t)"
apply(simp, induction varFunList uInput rule: cross_list.induct, simp, simp, clarify)
proof(rename_tac x f varFunTail u uTail y w)
fix x y ::"string" and f ::"real store \<Rightarrow> real"  and u w::"real \<Rightarrow> real store \<Rightarrow> real" and
varFunTail::"(string \<times> (real store \<Rightarrow> real)) list" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real) list"
assume "length ((x, f) # varFunTail) = length (u # uTail)"
then obtain varTail::"string list" and funTail::"(real store \<Rightarrow> real) list"
where varfHyp:"map \<pi>\<^sub>1 varFunTail = varTail \<and> map \<pi>\<^sub>2 varFunTail = funTail \<and> 
length varFunTail = length uTail" by simp
assume dist:"distinct (map \<pi>\<^sub>1 ((x, f) # varFunTail))"
then have notX:"\<forall> var \<in> set varTail. var \<noteq> x" using varfHyp by auto 
assume *:"\<forall>var\<in>set ((x, f) # varFunTail). \<pi>\<^sub>1 var \<notin> varDiffs" 
from this have notdY:"\<forall> var \<in> set (x # varTail). var \<noteq> vdiff y" 
using varfHyp vdiff_invarDiffs by fastforce 
assume IH:"distinct (map \<pi>\<^sub>1 varFunTail) \<longrightarrow> 
(\<forall>var\<in>set varFunTail. \<pi>\<^sub>1 var \<notin> varDiffs) \<longrightarrow>
length varFunTail = length uTail \<longrightarrow>
(\<forall>xs\<in>set (cross_list (map \<pi>\<^sub>1 varFunTail) uTail).
  toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a) (vdiff (\<pi>\<^sub>1 xs)) =
  frechet_derivative (\<lambda>r. \<pi>\<^sub>2 xs r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t)"
then have keyFact:"\<forall> xs \<in> set (cross_list varTail uTail).
  toSol (cross_list varTail uTail) t (toInit a) (vdiff (\<pi>\<^sub>1 xs)) =
  frechet_derivative (\<lambda>r. \<pi>\<^sub>2 xs r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t" 
  using varfHyp dist * by simp
assume ywHyp:"(y, w) \<in> set (cross_list (map \<pi>\<^sub>1 ((x, f) # varFunTail)) (u # uTail))"
let ?goalLHS = "toSol (cross_list (map \<pi>\<^sub>1 ((x, f) # varFunTail)) (u # uTail)) t (toInit a) 
(vdiff (\<pi>\<^sub>1 (y, w)))"
let ?goalRHS = "frechet_derivative (\<lambda>r. \<pi>\<^sub>2 (y, w) r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t"
let ?goal = "?goalLHS = ?goalRHS"
let ?lhs = "((toSol (cross_list varTail uTail) t (toInit a))
(x := u t (toInit a), vdiff x := frechet_derivative (\<lambda> r. u r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t))
(vdiff (\<pi>\<^sub>1 (y, w)))"
let ?rhs = "frechet_derivative (\<lambda>r. w r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t"
from ywHyp have "(y,w) = (x,u) \<or> (y,w) \<in> set (cross_list varTail uTail)" using varfHyp by simp 
moreover
{from varfHyp have "?goalLHS = ?lhs" by simp
  also have "?goalRHS =?rhs" using varfHyp by simp
  ultimately have "?goal = (?lhs = ?rhs)" by simp}
moreover
{assume ywxu:"(y,w) = (x,u)"
  then have "?lhs = frechet_derivative (\<lambda> r. u r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t" by simp
  also have "frechet_derivative (\<lambda> r. u r (toInit a)) (at t within {0<--< (2 \<cdot> t)}) t = ?rhs" 
  using ywxu by simp
  ultimately have "?lhs = ?rhs" by simp}
moreover
{assume ywTail:"(y,w) \<in> set (cross_list varTail uTail)"
  from this have "y \<noteq> x" using non_empty_crossListElim notX by fastforce
  hence dXnotdY:"vdiff x \<noteq> vdiff y" by(simp add: vdiff_def)
  from notdY have xNotdY:"x \<noteq> vdiff y" using non_empty_crossListElim by fastforce
  then have "?lhs = toSol (cross_list varTail uTail) t (toInit a) (vdiff y)" 
  using xNotdY and dXnotdY by simp
  also have "toSol (cross_list varTail uTail) t (toInit a) (vdiff y) = ?rhs" 
  using keyFact ywTail by auto  
  ultimately have "?lhs = ?rhs" by simp}
ultimately show ?goal by blast
qed

lemma conds4vdiffs:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 (varFunList::(string \<times> (real store \<Rightarrow> real))list))" 
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs"
and lengthHyp:"length varFunList = length uInput"
and keyFact:"\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>t\<ge>0. frechet_derivative (\<lambda>r. \<pi>\<^sub>2 funSol r (toInit st)) (at t within {0<--< (2 *\<^sub>R t)}) t =
      \<pi>\<^sub>1 funSol (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit st))"
shows "\<forall> st. \<forall> t\<ge>0. \<forall> xf\<in>set varFunList. 
(toSol varSolList t (toInit st)) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (toSol varSolList t (toInit st))"
proof(clarify)
fix t::real and x::string and f::"real store \<Rightarrow> real" and a::"real store"
from assms have toSol_onVdiff:"\<forall>t\<ge>0. \<forall>xs\<in>set varSolList.
  toSol varSolList t (toInit a) (vdiff (\<pi>\<^sub>1 xs)) =
  frechet_derivative (\<lambda>r. \<pi>\<^sub>2 xs r (toInit a)) (at t within {0<--< (2 *\<^sub>R t)}) t" 
using toSol_correctInPrimes by simp
assume tHyp:"0 \<le> t" and "(x, f) \<in> set varFunList" 
from this obtain s::"real \<Rightarrow> real store \<Rightarrow> real" where 
xfs:"(x, s) \<in> set varSolList \<and> (f, s) \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput)"
using lengthHyp varSolDef by (metis crossList_map_projElim legnth_crossListEx3)
from this and toSol_onVdiff have "toSol varSolList t (toInit a) (vdiff x) =
  frechet_derivative (\<lambda>r. s r (toInit a)) (at t within {0<--< (2 *\<^sub>R t)}) t" using tHyp by fastforce
also have "frechet_derivative (\<lambda>r. s r (toInit a)) (at t within {0<--< (2 *\<^sub>R t)}) t =
  f (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit a))" 
using xfs tHyp and keyFact by fastforce
ultimately show "toSol varSolList t (toInit a) (vdiff (\<pi>\<^sub>1 (x, f))) = 
\<pi>\<^sub>2 (x, f) (toSol varSolList t (toInit a))" using varSolDef by simp
qed

lemma toSol_sendsCnstsTo0:
shows "\<forall> varSolList. varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput \<longrightarrow>
(\<forall> str \<in> set (map \<pi>\<^sub>1 varFunList). str \<notin> varDiffs) \<longrightarrow>
(\<forall> t \<ge> 0. \<forall>str. (str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>\<rbrakk>)) \<longrightarrow> 
(toSol varSolList t (toInit a)) str = 0))"
by(simp, induction varFunList uInput rule: cross_list.induct, simp_all)

lemma conds4Consts:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and varsHyp:"\<forall> str \<in> set (map \<pi>\<^sub>1 varFunList). str \<notin> varDiffs"
shows "\<forall> t \<ge> 0. \<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>\<rbrakk>)). 
(toSol varSolList t (toInit a)) str = 0"
using assms by (simp add: toSol_sendsCnstsTo0) 

lemma toSol_correctEverywhereElse:
shows "\<forall> varSolList. varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput \<longrightarrow> 
(\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs \<longrightarrow> (toSol varSolList t (toInit a)) str = a str)"
apply(simp add: image_def, induction varFunList uInput rule: cross_list.induct)
by (auto simp: varDiffs_def)

lemma conds4RestOfStrings:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
shows "\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs \<longrightarrow> (toSol varSolList t (toInit a)) str = a str"
using assms and toSol_correctEverywhereElse by blast

lemma toSol_simp:
 "\<forall> varSolList. varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput \<longrightarrow> 
distinct (map \<pi>\<^sub>1 varFunList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs) \<longrightarrow>
length (varFunList::(string \<times> (real store \<Rightarrow> real))list) = 
length (uInput::(real \<Rightarrow> real store \<Rightarrow> real)list) \<longrightarrow> 
(\<forall> st. \<forall> t. \<forall> varSol \<in>set varSolList. 
(toSol varSolList t (toInit st)) (\<pi>\<^sub>1 varSol) = \<pi>\<^sub>2 varSol t (toInit st))"
apply(simp, induction varFunList uInput rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac x f varFunTail u uTail a t y sol)
fix x y::"string" and f::"real store \<Rightarrow> real" and u sol::"real \<Rightarrow> real store \<Rightarrow> real"
and a::"real store" and t::real and varFunTail::"(string \<times> (real store \<Rightarrow> real))list" 
and uTail::"(real \<Rightarrow> real store \<Rightarrow> real)list"
let ?gLHS = "toSol (cross_list (map \<pi>\<^sub>1 ((x, f) # varFunTail)) (u # uTail)) t (toInit a) (\<pi>\<^sub>1 (y, sol))"
let ?goal = "?gLHS = \<pi>\<^sub>2 (y, sol) t (toInit a)"
assume IH:"distinct (map \<pi>\<^sub>1 varFunTail) \<longrightarrow> (\<forall>var\<in>set varFunTail. \<pi>\<^sub>1 var \<notin> varDiffs) \<longrightarrow>
length varFunTail = length uTail \<longrightarrow> (\<forall>st t.(\<forall>varSol\<in>set (cross_list (map \<pi>\<^sub>1 varFunTail) uTail).
  toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit st) (\<pi>\<^sub>1 varSol) = \<pi>\<^sub>2 varSol t (toInit st)))"
and distHyp:"distinct (map \<pi>\<^sub>1 ((x, f) # varFunTail))"
and varsHyp:"\<forall>xf \<in> set ((x, f) # varFunTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length ((x, f) # varFunTail) = length (u # uTail)"
then have keyHyp:"\<forall>varSol\<in>set (cross_list (map \<pi>\<^sub>1 varFunTail) uTail).
toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a) (\<pi>\<^sub>1 varSol) = \<pi>\<^sub>2 varSol t (toInit a)"
by fastforce
assume "(y, sol) \<in> set (cross_list (map \<pi>\<^sub>1 ((x, f) # varFunTail)) (u # uTail))" 
from this have "(y,sol) = (x,u) \<or> (y,sol) \<in> set (cross_list (map \<pi>\<^sub>1 varFunTail) uTail)" by simp
moreover
{assume uSolxy:"(y,sol) = (x,u)" 
  then have "?gLHS = ((toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a))
  (x := sol t (toInit a), vdiff x := frechet_derivative (\<lambda>r. sol r (toInit a)) 
  (at t within {0<--< (2 *\<^sub>R t)}) t)) y" by simp
  also have "((toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a))(x := sol t (toInit a), 
  vdiff x := frechet_derivative (\<lambda>r. sol r (toInit a)) (at t within {0<--< (2 *\<^sub>R t)}) t)) y = 
  sol t (toInit a)" using uSolxy by (simp add: vdiff_noFixPoints)
  ultimately have ?goal by simp}
moreover
{assume yTailHyp:"(y,sol) \<in> set (cross_list (map \<pi>\<^sub>1 varFunTail) uTail)"
  from this and keyHyp have 3:"toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a) y = 
  sol t (toInit a)" by fastforce
  from yTailHyp and distHyp have 2:"y \<noteq> x" using non_empty_crossListElim by force 
  from yTailHyp and varsHyp have 1:"y \<noteq> vdiff x" 
  using non_empty_crossListElim vdiff_invarDiffs by fastforce 
  from 1 and 2 have "?gLHS = toSol (cross_list (map \<pi>\<^sub>1 varFunTail) uTail) t (toInit a) y"  by simp
  then have "?goal" using 3 by simp}
ultimately show ?goal by blast
qed

lemma conds4simpl_toSol:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 (varFunList::(string \<times> (real store \<Rightarrow> real))list))" 
and lengthHyp:"length varFunList = length (uInput::(real \<Rightarrow> real store \<Rightarrow> real)list)"
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs"
shows "\<forall> varSol \<in>set varSolList. (toSol varSolList t (toInit a)) (\<pi>\<^sub>1 varSol) = \<pi>\<^sub>2 varSol t (toInit a)"
using assms and toSol_simp by blast

lemma keyFact_elim:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 (varFunList::(string \<times> (real store \<Rightarrow> real))list))" 
and lengthHyp:"length varFunList = length (uInput::(real \<Rightarrow> real store \<Rightarrow> real)list)"
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs" 
and tHyp:"0 \<le> t"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. ((\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol varSolList t (toInit st)))) {0--t}" 
shows keyFact:"\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>r \<in> {0<..<t}. frechet_derivative (\<lambda>s. \<pi>\<^sub>2 funSol s (toInit st)) (at r within {0<--<t}) =
      (\<lambda>s. s *\<^sub>R  (\<pi>\<^sub>1 funSol (toSol varSolList r (toInit st))))"
proof(clarify, rename_tac a f u r)
fix a::"real store" and r::real and f::"real store \<Rightarrow> real" and u::"real \<Rightarrow> real store \<Rightarrow> real"
assume "(f, u) \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput)" and rHyp:"r \<in> {0<..<t}"
then obtain x where xDef:"(x,f) \<in> set varFunList \<and> (x,u) \<in> set varSolList" 
using non_empty_crossList_map_projEx varSolDef by fastforce
from this and assms have "\<forall> s \<ge> 0. (toSol varSolList s (toInit a)) x = u s (toInit a)" 
using conds4simpl_toSol by (metis fst_conv snd_conv) 
hence 1:"\<And>r. r \<in> {0<--<t} \<Longrightarrow> (\<lambda> t. (toSol varSolList t (toInit a)) x) r = (\<lambda> t. u t (toInit a)) r "
by (simp add: open_segment_eq_real_ivl tHyp)
from solHyp1 and xDef and tHyp have "((\<lambda>t. (toSol varSolList t (toInit a)) x) 
has_vderiv_on (\<lambda>t. f (toSol varSolList t (toInit a)))) {0--t}" by fastforce 
hence "((\<lambda>t. (toSol varSolList t (toInit a)) x) 
has_vderiv_on (\<lambda>t. f (toSol varSolList t (toInit a)))) {0<--<t}"
using has_vderiv_on_subset open_closed_segment_subset by blast 
then have "((\<lambda> t. u t (toInit a)) has_vderiv_on (\<lambda>t. f (toSol varSolList t (toInit a)))) {0<--<t}"
using 1 and has_vderiv_on_cong by auto
from this have "\<forall>r\<in> {0<--<t}. ((\<lambda> t. u t (toInit a)) has_vector_derivative 
f (toSol varSolList r (toInit a))) (at r within {0<--<t})" by (simp add: has_vderiv_on_def)
hence "\<forall>s\<in> {0<--<t}. ((\<lambda> t. u t (toInit a)) has_derivative 
(\<lambda>t. t *\<^sub>R f (toSol varSolList s (toInit a)))) (at s within {0<--<t})" 
by (simp add: has_vector_derivative_def)
from rHyp and this have derivHyp:"((\<lambda> t. u t (toInit a)) has_derivative 
(\<lambda>t. t \<cdot> f (toSol varSolList r (toInit a)))) (at r within {0<--<t})" by (simp add: open_segment_real) 
show "frechet_derivative (\<lambda>s. \<pi>\<^sub>2 (f, u) s (toInit a)) (at r within {0<--<t}) =
       (\<lambda>s. s *\<^sub>R \<pi>\<^sub>1 (f, u) (toSol varSolList r (toInit a)))"
  proof(simp add: frechet_derivative_def, rule some_equality, simp add: derivHyp)
  fix f'::"real \<Rightarrow> real"       
  assume otherDerivHyp:"((\<lambda>s. u s (toInit a)) has_derivative f') (at r within {0<--<t})"
  have "r \<in> box 0 t" using rHyp by simp 
  from this derivHyp and otherDerivHyp show "f' = (\<lambda>s. s \<cdot> f (toSol varSolList r (toInit a)))"
  by (simp add: frechet_derivative_unique_within_open_interval open_segment_real)
  qed
qed


lemma conds4storeIVP_on_toSol:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 (varFunList::(string \<times> (real store \<Rightarrow> real))list))" 
and lengthHyp:"length varFunList = length uInput"
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs"
and keyFact:"\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>t\<ge>0. frechet_derivative (\<lambda>r. \<pi>\<^sub>2 funSol r (toInit st)) (at t within {0<--< (2 *\<^sub>R t)}) t =
      \<pi>\<^sub>1 funSol (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit st))"
and initHyp:"\<forall> st. \<forall> varSol \<in> set varSolList. (\<pi>\<^sub>2 varSol) 0 st = st (\<pi>\<^sub>1 varSol)"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol varSolList t (toInit st))"
and solHyp:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. ((\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol varSolList t (toInit st)))) {0--t} 
\<and> (\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV
\<and> toSol varSolList 0 (toInit st) (\<pi>\<^sub>1 xf) = st (\<pi>\<^sub>1 xf)"
shows "\<forall> st. solvesStoreIVP (\<lambda> t. toSol varSolList t (toInit st)) varFunList st G"
apply(rule allI, rule solves_store_ivpI)
subgoal using conds4InitState initHyp by blast
subgoal using guardHyp by simp
subgoal using conds4RestOfStrings varSolDef by blast
subgoal using conds4Consts varsHyp varSolDef by blast
subgoal using conds4vdiffs varSolDef distinctHyp lengthHyp varsHyp keyFact by blast
subgoal using solHyp by(simp add: solves_ivp_def solves_ode_def) sorry
done
(*proof(clarify, rename_tac a t x f)
fix a::"real store" and t::"real" and x::"string" and f::"real store \<Rightarrow> real"
assume tHyp:"0\<le>t" and "(x, f) \<in> set varFunList"
let ?goal = "toSol varSolList t (toInit a) (vdiff (\<pi>\<^sub>1 (x, f))) = 
\<pi>\<^sub>2 (x, f) (toSol varSolList t (toInit a)) "
from varSolDef and lengthHyp obtain u where uDef:"(f,u) \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput) 
\<and> (x,u) \<in> set varSolList" by (metis \<open>(x, f) \<in> set varFunList\<close> crossList_proj cross_list_lengthEx3) 
show ?goal
proof(cases "t=0")
case True
then show ?thesis sorry
next
case False
then have "\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>r \<in> {0<..<t}. frechet_derivative (\<lambda>s. \<pi>\<^sub>2 funSol s (toInit st)) (at r within {0<--<t}) =
      (\<lambda>s. s *\<^sub>R  (\<pi>\<^sub>1 funSol (toSol varSolList r (toInit st))))"
using keyFact_elim tHyp varSolDef distinctHyp lengthHyp varsHyp solHyp by auto
from this and False have "\<forall>r \<in> {0<..<2 \<cdot> t}. 
frechet_derivative (\<lambda>s. u s (toInit a)) (at r within {0<--<2 \<cdot> t}) =
(\<lambda>s. s *\<^sub>R  (f (toSol varSolList r (toInit a))))" 
using uDef tHyp 
(* \<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>t\<ge>0. frechet_derivative (\<lambda>r. \<pi>\<^sub>2 funSol r (toInit st)) (at t within {0<--< (2 *\<^sub>R t)}) t =
      \<pi>\<^sub>1 funSol (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit st)) *)
then show ?thesis sorry
qed*)
(*using conds4vdiffs varSolDef distinctHyp lengthHyp varsHyp sorry*)

theorem dSolve_toSolve:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 (varFunList::(string \<times> (real store \<Rightarrow> real))list))" 
and lengthHyp:"length varFunList = length uInput"
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs"
and keyFact:"\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>t\<ge>0. frechet_derivative (\<lambda>r. \<pi>\<^sub>2 funSol r (toInit st)) (at t within {0<--< (2 *\<^sub>R t)}) t =
      \<pi>\<^sub>1 funSol (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit st))"
and initHyp:"\<forall> st. \<forall> varSol \<in> set varSolList. (\<pi>\<^sub>2 varSol) 0 st = st (\<pi>\<^sub>1 varSol)"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol varSolList t (toInit st))"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. ((\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol varSolList t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. 
(\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>xf\<in>set varFunList. toSol varSolList 0 (toInit st) (\<pi>\<^sub>1 xf) = st (\<pi>\<^sub>1 xf)"
and uniqHyp:"\<forall> st. \<forall> X. solvesStoreIVP X varFunList st G \<longrightarrow> 
(\<forall> t \<ge> 0. (toSol varSolList t (toInit st)) = X t)"
and diffAssgn: "\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol varSolList r (toInit st))) \<longrightarrow> 
\<lfloor>wp (((map \<pi>\<^sub>1 varFunList) :::= uInput) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem varFunList with G) POST Q"
apply(rule_tac varSolList="varSolList" and varFunList="varFunList" and uInput="uInput" in dSolve)
subgoal using varSolDef by simp
subgoal
  apply(rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
  using assms by auto
subgoal using uniqHyp by simp
using diffAssgn by simp

(* As before, we keep refining the rule dSolve. This time we find the necessary restrictions on 
to attain uniqueness. *)

(* OBSERVATIONS *)
term "unique_on_bounded_closed t0 T x0 f X L"
thm unique_on_bounded_closed_def
thm unique_on_bounded_closed_axioms_def
thm unique_on_closed_def
(* This equivalence helps Isabelle a lot. *)
thm closed_segment_eq_real_ivl

lemma conds4UniqSol:
assumes contHyp:"\<forall>xf\<in>set varFunList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a)))"
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real" and f::"real store \<Rightarrow> real"
assumes tHyp:"t \<ge> 0"
shows "\<forall>xf\<in>set varFunList. unique_on_bounded_closed 0 {0<--<t} 
(a (\<pi>\<^sub>1 xf)) (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a))) UNIV (if t = 0 then 1 else 1/(t+1))"
apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def
unique_on_closed_def compact_interval_def compact_interval_axioms_def)
oops

lemma conds4UniqSol:
assumes contHyp:"\<forall>xf\<in>set varFunList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a)))"
fixes x::"real \<Rightarrow> (real store) \<Rightarrow> real" and f::"real store \<Rightarrow> real"
assumes tHyp:"t \<ge> 0"
shows "\<forall>xf\<in>set varFunList. unique_on_bounded_closed 0 {0--t} 
(a (\<pi>\<^sub>1 xf)) (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a))) UNIV (if t = 0 then 1 else 1/(t+1))"
apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def 
unique_on_closed_def compact_interval_def compact_interval_axioms_def nonempty_set_def 
interval_def self_mapping_def self_mapping_axioms_def closed_domain_def global_lipschitz_def 
lipschitz_def)
apply(rule conjI)
subgoal using contHyp continuous_rhs_def by fastforce
apply(rule impI, rule ballI, rule conjI)
subgoal using contHyp continuous_rhs_def by auto
using closed_segment_eq_real_ivl tHyp by auto

lemma ubcStoreUniqueSol:
assumes tHyp:"t \<ge> 0"
assumes contHyp:"\<forall>xf\<in>set varFunList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a)))"
assumes eqDerivs:"\<forall> t \<ge> 0.\<forall>xf\<in>set varFunList.(\<pi>\<^sub>2 xf) (F t) = (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a))"
assumes Fsolves:"solvesStoreIVP F varFunList a G"
assumes solHyp:"solvesStoreIVP (\<lambda> t. toSol varSolList t (toInit a)) varFunList a G"
shows "(toSol varSolList t (toInit a)) = F t"
proof
  fix str::"string" show "(toSol varSolList t (toInit a)) str = F t str"
  proof(cases "str \<in> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs")
  case False
    then have notInVars:"str \<notin> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs" by simp
    from solHyp have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs \<longrightarrow> 
    (toSol varSolList t (toInit a)) str = a str"
    by (simp add: solvesStoreIVP_def) 
    hence 1:"(toSol varSolList t (toInit a)) str = a str" using tHyp notInVars by blast
    from Fsolves have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<union> varDiffs \<longrightarrow> F t str = a str" 
    by (simp add: solvesStoreIVP_def) 
    then have 2:"F t str = a str" using tHyp notInVars by blast
    thus "toSol varSolList t (toInit a) str = F t str" using 1 and 2 by simp
  next case True
    then have strIsXvar:"str \<in> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>) \<or> str \<in> varDiffs" by simp
    moreover
    {assume "str \<in> (\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>)" from this obtain f::"((char list \<Rightarrow> real) \<Rightarrow> real)" where 
      strFhyp:"(str, f) \<in> set varFunList" by fastforce
    (* Expand hypothesis for arbitrary solution. *)
    from Fsolves and tHyp have "(\<forall> xf \<in> set varFunList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP 
    (\<lambda>t r. \<pi>\<^sub>2 xf (F t)) withInitCond  0 \<mapsto> a (\<pi>\<^sub>1 xf)) {0<--<t} UNIV)" by (simp add: solvesStoreIVP_def)
    then have "\<forall> xf \<in> set varFunList.((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode (\<lambda>t r. (\<pi>\<^sub>2 xf) (F t))){0<--<t} UNIV 
    \<and> F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" by (simp add: solves_ivp_def)
    (* Re-express hypothesis for arbitrary solution in terms of user solution.*)
    hence "\<forall> xf \<in> set varFunList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode 
    (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a)))){0<--<t} UNIV \<and> F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" 
    using eqDerivs tHyp by (auto simp: solves_ode_def open_segment_eq_real_ivl has_vderiv_on_def)
    then have 1:"((\<lambda>t. F t str) solvesTheIVP (\<lambda>t r. f (toSol varSolList t (toInit a))) 
    withInitCond  0 \<mapsto> a str) {0<--<t} UNIV" using strFhyp solves_ivp_def by fastforce
    (* Expand hypothesis for user's solution. *)
    from solHyp and strFhyp have 2:"((\<lambda> t. toSol varSolList t (toInit a) str) solvesTheIVP 
    (\<lambda>t r. f (toSol varSolList t (toInit a))) withInitCond  0 \<mapsto> a str) {0<--<t} UNIV" 
    using solvesStoreIVP_def tHyp by fastforce
    (* Show user's solution and arbitrary solution are the same. *)
    from tHyp and contHyp have "\<forall> xf \<in> set varFunList. unique_on_bounded_closed 0 {0--t} (a (\<pi>\<^sub>1 xf)) 
    (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit a))) UNIV (if t = 0 then 1 else 1/(t+1))" 
    using conds4UniqSol by blast
    
    then have 3:"unique_on_bounded_closed 0 {0--t} (a str) (\<lambda>t r. f (toSol varSolList t (toInit a)))
    UNIV (if t = 0 then 1 else 1/(t+1))" using strFhyp 
    from 1 2 and 3 have "toSol varSolList t (toInit a) str = F t str"
    using unique_on_bounded_closed.ivp_unique_solution by blast}
    moreover
    {assume "str \<in> varDiffs"
      then obtain x where xDef:"str = vdiff x" by (auto simp: varDiffs_def)
      have "toSol varSolList t (toInit a) str = F t str "
      proof(cases "x \<in> set (map \<pi>\<^sub>1 varFunList)")
      case True
      then obtain f::"((char list \<Rightarrow> real) \<Rightarrow> real)" where 
      strFhyp:"(x, f) \<in> set varFunList" by fastforce
      from this Fsolves and tHyp have Fhyp:"F t str = f (F t)" 
      using solvesStoreIVP_def xDef by fastforce
      from strFhyp solHyp and tHyp have "toSol varSolList t (toInit a) str = 
      f (toSol varSolList t (toInit a))" using solvesStoreIVP_def xDef by fastforce
      then show ?thesis using Fhyp tHyp eqDerivs strFhyp by fastforce  
      next
      case False
      then have strHyp:"str \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set varFunList\<rbrakk>\<rbrakk>)" 
      using xDef \<open>str \<in> varDiffs\<close> 
      vdiff_inj by (metis (no_types, lifting) DiffI imageE set_map) 
      from this Fsolves and tHyp have "F t str = 0" 
      using solvesStoreIVP_def by simp
      also have "toSol varSolList t (toInit a) str = 0" 
      using strHyp solHyp tHyp solvesStoreIVP_def by simp
      ultimately show ?thesis by simp
      qed}
    ultimately show "toSol varSolList t (toInit a) str = F t str" by blast
  qed
qed

theorem dSolveUBC:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and contHyp:"\<forall> st. \<forall> t \<ge> 0.\<forall>xf\<in>set varFunList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit st)))"
and solves:"\<forall> st. solvesStoreIVP (\<lambda> t. toSol varSolList t (toInit st)) varFunList st G"
and eqDerivsHyp:"\<forall> st. \<forall> X. solvesStoreIVP X varFunList st G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall>xf\<in>set varFunList.(\<pi>\<^sub>2 xf) (X t) = (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit st)))"
and diffAssgn:"\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r\<in>{0<--<t}. G (toSol varSolList r (toInit st))) \<longrightarrow> 
\<lfloor>wp ((map \<pi>\<^sub>1 varFunList :::= uInput) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem varFunList with G) POST Q"
apply(rule_tac varFunList="varFunList" and varSolList="varSolList" and uInput="uInput" in dSolve)
subgoal using varSolDef by simp
subgoal using solves by simp
subgoal by (clarify, rule ubcStoreUniqueSol, auto simp: contHyp eqDerivsHyp solves)
subgoal using diffAssgn by simp
done

theorem dSolve_toSolveUBC:
assumes varSolDef:"varSolList = cross_list (map \<pi>\<^sub>1 varFunList) uInput"
and distinctHyp:"distinct (map \<pi>\<^sub>1 varFunList)" 
and lengthHyp:"length varFunList = length uInput"
and varsHyp:"\<forall> var \<in> set (map \<pi>\<^sub>1 varFunList). var \<notin> varDiffs"
and initHyp:"\<forall> st. \<forall> varSol \<in> set varSolList. (\<pi>\<^sub>2 varSol) 0 st = st (\<pi>\<^sub>1 varSol)"
and keyFact:"\<forall> st. \<forall> funSol \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput).
\<forall>t\<ge>0. frechet_derivative (\<lambda>r. \<pi>\<^sub>2 funSol r (toInit st)) (at t within {0<--< (2 *\<^sub>R t)}) t =
      \<pi>\<^sub>1 funSol (toSol (cross_list (map \<pi>\<^sub>1 varFunList) uInput) t (toInit st))"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol varSolList t (toInit st))"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. ((\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol varSolList t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set varFunList. 
(\<lambda>t. (toSol varSolList t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>xf\<in>set varFunList. toSol varSolList 0 (toInit st) (\<pi>\<^sub>1 xf) = st (\<pi>\<^sub>1 xf)"
and contHyp:"\<forall> st. \<forall> t \<ge> 0.\<forall>xf\<in>set varFunList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit st)))"
and eqDerivsHyp:"\<forall> st. \<forall> X. solvesStoreIVP X varFunList st G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall>xf\<in>set varFunList.(\<pi>\<^sub>2 xf) (X t) = (\<pi>\<^sub>2 xf) (toSol varSolList t (toInit st)))"
and diffAssgn: "\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol varSolList r (toInit st))) \<longrightarrow> 
\<lfloor>wp (((map \<pi>\<^sub>1 varFunList) :::= uInput) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem varFunList with G) POST Q"
apply(rule_tac varSolList="varSolList" and varFunList="varFunList" and uInput="uInput" in dSolveUBC)
subgoal using varSolDef by simp
subgoal using contHyp by simp
subgoal
  apply(rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
  using assms by auto
  (*apply(rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
  subgoal using varSolDef by simp
  subgoal using distinctHyp by simp
  subgoal using lengthHyp by simp
  subgoal using varsHyp by simp
  subgoal
    using solHyp1
    apply(simp add: has_vderiv_on_def has_vector_derivative_def)
    apply(clarify, rename_tac a f sol t)
    apply(subgoal_tac "\<exists> x. (x, f) \<in> set varFunList")
    defer
    subgoal by (metis cross_listE3 in_set_impl_in_set_zip2 length_map zip_map_fst_snd)
    apply(erule exE)
    apply(subgoal_tac "((\<lambda>t. toSol varSolList t (toInit a) x) has_derivative 
    (\<lambda>xa. xa \<cdot> f (toSol varSolList t (toInit a)))) (at t within {0--t})")
    defer
    subgoal by fastforce
    apply(simp add: varSolDef)
    apply(simp add: someI)
    thm someI
    (*
    proof(clarify, rename_tac a f sol t)
    fix a and f and sol and t::"real"
    assume "(f, sol) \<in> set (cross_list (map \<pi>\<^sub>2 varFunList) uInput)" and "0 \<le> t"
    then obtain x::"string" where "(x, f) \<in> set varFunList"
    by (metis cross_listE3 in_set_impl_in_set_zip2 length_map zip_map_fst_snd) 
    from this and solHyp1 have "((\<lambda>t. (toSol varSolList t (toInit a)) x) 
    has_vderiv_on (\<lambda>t. f (toSol varSolList t (toInit a)))) {0--t}" using \<open>0 \<le> t\<close> by fastforce
    hence "\<forall>r\<in>{0--t}. ((\<lambda>t. (toSol varSolList t (toInit a)) x) 
    has_derivative (\<lambda>t. t *\<^sub>R f (toSol varSolList t (toInit a)))) (at r within {0--t})" 
    using has_vderiv_on_def has_vector_derivative_def *)
    sorry
  subgoal using initHyp by simp
  subgoal using guardHyp by simp
  subgoal using solHyp1 solHyp2 solHyp3 by simp
  done*)
subgoal using eqDerivsHyp by simp
using diffAssgn by simp


(* OBSERVATIONS *)
thm derivative_intros(173)
thm derivative_intros
thm derivative_intros(176)
thm derivative_eq_intros(8)
thm derivative_eq_intros
thm continuous_intros

lemma myDeriv: "(f has_derivative (\<lambda> t. g t)) (at t within {0<--<2 \<cdot> t}) \<Longrightarrow> (frechet_derivative f (at t within {0<--<2 \<cdot> t}) t = g t)"
apply(simp add: frechet_derivative_def)
by (metis frechet_derivative_at someI)
sorry

lemma "(f has_vderiv_on (\<lambda> t. g t)) {0 -- t} \<Longrightarrow> (frechet_derivative f (at t) t = g t)"
apply(simp add: frechet_derivative_def has_vderiv_on_def has_vector_derivative_def)
oops

thm frechet_derivative_at someI

(* Example of hybrid program verified with differential solve. *)
declare vdiff_def [simp]
lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (ODEsystem [(''pos'',(\<lambda> s. s ''vel''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
apply(rule_tac varSolList="[(''pos'', \<lambda> t s. s ''vel'' \<cdot> t + s ''pos'')]" and 
               varFunList="[(''pos'',(\<lambda> s. s ''vel''))]" and 
               uInput="[\<lambda> t s. s ''vel'' \<cdot> t + s ''pos'']" in dSolve_toSolveUBC) (* 12 subgoals *)
apply(simp_all add: override_on_def varDiffs_def)
subgoal
  apply(clarify)
  apply(rule myDeriv)
  apply(rule_tac f'1="\<lambda> x. st ''vel''" and g'1="\<lambda> x. 0" in derivative_eq_intros(8))
  apply(simp_all)
  apply(simp add: has_derivative_def)
  apply(simp add: bounded_linear_def)
  apply(simp add: linear_def)
  apply(simp add: Real_Vector_Spaces.additive_def)
  apply(simp add: linear_axioms_def)
  sorry (* we need to define our own frechet derivative... *)*)
subgoal 
  apply(clarify)
  apply(rule_tac f'1="\<lambda> x. st ''vel''" and g'1="\<lambda> x. 0" in derivative_intros(173))(* 3 goals appear. *)
  apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))           (* 3 goals appear. *)
  by(auto intro: derivative_intros)
subgoal by (clarsimp, rule continuous_intros)
subgoal 
  apply(clarsimp)
  apply(drule solves_store_ivpD(3))
  by(simp add: varDiffs_def)
subgoal 
  apply(simp add: wp_trafo mass_gets_def, clarify)
  by (meson add_strict_increasing2 less_eq_real_def mult_nonneg_nonneg)
done
declare vdiff_def [simp del]

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

    IN THIS VERSION WE ARE GOING TO TRY THE SECOND (2) APPROACH
*)

(* UPDATE: Here's the situation...
      · Method 3 is ruled out because of the following argument (provided by Andreas Lochbihler). 
      Suppose that you are able to create operators "D" such that "D:(a' \<Rightarrow> bool) \<Rightarrow> (a' \<Rightarrow> bool)" 
      depends on the inductive structure of its argument. Then you could define a D such that 
      D(\<lambda> x. P x) = (\<lambda> x. True) and D(\<lambda> x. P x \<and> True) = (\<lambda> x. False). Notice then that by the 
      "substitution axiom", (\<lambda> x. False) = D(\<lambda> x. True \<and> True) = D(\<lambda> x. True) = (\<lambda> x. True).
      Picking any arbitrary "x::'a", we would have a proof of True = False within Isabelle. =/
      · Method 2 is then the suggested approach. However, as shown in the dInvForVars-lemma (below),
      it requires us to talk about the semantics of differential variables. This in turn requires us
      to expand our domain of work from "string" to "string \<union> string'", or modify our definitions 
      so that "solvesStoreIVP" has a special treatment for the subset "{d@\<alpha>| \<alpha>::string }". However,
      doing any of these will affect "solvesStoreIVP" in a way that we won't be able to generalize
      later to many variables with the approach: 
        "(D[x] = f, D[x]=g with G) = (D[x]=f with G) \<inter> (D[y]=g with G)"
      Moreover, assuming that we can use this approach in a way that it generalizes nicely to many
      variables, we still have to learn how to define "simprocs in Isabelle/ML" so that we can
      automate the tool enough that it competes with KeYmaera X's invariant rules.
      · Finally, method 1 is quickly discarded by Andreas Lochbihler.
*) 

term "\<lambda> (t::real). (f::real store \<Rightarrow> real) (x t)"

term "\<lambda> s. s ''x'' > (0::real)"
term "(\<lambda> (s::real store). (P::real store \<Rightarrow> string \<Rightarrow> bool) (s::real store) str)"
definition predToPrime :: "string \<Rightarrow> (real store \<Rightarrow> string \<Rightarrow> bool) \<Rightarrow> (real store \<Rightarrow> bool)" where
"predToPrime str Q = (\<lambda> s. Q s (''d''@str))"
value "(\<lambda> s var. s var > s ''y'' \<or> s var \<noteq> 0) a ''x''"
value "(predToPrime ''x'' (\<lambda> s var. s var > s ''y'' \<or> s var \<noteq> 0)) a"

thm derivative_eq_intros
thm solvesStoreIVP_def

lemma dInvForVars: 
assumes "\<forall> c. (a,c) \<in> ((''d''@x) ::= f) \<longrightarrow> (\<lambda> s. s (''d''@y)) c = 0"
shows "(\<lambda> s. s y) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem [(x,f)] with (\<lambda> s. True)) \<longrightarrow> (\<lambda> s. s y) c = 0)"
proof(clarify)
fix c assume "a y = 0" and cHyp:"(a, c) \<in> ODEsystem [(x,f)] with (\<lambda>s. True)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> F 0 = a \<and> F t = c \<and> solvesStoreIVP F [(x,f)] a (\<lambda> s. True)" 
using guarDiffEqtn_def solvesStoreIVP_def by auto
show "c y = 0"
  proof(cases "y=x")
    case True
    then have "a x = 0" using \<open>a y = 0\<close> by blast 
    from FHyp have "c = a ((''d''@x) := f a)" sorry (* behavior of store-solutions on primed vars. *)
    hence "(a,c) \<in> ((''d''@x) ::= f)" by (simp add: gets_def)
    from this and assms have "c (''d''@y) = 0" by simp
    hence derivInC: "c (''d''@x) = 0" using \<open>y=x\<close> by simp
    then have dIsZero:"\<forall> s \<in> {0 -- t}. f (F s) = 0" (* derivative is zero. *)
    using FHyp and solvesStoreIVP_def sorry 
    hence "\<forall> s \<in> {0 -- t}. F s x = a x" sorry (* Integrating *)
    thus "c y = 0" using \<open>y=x\<close> FHyp \<open>a y = 0\<close> by fastforce
  next
    case False
    from this and FHyp  have "\<forall>r\<in>{0--t}. \<forall>y. y \<noteq> x \<longrightarrow> F r y = a y" 
    by (meson solvesStoreIVP_def)
    then show ?thesis using \<open>y \<noteq> x\<close> \<open>a y = 0\<close> FHyp 
    by (metis ends_in_segment(2)) 
  qed
qed

lemma dInvForSums:
assumes "\<forall> c. (a,c) \<in> ((''d''@x) ::= f) \<longrightarrow> (\<lambda> s. f s + g s) c = 0"
shows "(\<lambda> s. f s + g s) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem [(x,f)] with (\<lambda> s. True)) \<longrightarrow> (\<lambda> s. f s + g s) c = 0)"
sorry

lemma 
fixes g::"real store \<Rightarrow> real"
assumes "\<forall> c. (a,c) \<in> ((''d''@x) ::= f) \<longrightarrow> g c = 0"
shows "g a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem [(x,f)] with (\<lambda> s. s = s)) \<longrightarrow> g c = 0)"
sorry

lemma pelim_dInv:
assumes "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE Q (ODEsystem [(x,f)] with G) POST Q"
sorry

theorem dInv:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st x" (* Notice that the conjunction below is not valid. *)
assumes "PRE G ((''d''@x) ::= f) POST (\<lambda> s. Q s (''d''@x))"
shows " PRE P (ODEsystem [(x,f)] with G) POST (\<lambda> s. Q s x)"
proof(clarify)
fix a b assume "(a, b) \<in> rdom \<lceil>P\<rceil>"
from this have "a = b \<and> P a" by (metis rdom_p2r_contents)
have "\<forall> c. (a,c) \<in> (ODEsystem [(x,f)] with G) \<longrightarrow> Q c x"
proof(clarify)
fix c assume "(a, c) \<in> ODEsystem [(x,f)] with G"
show "Q c x"
sorry
qed
thus "(a, b) \<in> wp (ODEsystem [(x,f)] with G ) \<lceil>\<lambda>s. Q s x\<rceil>" sorry
qed

theorem dInv2:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st x" (* Notice that the conjunction below is not valid. *)
assumes "PRE (\<lambda> s. P s \<and> G s) ((''d''@x) ::= f) POST (\<lambda> s. Q s (''d''@x))"
shows " PRE P (ODEsystem [(x,f)] with G) POST (\<lambda> s. Q s x)"
sorry

theorem dInv3:
assumes "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st"
assumes "PRE G ((''d''@x) ::= f) POST (deriv_Pred Q)"
shows " PRE P (ODEsystem [(x,f)] with G) POST Q"
sorry

lemma "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      (ODEsystem [(''x'', \<lambda> s. s ''v'')] with (\<lambda> s. True))
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
      (ODEsystem [(''x'', \<lambda> s. s ''v'')] with (\<lambda> s. True))
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
      (ODEsystem [(''x'', \<lambda> s. s ''v'')] with (\<lambda> s. True))
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
      ((ODEsystem [(''x'', \<lambda> s. s ''v''),(''vel'',\<lambda> s. s ''acc'')] with (\<lambda> s. True)))
      )
      POST (\<lambda> s. (s ''station'' \<ge> s ''pos'') \<and> (s ''vel'' = 0 \<longleftrightarrow> s ''station'' = s ''pos''))"
      apply(rule_tac xfList ="(\<lambda> t. \<lambda> s. s ''vel'' \<cdot> t + s ''pos'')" in dSolveUBC)
      oops

declare [[show_types]]
declare [[show_sorts]]

      
end