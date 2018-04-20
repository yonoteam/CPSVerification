section {* my cool theory *}
theory VC_diffKAD
imports
Main
"afpModified/VC_KAD"
"Ordinary_Differential_Equations.IVP/Initial_Value_Problem"

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

lemma rel_ad_proj_chrctrztn:"\<Delta>\<^sup>c\<^sub>1 R = Id - (\<lceil>\<lambda> x. x \<in> (\<pi>\<^sub>1\<lbrakk>R\<rbrakk>)\<rceil>)"
by(simp add: p2r_def image_def fst_def rel_ad_def, fastforce)

lemma boxProgrPred_IsProp: "wp R \<lceil>P\<rceil> \<subseteq> Id"
by (simp add: rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def)

lemma boxProgrRel_iso:"P \<subseteq> Q \<Longrightarrow> wp R P \<subseteq> wp R Q"
by (simp add: rel_antidomain_kleene_algebra.dka.dom_iso rel_antidomain_kleene_algebra.fbox_iso)

lemma rdom_p2r_contents:"(a, b) \<in> rdom \<lceil>P\<rceil> = ((a = b) \<and> P a)" 
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

(* A "cartesian product" of lists. *)
fun cross_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" (infixl "\<otimes>" 63) where
"[] \<otimes> list = []"|
"list \<otimes> [] = []"|
"(x # xtail) \<otimes> (y # ytail) = (x,y) # (xtail \<otimes> ytail)"

primrec swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a" where "swap (x,y) = (y,x)"

primrec listSwap :: "('a \<times> 'b) list \<Rightarrow> ('b \<times> 'a) list" where
"listSwap [] = []" |
"listSwap (head # tail) = swap head # (listSwap tail)"

lemma listSwap_isMapSwap:"listSwap l = map swap l"
by(induct_tac l, auto)

lemma listSwap_crossList[simp]: "listSwap (l2 \<otimes> l1) = l1 \<otimes> l2"
apply(induction l1 l2 rule: cross_list.induct)
apply(metis cross_list.elims cross_list.simps(1) cross_list.simps(2) listSwap.simps(1))
apply(metis cross_list.simps(1) cross_list.simps(2) listSwap.simps(1))
by simp

lemma empty_crossListElim:
"[] = xList \<otimes> yList \<Longrightarrow>  [] = xList \<or> [] = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma tail_crossListElim:
"(x, y) # tail = xList \<otimes> yList \<Longrightarrow>  \<exists>xTail yTail. x # xTail = xList \<and> y # yTail = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma non_empty_crossListElim:
"(x, y) \<in> set (xList \<otimes> yList) \<Longrightarrow> x \<in> set xList \<and> y \<in> set yList"
by(induction xList yList rule: cross_list.induct, auto)

lemma crossList_map_projElim[simp]:"(map \<pi>\<^sub>1 list) \<otimes> (map \<pi>\<^sub>2 list) = list"
by(induct_tac list, auto)

lemma tail_crossList_map_projElim: 
"(x,y)#list = (map \<pi>\<^sub>1 l1) \<otimes> l2 \<Longrightarrow> \<exists> z tail. (x, z) # tail = l1"
proof-
assume hyp:"(x, y) # list = (map \<pi>\<^sub>1 l1) \<otimes> l2"
then have noEmpt:"(map \<pi>\<^sub>1 l1) \<noteq> [] \<and> l2 \<noteq> []" by (metis cross_list.elims list.discI) 
from this obtain hd1 hd2 tl1 and tl2 where hd1Def:"(map \<pi>\<^sub>1 l1) = hd1 # tl1 \<and> l2 = hd2 # tl2" 
by (meson list.exhaust) 
then obtain z and tail where tailDef:"l1 = (hd1,z) # tail \<and> (map \<pi>\<^sub>1 tail) = tl1" by auto
moreover have "(x, y) # list = (hd1,hd2)#(tl1 \<otimes> tl2)" by (simp add: hd1Def hyp)
ultimately show ?thesis by simp
qed

lemma non_empty_crossList_map_projEx:
"\<forall> xzList. xzList = (map \<pi>\<^sub>1 xyList) \<otimes> zList \<longrightarrow> 
(y, z) \<in> set ((map \<pi>\<^sub>2 xyList) \<otimes> zList) \<longrightarrow> 
(\<exists> x. (x,y) \<in> set xyList \<and> (x,z) \<in> set xzList)"
by(simp, induction xyList zList rule: cross_list.induct, auto)

lemma crossList_length:
"length xList = length yList \<Longrightarrow> length (xList \<otimes> yList) = length xList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma crossList_lengthEx:
"length xList = length yList \<Longrightarrow> 
\<forall> x \<in> set xList. \<exists> y \<in> set yList. (x,y) \<in> set (xList \<otimes> yList)"
apply(induction xList yList rule: cross_list.induct)
subgoal by simp
subgoal by simp
apply(rule ballI, simp, erule disjE, simp) 
by blast

lemma tail_crossList_length:
"length (xList \<otimes> yList) = length (z # zTail) \<longrightarrow> 
(\<exists> x y xTail yTail. (xList = x # xTail) \<and> (yList = y # yTail) \<and> 
length (xTail \<otimes> yTail) = length zTail)"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma length_crossListProj1:
"length xList = length yList \<Longrightarrow> map \<pi>\<^sub>1 (xList \<otimes> yList) = xList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma length_crossListProj2:
"length xList = length yList \<Longrightarrow> map \<pi>\<^sub>2 (xList \<otimes> yList) = yList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma legnth_crossListEx1:
"length (xList \<otimes> yList) = length yList \<Longrightarrow> 
\<forall> y \<in> set yList. \<exists> x \<in> set xList. (x, y) \<in> set (xList \<otimes> yList)"
apply(induction xList yList rule: cross_list.induct, simp, simp)
by(rule ballI, simp, erule disjE, simp, blast)

lemma legnth_crossListEx2:
"length ((x#xTail) \<otimes> (y#yTail)) = length zList \<Longrightarrow> 
\<exists> z zTail. zList = z # zTail \<and> length zTail = length (xTail \<otimes> yTail)"
by(induction zList, simp_all)

lemma legnth_crossListEx3:
"\<forall> zList x y. length (xList \<otimes> yList) = length zList \<longrightarrow> (x, y) \<in> set (xList \<otimes> yList) \<longrightarrow> 
(\<exists> z. (x, z) \<in> set (xList \<otimes> zList) \<and> (y, z) \<in> set ((map \<pi>\<^sub>2 (xList \<otimes> yList)) \<otimes> zList))"
apply(induction xList yList rule: cross_list.induct, simp, simp, clarify)
apply(rename_tac x xTail y yTail zList u v)
apply(subgoal_tac "(u,v) = (x,y) \<or> (u,v) \<in> set (xTail \<otimes> yTail)")
apply(subgoal_tac "\<exists> z zTail. (zList = z # zTail) \<and> (length(xTail \<otimes> yTail) = length zTail)")
apply(erule disjE)
subgoal by auto
subgoal by fastforce
subgoal by (metis cross_list.simps(3) length_Suc_conv)
subgoal by simp
done

-- {* dL CALCULUS. *}
(* Observations *)
term "atLeastAtMost a (b::real)"
term "greaterThanLessThan a b"
thm atLeast_def
term "box a (b::real)"
thm box_def
thm solves_ode_def
term "f \<in> A \<rightarrow> B"
thm Pi_def
thm has_vderiv_on_def
thm has_vector_derivative_def
thm has_field_derivative_def
term "\<lambda> x. f has_real_derivative x"
thm has_derivative_def

(*  In this section we consider initial value problems (IVP) such as:
       x' t = f t (x t)    x 0 = x\<^sub>0 \<in> \<real>\<^sup>n
where f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n and x,x':\<real>\<rightarrow>\<real>\<^sup>n. *)
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

(* In our store implementation:
  · The solution "x:\<real>\<rightarrow>\<real>\<^sup>n" is changed for "F::real \<Rightarrow> real store" (i.e. real \<Rightarrow> string \<Rightarrow> real).
   The letter "x" is reserved for strings.
  · Instead of "f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n" we use "f::real store \<Rightarrow> real". This is for consistency with the
    "expressions" in assignments in VC_KAD.thy and because we mainly focus on "autonomous systems
    of ODE'S (i.e. systems of the form x'(t)=f(x(t))). *)

definition vdiff ::"string \<Rightarrow> string" where
"vdiff x = ''d[''@x@'']''" (* Alternatively, we could have use: "''d''@x@''/dt''" *)

definition varDiffs :: "string set" where
"varDiffs = {str. \<exists> x. str = vdiff x}"

lemma vdiff_inj:"vdiff x = vdiff y \<Longrightarrow> x = y"
by(simp add: vdiff_def)

lemma vdiff_noFixPoints:"str \<noteq> vdiff str"
by(simp add: vdiff_def)

lemma varDiffsI:"x = vdiff z \<Longrightarrow> x \<in> varDiffs"
by(simp add: varDiffs_def vdiff_def)

lemma varDiffsE:
assumes "x \<in> varDiffs"
obtains y where "x = ''d[''@y@'']'' "
using assms unfolding varDiffs_def vdiff_def by auto

lemma vdiff_invarDiffs:"vdiff str \<in> varDiffs"
by (simp add: varDiffsI)

definition solvesStoreIVP :: "(real \<Rightarrow> real store) \<Rightarrow> (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real store \<Rightarrow> (real store pred) \<Rightarrow> bool" 
("(_ solvesTheStoreIVP _ withInitState _ andGuard _)" [70, 70, 70, 70] 68) where
"solvesStoreIVP F xfList st G \<equiv>
(* F preserves the guard statement and F sends vdiffs-in-list to derivs. *)
(\<forall> t \<ge> 0. G (F t) \<and>  (\<forall> xf \<in> set xfList. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)) \<and> 
(* F preserves the rest of the variables and F sends derivs of constants to 0. *)
  (\<forall> str. (str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str) \<and> 
  (str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> F t (vdiff str) = 0)) \<and> 
(* F solves the induced IVP. *)
  (\<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
  withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0..t} UNIV))"
  
lemma solves_store_ivpI:
assumes "\<forall> t \<ge> 0. G (F t)"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> F t (vdiff str) = 0" 
  and "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0..t} UNIV"
shows "F solvesTheStoreIVP xfList withInitState st andGuard G"
using assms solvesStoreIVP_def by auto

named_theorems solves_store_ivpE "elimination rules for solvesStoreIVP"

lemma [solves_store_ivpE]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G"
shows "\<forall> t \<ge> 0. G (F t)"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> F t (vdiff str) = 0"
  and "\<forall> t \<ge> 0.\<forall> xf \<in> set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0..t} UNIV"
using assms solvesStoreIVP_def by auto

lemma [solves_store_ivpE]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G"
shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str"
proof(clarify, rename_tac x)
fix x assume "x \<notin> varDiffs"
from assms and solves_store_ivpE(5) 
have "\<forall> f. (x,f)\<in>set xfList \<longrightarrow> ((\<lambda>t. F t x) solvesTheIVP (\<lambda>t r. f (F t)) withInitCond 
0 \<mapsto> st x) {0..0} UNIV" by force
hence "x \<in>(\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<Longrightarrow> F 0 x = st x" using solves_ivpD(2) by fastforce
also have "x \<notin>(\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<Longrightarrow> F 0 x = st x" 
using assms and solves_store_ivpE(2) by simp
ultimately show "F 0 x = st x" using \<open>x \<notin> varDiffs\<close> by auto
qed

named_theorems solves_store_ivpD "computation rules for solvesStoreIVP"

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "t \<ge> 0"
shows "G (F t)"
using assms solves_store_ivpE(1) by blast

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "t \<ge> 0"
  and "str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs"
shows "F t str = st str"
using assms solves_store_ivpE(2) by simp

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "t \<ge> 0"
  and "str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)"
shows "F t (vdiff str) = 0"
using assms solves_store_ivpE(3) by simp

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "t \<ge> 0"
  and "xf \<in> set xfList"
shows "(F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
using assms solves_store_ivpE(4) by simp

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "t \<ge> 0"
  and "xf \<in> set xfList"
shows "((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0..t} UNIV" 
using assms solves_store_ivpE(5) by simp

lemma [solves_store_ivpD]:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G" 
  and "str \<notin> varDiffs"
shows "F 0 str = st str" 
using assms solves_store_ivpE(6) by simp

thm solves_store_ivpE
thm solves_store_ivpD

definition guarDiffEqtn :: "(string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> (real store pred) \<Rightarrow> 
real store rel" ("ODEsystem _ with _ " [70, 70] 61) where
"ODEsystem xfList with G = {(st,F t) |st t F. t \<ge> 0 \<and> solvesStoreIVP F xfList st G}"

-- "Differential Weakening."
lemma box_evol_guard:"Id \<subseteq> wp (ODEsystem xfList with G) \<lceil>G\<rceil>"
apply(simp add: rel_antidomain_kleene_algebra.fbox_def rel_ad_def guarDiffEqtn_def p2r_def)
using solves_store_ivpD(1) by force

theorem dWeakening: 
assumes guardImpliesPost: "\<lceil>G\<rceil> \<subseteq> \<lceil>Q\<rceil>"
shows "PRE P (ODEsystem xfList with G) POST Q"
using assms and box_evol_guard by (metis (no_types, hide_lams) d_p2r 
order_trans p2r_subid rel_antidomain_kleene_algebra.fbox_iso)

(* Example of hybrid program verified with differential weakening. *)  
lemma "PRE (\<lambda> s. s ''x'' = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' \<ge> 0))
      POST (\<lambda> s. s ''x'' \<ge> 0)"
using dWeakening by blast

lemma "PRE (\<lambda> s. s ''x'' = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''x'' + 1))] with (\<lambda> s. s ''x'' \<ge> 0))
      POST (\<lambda> s. s ''x'' \<ge> 0)"
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
subgoal proof(clarify)
from boxDiffC have diffHyp:"\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> C c"
using guarDiffEqtn_def wp_trafo by (metis (no_types, lifting) Domain.intros r2p_def)
fix t::real assume tHyp:"0 \<le> t"
then have odeF:"(a,F t) \<in> (ODEsystem xfList with G)" using FisSol guarDiffEqtn_def by auto 
from this diffHyp and tHyp show "G (F t) \<and> C (F t)" using solves_store_ivpD(1) FisSol by blast
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
ultimately have "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> Q c"
using guarDiffEqtn_def boxDiffCond_impliesAllTimeInCond by auto
from this and \<open>a = b \<and> P a\<close> show "(a,b) \<in> wp (ODEsystem xfList with G) \<lceil>Q\<rceil>" 
by (simp add: boxProgrPred_chrctrztn)
qed 

-- "Solve Differential Equation."
definition "vderiv_of f S = (SOME f'. (f has_vderiv_on f') S)"
abbreviation varDiffs_to_zero ::"real store \<Rightarrow> real store" ("d2z") where
"d2z a \<equiv> (override_on a (\<lambda> str. 0) varDiffs)" 

lemma varDiffs_to_zero_beginning[simp]: "take 2 x \<noteq> ''d['' \<Longrightarrow> (d2z a) x = a x"
apply(simp add: varDiffs_def override_on_def vdiff_def)
by(fastforce)

lemma override_on_upd:"x \<in> X \<Longrightarrow> (override_on f g X)(x := z) = (override_on f (g(x := z)) X)"
by(rule ext, simp add: override_on_def)

primrec state_list_upd :: "((real \<Rightarrow> real store \<Rightarrow> real) \<times> string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real \<Rightarrow> real store \<Rightarrow> real store" where
"state_list_upd [] t a  = a"|
"state_list_upd (uxf # tail) t a = (state_list_upd tail t a)
(     (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (\<pi>\<^sub>1 uxf) t a, 
vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (if t = 0 then (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) a
else vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<..< (2 *\<^sub>R t)} t))"

abbreviation state_list_cross_upd ::"real store \<Rightarrow>  (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> (char list \<Rightarrow> real)" ("_[_\<leftarrow>_] _" [64,64,64] 63) where
"s[xfList\<leftarrow>uInput] t \<equiv> state_list_upd (uInput \<otimes> xfList) t s"

lemma state_list_cross_upd_empty[simp]: "(a[[]\<leftarrow>list] t) = a"
by(induction list, simp_all)

lemma state_list_cross_upd_its_vars:
"distinct (map \<pi>\<^sub>1 xfList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 xfList). var \<notin> varDiffs) \<longrightarrow>
length (xfList) = length (uInput) \<longrightarrow> (\<forall> uxf \<in>set (uInput \<otimes> xfList). 
(a[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = (\<pi>\<^sub>1 uxf) t a)"
apply(simp, induction xfList uInput rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac x f xfTail u uTail s y g)
fix x y::"string" and f g::"real store \<Rightarrow> real" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real)list"
and xfTail::"(string \<times> (real store \<Rightarrow> real))list" and u s::"real \<Rightarrow> real store \<Rightarrow> real"
let ?gLHS = "(a[((x, f) # xfTail)\<leftarrow>(u # uTail)] t) (\<pi>\<^sub>1 (\<pi>\<^sub>2 (s, y, g)))"
let ?goal = "?gLHS = \<pi>\<^sub>1 (s, y, g) t a"
assume IH:"distinct (map \<pi>\<^sub>1 xfTail) \<longrightarrow> (\<forall> xf \<in> set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs) \<longrightarrow>
length xfTail = length uTail \<longrightarrow> (\<forall>uxf\<in>set (uTail \<otimes> xfTail). 
(a[xfTail\<leftarrow>uTail] t) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = \<pi>\<^sub>1 uxf t a)"
and distHyp:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and varsHyp:"\<forall>xf \<in> set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length ((x, f) # xfTail) = length (u # uTail)"
then have keyHyp:"\<forall>uxf\<in>set (uTail \<otimes> xfTail). 
(a[xfTail\<leftarrow>uTail] t) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = \<pi>\<^sub>1 uxf t a" by fastforce
assume "(s, y, g) \<in> set ((u # uTail) \<otimes> ((x, f) # xfTail))" 
from this have "(s, y, g) = (u, x, f) \<or> (s, y, g) \<in> set (uTail \<otimes> xfTail)" by simp
moreover
{assume eq:"(s, y, g) = (u, x, f)" 
  then have "?gLHS = ((a[xfTail\<leftarrow>uTail] t)(y := s t a, vdiff y := if t = 0 then g a 
  else vderiv_of (\<lambda> r. s r a) {0<..< (2 *\<^sub>R t)} t)) y" by simp
  also have "((a[xfTail\<leftarrow>uTail] t)(y := s t a, vdiff y := if t = 0 then g a 
  else vderiv_of (\<lambda> r. s r a) {0<..< (2 *\<^sub>R t)} t)) y = s t a" 
  using eq by (simp add: vdiff_def)
  ultimately have ?goal by simp}
moreover
{assume yTailHyp:"(s, y, g) \<in> set (uTail \<otimes> xfTail)"
  from this and keyHyp have 3:"(a[xfTail\<leftarrow>uTail] t) y = s t a" by fastforce
  from yTailHyp and distHyp have 2:"y \<noteq> x" using non_empty_crossListElim by force 
  from yTailHyp and varsHyp have 1:"y \<noteq> vdiff x" 
  using non_empty_crossListElim vdiff_invarDiffs by fastforce 
  from 1 and 2 have "?gLHS = (a[xfTail\<leftarrow>uTail] t) y"  by (simp)
  then have "?goal" using 3 by simp}
ultimately show ?goal by blast
qed

lemma state_list_cross_upd_its_dvars:
assumes lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp3:"\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists> g. (a[xfList\<leftarrow>uInput] 0) = (override_on a g varDiffs)"
using assms proof(induction xfList uInput rule: cross_list.induct)
case (1 list)
have "(a[[]\<leftarrow>list] 0) = a" by simp
also have "override_on a a varDiffs = a" 
unfolding override_on_def by simp
ultimately show ?case by metis 
next
case (2 xf xfTail)
have "(a[(xf # xfTail)\<leftarrow>[]] 0) = a" by simp
also have "override_on a a varDiffs = a" 
unfolding override_on_def by simp
ultimately show ?case by metis 
next
case (3 xf xfTail u uTail)
let ?gLHS="(a[(xf # xfTail)\<leftarrow>(u # uTail)] 0)"
have observ:"vdiff (\<pi>\<^sub>1 xf) \<in> varDiffs" by (auto simp: varDiffs_def)
assume IH:"length xfTail = length uTail \<Longrightarrow> \<forall>xf\<in>set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs \<Longrightarrow>
\<forall>uxf\<in>set (uTail \<otimes> xfTail). \<pi>\<^sub>1 uxf 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) \<Longrightarrow>
\<exists>g. (a[xfTail\<leftarrow>uTail] 0) = override_on a g varDiffs"
assume "length (xf # xfTail) = length (u # uTail)"
and solHyp:"\<forall>uxf\<in>set ((u # uTail) \<otimes> (xf # xfTail)). \<pi>\<^sub>1 uxf 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and no_varDiffs:"\<forall>xf\<in>set (xf # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
from this and IH obtain g where "(a[xfTail\<leftarrow>uTail] 0) = override_on a g varDiffs" by force
then have 1:"?gLHS = (override_on a g varDiffs)(\<pi>\<^sub>1 xf := u 0 a, vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" by simp
also have 2:"(override_on a g varDiffs)(\<pi>\<^sub>1 xf := u 0 a, vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a) = 
(override_on a g varDiffs)(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" 
using override_on_def varDiffs_def "3.prems"(2) solHyp by auto 
also have 3:"(override_on a g varDiffs)(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a) = 
(override_on a (g(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)) varDiffs)" using observ and override_on_upd by force
ultimately show ?case by auto
qed

lemma state_list_cross_upd_uxf_on_x:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)"
shows "(a[xfList\<leftarrow>uInput] t) x = u t a"
using assms and state_list_cross_upd_its_vars by force

abbreviation state_to_sol::"real store \<Rightarrow>  (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> (char list \<Rightarrow> real)" 
("sol _[_\<leftarrow>_] _" [64,64,64] 63) where "sol s[xfList\<leftarrow>uInput] t  \<equiv> d2z s[xfList\<leftarrow>uInput] t"

lemma prelim_dSolve:
assumes solHyp:"(\<lambda>t. sol a[xfList\<leftarrow>uInput] t) solvesTheStoreIVP xfList withInitState a andGuard G"
and uniqHyp:"\<forall> X. solvesStoreIVP X xfList a G \<longrightarrow> (\<forall> t \<ge> 0. (sol a[xfList\<leftarrow>uInput] t) = X t)"
and diffAssgn: "\<forall>t\<ge>0. G (sol a[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol a[xfList\<leftarrow>uInput] t)"
shows "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> Q c"
proof(clarify)
fix c assume "(a,c) \<in> (ODEsystem xfList with G)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto 
from this and uniqHyp have "(sol a[xfList\<leftarrow>uInput] t) = F t" by blast
then have cHyp:"c = (sol a[xfList\<leftarrow>uInput] t)" using FHyp by simp
from solHyp have "G (sol a[xfList\<leftarrow>uInput] t)" by (simp add: solvesStoreIVP_def FHyp)
then show "Q c" using diffAssgn FHyp cHyp by auto
qed

theorem wlp_guard_inv:
assumes solHyp:"solvesStoreIVP (\<lambda>t. sol a[xfList\<leftarrow>uInput] t) xfList a G"
and uniqHyp:"\<forall> X. solvesStoreIVP X xfList a G \<longrightarrow> (\<forall> t \<ge> 0. (sol a[xfList\<leftarrow>uInput] t) = X t)"
and diffAssgn: "\<forall>t\<ge>0. G (sol a[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol a[xfList\<leftarrow>uInput] t)"
shows "\<lfloor>wp (ODEsystem xfList with G ) \<lceil>Q\<rceil>\<rfloor> a "
apply(simp add: r2p_def, subst boxProgrRel_chrctrztn2)
apply(simp_all add: p2r_def, rule_tac uInput="uInput" in prelim_dSolve)
by (simp_all add: r2p_def Domain_unfold assms)

theorem dSolve:
assumes solHyp:"\<forall>st. solvesStoreIVP (\<lambda>t. sol st[xfList\<leftarrow>uInput] t) xfList st G"
and uniqHyp:"\<forall> st. \<forall> X. solvesStoreIVP X xfList st G \<longrightarrow> (\<forall> t \<ge> 0.(sol st[xfList\<leftarrow>uInput] t) = X t)"
and diffAssgn: "\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. G (sol st[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol st[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(clarsimp, subgoal_tac "a=b")
apply(clarify, subst boxProgrPred_chrctrztn)
apply(simp_all add: p2r_def)
apply(rule_tac uInput="uInput" in prelim_dSolve)
apply(simp add: solHyp, simp add: uniqHyp)
by (metis (no_types, lifting) diffAssgn)

(*By Picard-Lindel\"of, there's a (partial) functional
  dependency of flows on $x$ and $f$ in the evolution statements
  below. In Isabelle one could therefore define flows as partial
  functions that take a list of pairs $(x_i,f_i)$ and time $t$ and map
  $\reals^V\to \reals^V$.  If there is no flow for $x$ and $f$, then
  the flow is undefined. In Isabelle, one could use the option monad
  for this. I guess that then, by definition, the orbit of an
  undefined ``flow problem'' (e.g. when $x$ and $f$ have no flow) is
  then empty, that is, equal to abort.  It thus trivially satisfies
  any Hoare triple.  I guess this is how we should model flows in
  Isabelle. The advantage would be that we don't have to check
  preconditions on existence and uniqueness in rules, they would be
  absorbed by the correctness specs. We would also not need the Solves
  predicate below.
*)

(* We proceed to refine the previous rule by finding the necessary restrictions on 
"varFunList" and "uInput" so that the solution to the store-IVP is guaranteed. *)
lemma conds4InitState:(* toSol respects the initial state for non-primed strings. *)
assumes initHyp:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 st = st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> (sol a[xfList\<leftarrow>uInput] 0) str = a str"
using assms apply(induction uInput xfList rule: cross_list.induct, simp_all)
by(simp add: varDiffs_def vdiff_def)

lemma conds4InitState2:(* toSol respects the initial state for affected primed strings. *)
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. 
\<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall>xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp3:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. \<forall>xf \<in> set xfList. 
(sol st[xfList\<leftarrow>uInput] 0)(vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] 0)"
using assms apply(induction uInput xfList rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac u uTail x f xfTail a y g)
fix x y ::"string" and f g::"real store \<Rightarrow> real"  
and u s::"real \<Rightarrow> real store \<Rightarrow> real" and a::"real store" and
xfTail::"(string \<times> (real store \<Rightarrow> real)) list" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real) list"
assume IH:"\<forall>st g. \<forall>xf\<in>set xfTail. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st \<Longrightarrow>
distinct (map \<pi>\<^sub>1 xfTail) \<Longrightarrow> length xfTail = length uTail \<Longrightarrow> \<forall>xf\<in>set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs \<Longrightarrow>
\<forall>st. \<forall>uxf\<in>set (uTail \<otimes> xfTail). \<pi>\<^sub>1 uxf 0 (d2z st) = d2z st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) \<Longrightarrow>
\<forall>st. \<forall>xf\<in>set xfTail. (sol st[xfTail\<leftarrow>uTail] 0) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol st[xfTail\<leftarrow>uTail] 0)"
let ?gLHS = "(sol a[((x, f) # xfTail)\<leftarrow>(u # uTail)] 0) (vdiff (\<pi>\<^sub>1 (y, g)))"
let ?gRHS = "\<pi>\<^sub>2 (y, g) (sol a[((x, f) # xfTail)\<leftarrow>(u # uTail)] 0)"
let ?goal = "?gLHS = ?gRHS"
assume eqFuncs:"\<forall>st g. \<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st"
and eqLengths:"length ((x, f) # xfTail) = length (u # uTail)"
and distinct:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and vars:"\<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp:"\<forall>st.\<forall>uxf\<in>set ((u # uTail) \<otimes> ((x, f) # xfTail)). \<pi>\<^sub>1 uxf 0 (d2z st) = d2z st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
from this obtain h1 where h1Def:"(sol a[((x, f) # xfTail)\<leftarrow>(u # uTail)] 0) = 
(override_on (d2z a) h1 varDiffs)" using state_list_cross_upd_its_dvars by blast 
from IH eqFuncs distinct eqLengths vars and solHyp have summary:"\<forall>xf\<in>set xfTail. 
  (sol a[xfTail\<leftarrow>uTail] 0) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol a[xfTail\<leftarrow>uTail] 0)" by simp
assume "(y, g) \<in> set ((x, f) # xfTail)"
then have "(y, g) = (x, f) \<or> (y, g) \<in> set xfTail" by simp
moreover
{assume eqHeads:"(y, g) = (x, f)"
  then have 1:"?gRHS =f (state_list_upd ((u,x,f) # (uTail \<otimes> xfTail)) 0 (d2z a))" by simp
  have 2:"f (state_list_upd ((u,x,f) # (uTail \<otimes> xfTail)) 0 (d2z a)) = 
  f (override_on (d2z a) h1 varDiffs)" using h1Def by simp
  have 3:"f (override_on (d2z a) h1 varDiffs) = f (d2z a)" using eqFuncs by simp
  have "f (d2z a) = ?gLHS" by (simp add: eqHeads)
  hence "?goal" using 1 2 and 3 by simp} 
moreover
{assume tailHyp:"(y, g) \<in> set xfTail"
  obtain h2 where h2Def:"(sol a[xfTail\<leftarrow>uTail] 0) = override_on (d2z a) h2 varDiffs" 
  using state_list_cross_upd_its_dvars eqLengths distinct vars and solHyp by force
  from eqFuncs and tailHyp have h2Hyp:"g (override_on (d2z a) h2 varDiffs) = g (d2z a)" by force
  from tailHyp have *:"g (sol a[xfTail\<leftarrow>uTail] 0) = (sol a[xfTail\<leftarrow>uTail] 0) (vdiff y)" 
  using summary by fastforce
  from tailHyp have "y \<noteq> x" using distinct non_empty_crossListElim by force
  hence dXnotdY:"vdiff x \<noteq> vdiff y" by(simp add: vdiff_def)
  have xNotdY:"x \<noteq> vdiff y" using vars vdiff_invarDiffs by auto 
  from * have "?gLHS = g (sol a[xfTail\<leftarrow>uTail] 0)" using xNotdY and dXnotdY by simp
  then have "?gLHS = g (d2z a)" using h2Hyp and h2Def by simp
  also have "?gRHS = g (d2z a)" using eqFuncs h1Def and tailHyp by fastforce 
  ultimately have "?goal" by simp}
ultimately show "?goal" by blast
qed
  
lemma state_list_cross_upd_correctInPrimes:
"distinct (map \<pi>\<^sub>1 xfList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 xfList). var \<notin> varDiffs) \<longrightarrow>
length xfList = length uInput \<longrightarrow> t > 0 \<longrightarrow> (\<forall> uxf \<in>set (uInput \<otimes> xfList). 
(a[xfList\<leftarrow>uInput] t) (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) = vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<..< (2 *\<^sub>R t)} t)"
apply(simp, induction uInput xfList rule: cross_list.induct, simp, simp, clarify)
proof(rename_tac u uTail x f xfTail s y g)
fix x y ::"string" and f g::"real store \<Rightarrow> real"  and u s::"real \<Rightarrow> real store \<Rightarrow> real" and
xfTail::"(string \<times> (real store \<Rightarrow> real)) list" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real) list"
assume IH:"distinct (map \<pi>\<^sub>1 xfTail) \<longrightarrow> (\<forall>var\<in>set xfTail. \<pi>\<^sub>1 var \<notin> varDiffs) \<longrightarrow>
length xfTail = length uTail \<longrightarrow> 0 < t \<longrightarrow> (\<forall>uxf\<in>set (uTail \<otimes> xfTail).
  (a[xfTail\<leftarrow>uTail] t) (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) = vderiv_of (\<lambda>r. \<pi>\<^sub>1 uxf r a) {0<..<2 \<cdot> t} t)"
assume lengthHyp:"length ((x, f) # xfTail) = length (u # uTail)" and tHyp:"0 < t"
and distHyp:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and varHyp:"\<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
from this and IH have keyFact:"\<forall>uxf\<in>set (uTail \<otimes> xfTail).
  (a[xfTail\<leftarrow>uTail] t) (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) = vderiv_of (\<lambda>r. \<pi>\<^sub>1 uxf r a) {0<..<2 \<cdot> t} t" by simp
assume sygHyp:"(s, y, g) \<in> set ((u # uTail) \<otimes> ((x, f) # xfTail))"
let ?gLHS = "(a[(x, f) # xfTail\<leftarrow>u # uTail] t) (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 (s, y, g))))"
let ?gRHS = "vderiv_of (\<lambda>r. \<pi>\<^sub>1 (s, y, g) r a) {0<..<2 \<cdot> t} t"
let ?goal = "?gLHS = ?gRHS"
let ?lhs = 
"((a[xfTail\<leftarrow>uTail] t)(x := u t a, vdiff x := vderiv_of (\<lambda> r. u r a) {0<..< (2 \<cdot> t)} t)) (vdiff y)"
let ?rhs = "vderiv_of (\<lambda>r. s r a) {0<..< (2 \<cdot> t)} t"
from sygHyp have "(s, y, g) = (u, x, f) \<or> (s, y, g) \<in> set (uTail \<otimes> xfTail)" by simp 
moreover
{have "?gLHS = ?lhs" using tHyp by simp
  also have "?gRHS =?rhs" by simp
  ultimately have "?goal = (?lhs = ?rhs)" by simp}
moreover
{assume uxfEq:"(s, y, g) = (u, x, f)"
  then have "?lhs = vderiv_of (\<lambda> r. u r a) {0<..< (2 \<cdot> t)} t" by simp
  also have "vderiv_of (\<lambda> r. u r a) {0<..< (2 \<cdot> t)} t = ?rhs" using uxfEq by simp
  ultimately have "?lhs = ?rhs" by simp}
moreover
{assume sygTail:"(s, y, g) \<in> set (uTail \<otimes> xfTail)"
  from this have "y \<noteq> x" using distHyp non_empty_crossListElim by force 
  hence dXnotdY:"vdiff x \<noteq> vdiff y" by(simp add: vdiff_def)
  have xNotdY:"x \<noteq> vdiff y" using varHyp using vdiff_invarDiffs by auto 
  then have "?lhs = (a[xfTail\<leftarrow>uTail] t) (vdiff y)" using xNotdY and dXnotdY by simp
  also have "(a[xfTail\<leftarrow>uTail] t) (vdiff y) = ?rhs" using keyFact sygTail by auto  
  ultimately have "?lhs = ?rhs" by simp}
ultimately show ?goal by blast
qed

lemma prelim_conds4vdiffs:
assumes funcsHyp:"\<forall>st g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and solHyp3:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and keyFact:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList).\<forall>t>0.
vderiv_of (\<lambda>r. (\<pi>\<^sub>1 uxf) r (d2z st)) {0<..< (2 *\<^sub>R t)} t = (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) (sol st[xfList\<leftarrow>uInput] t)"
shows "\<forall> st. \<forall> t\<ge>0. \<forall> xf\<in>set xfList. 
(sol st[xfList\<leftarrow>uInput] t) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t)"
proof(clarify)
fix t ::real and x::string and f::"real store \<Rightarrow> real" and a::"real store"
assume tHyp:"0 \<le> t" and pairHyp:"(x, f) \<in> set xfList"
from this obtain u where xfuHyp: "(u,x,f) \<in> set (uInput \<otimes> xfList)"
by (metis crossList_length legnth_crossListEx1 lengthHyp)
  show "(sol a[xfList\<leftarrow>uInput] t) (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (sol a[xfList\<leftarrow>uInput] t)"
  proof(cases "t=0")
  case True
    have "\<forall>st. \<forall>xf\<in>set xfList. 
    (sol st[xfList\<leftarrow>uInput] 0) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] 0)"
    using assms and conds4InitState2 by blast
    then show ?thesis using True and pairHyp by blast
  next
    case False
    from this have "t > 0" using tHyp by simp
    hence "(sol a[xfList\<leftarrow>uInput] t) (vdiff x) = vderiv_of (\<lambda>s. u s (d2z a)) {0<..< (2 *\<^sub>R t)} t" 
    using tHyp xfuHyp assms state_list_cross_upd_correctInPrimes by fastforce
    also have "vderiv_of (\<lambda>s. u s (d2z a)) {0<..< (2 *\<^sub>R t)} t = f (sol a[xfList\<leftarrow>uInput] t)" 
    using keyFact xfuHyp and \<open>t > 0\<close>  by force
    ultimately show ?thesis by simp
  qed
qed

lemma keyFact_elim:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}" 
shows keyFact:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList).\<forall>t>0.
vderiv_of (\<lambda>r. (\<pi>\<^sub>1 uxf) r (d2z st)) {0<..< (2 *\<^sub>R t)} t = (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) (sol st[xfList\<leftarrow>uInput] t)"
proof(clarify, rename_tac a u x f t)
fix a::"real store" and t::real and x::string
and f::"real store \<Rightarrow> real" and u::"real \<Rightarrow> real store \<Rightarrow> real"
assume uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)" and tHyp:"0 < t"
from this and assms have "\<forall> s > 0. (sol a[xfList\<leftarrow>uInput] s) x = u s (d2z a)" 
using state_list_cross_upd_uxf_on_x by (metis) 
hence 1:"\<And>s. s \<in> {0<..< 2 \<cdot> t} \<Longrightarrow> (sol a[xfList\<leftarrow>uInput] s) x = u s (d2z a)" using tHyp by force
have "{0<..<2 \<cdot> t} \<subseteq> {0..2 \<cdot> t}"  by auto
also have "\<forall>xf\<in>set xfList. ((\<lambda>r. (sol a[xfList\<leftarrow>uInput] r) (\<pi>\<^sub>1 xf)) 
  has_vderiv_on (\<lambda>r. \<pi>\<^sub>2 xf (sol a[xfList\<leftarrow>uInput] r))) {0..2 \<cdot> t}" using solHyp1 and tHyp  by simp
ultimately have "\<forall>xf\<in>set xfList. ((\<lambda>r. (sol a[xfList\<leftarrow>uInput] r) (\<pi>\<^sub>1 xf)) 
  has_vderiv_on (\<lambda>r. \<pi>\<^sub>2 xf (sol a[xfList\<leftarrow>uInput] r))) {0<..<2 \<cdot> t}"
using ODE_Auxiliarities.has_vderiv_on_subset by blast
also from uxfHyp have xfHyp:"(x,f) \<in> set xfList" by (meson non_empty_crossListElim) 
ultimately have 2:"((\<lambda>r. (sol a[xfList\<leftarrow>uInput] r) x) 
  has_vderiv_on (\<lambda>r. f (sol a[xfList\<leftarrow>uInput] r))) {0<..<2 \<cdot> t}"
using has_vderiv_on_subset by auto
have "((\<lambda>r. (sol a[xfList\<leftarrow>uInput] r) x) has_vderiv_on (\<lambda>r. f (sol a[xfList\<leftarrow>uInput] r))) {0<..<2\<cdot>t} = 
  ((\<lambda> r. u r (d2z a)) has_vderiv_on (\<lambda>r. f (sol a[xfList\<leftarrow>uInput] r))) {0<..<2 \<cdot> t}"
apply(rule_tac has_vderiv_on_cong) using 1 by auto
from this and 2 have derivHyp:"((\<lambda> r. u r (d2z a)) has_vderiv_on 
(\<lambda>r. f (sol a[xfList\<leftarrow>uInput] r))) {0<..<2 \<cdot> t}" by simp
then have "\<forall> s \<in> {0<..<2 \<cdot> t}. ((\<lambda> r. u r (d2z a)) has_vector_derivative 
f (sol a[xfList\<leftarrow>uInput] s)) (at s within {0<..<2 \<cdot> t})" by (simp add: has_vderiv_on_def)
{fix f' assume "((\<lambda>s. u s (d2z a)) has_vderiv_on f') {0<..<2 \<cdot> t}"
  then have f'Hyp:"\<forall> rr \<in> {0<..<2 \<cdot> t}. ((\<lambda>s. u s (d2z a)) has_derivative (\<lambda>s. s *\<^sub>R (f' rr))) 
  (at rr within {0<..<2 \<cdot> t})" by(simp add: has_vderiv_on_def has_vector_derivative_def) 
  {fix rr assume rrHyp:"rr \<in> {0 <..< 2 \<cdot> t}"
    have boxDef:"box 0 (2 \<cdot> t) = {0<..<2 \<cdot> t} \<and> rr \<in> box 0 (2 \<cdot> t)" 
    using tHyp rrHyp by auto
    have rr1:"((\<lambda>r. u r (d2z a)) has_derivative (\<lambda>s. s *\<^sub>R (f' rr))) (at rr within box 0 (2 \<cdot> t))"
    using tHyp boxDef rrHyp f'Hyp by force
    from derivHyp have "\<forall> rr \<in> {0<..<2 \<cdot> t}. ((\<lambda> s. u s (d2z a)) has_derivative 
    (\<lambda>s. s *\<^sub>R (f (sol a[xfList\<leftarrow>uInput] rr)))) (at rr within {0<..<2 \<cdot> t})" 
    by(simp add: has_vderiv_on_def has_vector_derivative_def)
    hence rr2:"((\<lambda> s. u s (d2z a)) has_derivative 
    (\<lambda>s. s *\<^sub>R (f (sol a[xfList\<leftarrow>uInput] rr)))) (at rr within box 0 (2 \<cdot> t))"using rrHyp boxDef by force
    from boxDef rr1 and rr2 have "(\<lambda>s. s *\<^sub>R (f' rr)) = (\<lambda>s. s *\<^sub>R (f (sol a[xfList\<leftarrow>uInput] rr)))"
    using frechet_derivative_unique_within_open_interval by blast 
    hence "f' rr = f (sol a[xfList\<leftarrow>uInput] rr)" by (metis lambda_one real_scaleR_def)}
  from this have "\<forall> rr \<in> {0<..< 2 \<cdot> t}. f' rr = (f (sol a[xfList\<leftarrow>uInput] rr))" by force}
then have f'Hyp:"\<forall> f'. ((\<lambda>s. u s (d2z a)) has_vderiv_on f') {0<..<2 \<cdot> t} \<longrightarrow> 
(\<forall> rr \<in> {0<..< 2 \<cdot> t}. f' rr = (f (sol a[xfList\<leftarrow>uInput] rr)))" by force
have "((\<lambda>s. u s (d2z a)) has_vderiv_on (vderiv_of (\<lambda>r. u r (d2z a)) {0<..< (2 *\<^sub>R t)})) {0<..<2 \<cdot> t}"
by(simp add: vderiv_of_def, metis derivHyp someI_ex)
from this and f'Hyp have "\<forall> rr \<in> {0<..< 2 \<cdot> t}. 
(vderiv_of (\<lambda>r. u r (d2z a)) {0<..< (2 *\<^sub>R t)}) rr = (f (sol a[xfList\<leftarrow>uInput] rr))" by blast
thus "vderiv_of (\<lambda>r. \<pi>\<^sub>1 (u, x, f) r (d2z a)) {0<..<2 *\<^sub>R t} t = 
\<pi>\<^sub>2 (\<pi>\<^sub>2 (u, x, f)) (sol a[xfList\<leftarrow>uInput] t)" using tHyp by force
qed

lemma conds4vdiffs:
assumes funcsHyp:"\<forall>st g. \<forall>xf\<in>set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st"
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. ((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}"
and solHyp3:"\<forall> st. \<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. \<forall> t\<ge>0. \<forall> xf\<in>set xfList. 
(sol st[xfList\<leftarrow>uInput] t) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t)"
apply(rule prelim_conds4vdiffs)
prefer 6 subgoal using assms and keyFact_elim by blast
using assms by simp_all

lemma conds4Consts:
assumes varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
shows "\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> (sol a[xfList\<leftarrow>uInput] t) (vdiff str) = 0"
using varsHyp apply(induction xfList uInput rule: cross_list.induct)
apply(simp_all add: override_on_def varDiffs_def vdiff_def)
by clarsimp

lemma conds4RestOfStrings: (* NONE, i.e. toSol keeps the initial state everywhere else. *)
"\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> (sol a[xfList\<leftarrow>uInput] t) str = a str"
apply(induction xfList uInput rule: cross_list.induct)
by(auto simp: varDiffs_def)

lemma conds4solvesIVP:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. (\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) \<in> {0..t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. \<forall>t\<ge>0.\<forall>xf\<in>set xfList. ((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) 
solvesTheIVP (\<lambda>t r. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t)) withInitCond  0 \<mapsto> st (\<pi>\<^sub>1 xf)) {0..t} UNIV"
apply(rule allI, rule allI, rule impI, rule ballI, rule solves_ivpI, rule solves_odeI)
subgoal using solHyp1 by simp
subgoal using solHyp2 by simp
proof(clarify, rename_tac a t x f)
fix t::real and x::string and f::"real store \<Rightarrow> real" and a::"real store"
assume tHyp:"0 \<le> t" and xfHyp:"(x, f) \<in> set xfList"
then obtain u where uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)"
by (metis crossList_map_projElim in_set_impl_in_set_zip2 lengthHyp map_fst_zip map_snd_zip)
from varsHyp have toZeroHyp:"(d2z a) x = a x" using override_on_def xfHyp by auto
from uxfHyp and solHyp3 have "u 0 (d2z a) = (d2z a) x" by fastforce
also have "(sol a[xfList\<leftarrow>uInput] 0) (\<pi>\<^sub>1 (x, f)) = u 0 (d2z a)" 
using state_list_cross_upd_uxf_on_x uxfHyp and assms by fastforce
ultimately show "(sol a[xfList\<leftarrow>uInput] 0) (\<pi>\<^sub>1 (x, f)) = a (\<pi>\<^sub>1 (x, f))" using toZeroHyp by simp
qed

lemma conds4storeIVP_on_toSol:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (sol st[xfList\<leftarrow>uInput] t)"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. (\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) \<in> {0..t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. solvesStoreIVP (\<lambda> t. (sol st[xfList\<leftarrow>uInput] t)) xfList st G"
apply(rule allI, rule solves_store_ivpI)
subgoal using guardHyp by simp
subgoal using conds4RestOfStrings by blast
subgoal using conds4Consts varsHyp by blast
subgoal using conds4vdiffs and assms by blast 
subgoal using conds4solvesIVP and assms by blast
done

theorem dSolve_toSolve:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (sol st[xfList\<leftarrow>uInput] t)"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. (\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) \<in> {0..t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and uniqHyp:"\<forall> st.\<forall> X. solvesStoreIVP X xfList st G \<longrightarrow> (\<forall> t \<ge> 0. (sol st[xfList\<leftarrow>uInput] t) = X t)"
and postCondHyp:"\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. Q (sol st[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
subgoal using assms and conds4storeIVP_on_toSol by simp
subgoal by (simp add: uniqHyp)
using postCondHyp guardHyp postCondHyp by simp

(* As before, we keep refining the rule dSolve. This time we find the necessary restrictions on 
to attain uniqueness. *)

(* OBSERVATIONS *)
term "unique_on_bounded_closed t0 T x0 f X L"
thm unique_on_bounded_closed_def
thm unique_on_bounded_closed_axioms_def
thm unique_on_closed_def

lemma conds4UniqSol:
assumes sHyp:"t \<ge> 0"(* does not depend on sol a[xfList\<leftarrow>uInput] t... *)
assumes contHyp:"\<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t))"
shows "\<forall> xf \<in> set xfList. unique_on_bounded_closed 0 {0..t} (a (\<pi>\<^sub>1 xf)) 
(\<lambda>t r. (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t)) UNIV (if t = 0 then 1 else 1/(t+1))"
apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def 
unique_on_closed_def compact_interval_def compact_interval_axioms_def nonempty_set_def 
interval_def self_mapping_def self_mapping_axioms_def closed_domain_def global_lipschitz_def 
lipschitz_def, rule conjI)
subgoal using contHyp continuous_rhs_def by fastforce 
subgoal 
  using contHyp continuous_rhs_def sHyp by fastforce 
done

lemma solves_store_ivp_at_beginning_overrides:
assumes Fsolves:"solvesStoreIVP F xfList a G"
shows "F 0 = override_on a (F 0) varDiffs"
apply(rule ext, subgoal_tac "x \<notin> varDiffs \<longrightarrow> F 0 x = a x")
subgoal by (simp add: override_on_def)
using assms and solves_store_ivpD(6) by simp

lemma ubcStoreUniqueSol:
assumes sHyp:"s \<ge> 0"
assumes contHyp:"\<forall> xf \<in> set xfList. continuous_on ({0..s} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t))"
and eqDerivs:"\<forall> xf \<in> set xfList. \<forall> t \<in> {0..s}. (\<pi>\<^sub>2 xf) (F t) = (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t)"
and Fsolves:"solvesStoreIVP F xfList a G"
and solHyp:"solvesStoreIVP (\<lambda> t. (sol a[xfList\<leftarrow>uInput] t)) xfList a G"
shows "(sol a[xfList\<leftarrow>uInput] s) = F s"
proof
  fix str::"string" show "(sol a[xfList\<leftarrow>uInput] s) str = F s str"
  proof(cases "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs")
  case False
    then have notInVars:"str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs" by simp
    from solHyp have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> 
    (sol a[xfList\<leftarrow>uInput] t) str = a str" by (simp add: solvesStoreIVP_def) 
    hence 1:"(sol a[xfList\<leftarrow>uInput] s) str = a str" using sHyp notInVars by blast
    from Fsolves have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> F t str = a str" 
    by (simp add: solvesStoreIVP_def) 
    then have 2:"F s str = a str" using sHyp notInVars by blast
    thus "(sol a[xfList\<leftarrow>uInput] s) str = F s str" using 1 and 2 by simp
  next case True
    then have "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<or> str \<in> varDiffs" by simp
    moreover
    {assume "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)" from this obtain f::"((char list \<Rightarrow> real) \<Rightarrow> real)" where 
      strfHyp:"(str, f) \<in> set xfList" by fastforce
      (* Expand hypothesis for arbitrary solution. *)
      from Fsolves and sHyp have "(\<forall> xf \<in> set xfList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP 
      (\<lambda>t r. \<pi>\<^sub>2 xf (F t)) withInitCond  0 \<mapsto> a (\<pi>\<^sub>1 xf)) {0..s} UNIV)" 
      by (simp add: solvesStoreIVP_def)
      then have expand1:"\<forall> xf \<in> set xfList.((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (F t))){0..s} UNIV \<and> F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" by (simp add: solves_ivp_def)
      hence expand2:"\<forall> xf \<in> set xfList. \<forall> t \<in> {0..s}. ((\<lambda>r. F r (\<pi>\<^sub>1 xf)) 
      has_vector_derivative (\<lambda>r. (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t)) t) (at t within {0..s})" 
      using eqDerivs by (simp add: solves_ode_def has_vderiv_on_def)
      (* Re-express hypothesis for arbitrary solution in terms of user solution.*)
      then have "\<forall> xf \<in> set xfList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t))){0..s} UNIV \<and> F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" 
      by (simp add: has_vderiv_on_def solves_ode_def expand1 expand2) 
      then have 1:"((\<lambda>t. F t str) solvesTheIVP (\<lambda>t r. f (sol a[xfList\<leftarrow>uInput] t)) 
      withInitCond  0 \<mapsto> a str) {0..s} UNIV" using strfHyp solves_ivp_def by fastforce
      (* Expand hypothesis for user's solution. *)
      from solHyp and strfHyp have 2:"((\<lambda> t. (sol a[xfList\<leftarrow>uInput] t) str) 
      solvesTheIVP (\<lambda>t r. f (sol a[xfList\<leftarrow>uInput] t)) withInitCond  0 \<mapsto> a str) {0..s} UNIV" 
      using solvesStoreIVP_def sHyp by fastforce
      (* Show user's solution and arbitrary solution are the same. *)
      from sHyp and contHyp have "\<forall> xf \<in> set xfList. unique_on_bounded_closed 0 {0..s} (a (\<pi>\<^sub>1 xf)) 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t)) UNIV (if s = 0 then 1 else 1/(s+1))" 
      using conds4UniqSol by simp
      from this have 3:"unique_on_bounded_closed 0 {0..s} (a str) (\<lambda>t r. f (sol a[xfList\<leftarrow>uInput] t)) 
      UNIV (if s = 0 then 1 else 1/(s+1))" using strfHyp by fastforce
      from 1 2 and 3 have "(sol a[xfList\<leftarrow>uInput] s) str = F s str"
      using unique_on_bounded_closed.ivp_unique_solution using real_Icc_closed_segment sHyp by blast}
    moreover
    {assume "str \<in> varDiffs"
      then obtain x where xDef:"str = vdiff x" by (auto simp: varDiffs_def)
      have "(sol a[xfList\<leftarrow>uInput] s) str = F s str "
      proof(cases "x \<in> set (map \<pi>\<^sub>1 xfList)")
      case True
        then obtain f where strFhyp:"(x, f) \<in> set xfList" by fastforce
          from sHyp and Fsolves have "F s str = f (F s)"
          using solves_store_ivpD(4) strFhyp xDef by force
          moreover from solHyp and sHyp have "(sol a[xfList\<leftarrow>uInput] s) str = 
          f (sol a[xfList\<leftarrow>uInput] s)" using solves_store_ivpD(4) strFhyp xDef by force
          ultimately show ?thesis using eqDerivs strFhyp sHyp by auto
      next
      case False
        from this Fsolves and sHyp have "F s str = 0" using xDef solves_store_ivpD(3) by simp
        also have "(sol a[xfList\<leftarrow>uInput] s) str = 0" 
        using False solHyp sHyp solves_store_ivpD(3) xDef by fastforce 
        ultimately show ?thesis by simp
      qed}
    ultimately show "(sol a[xfList\<leftarrow>uInput] s) str = F s str" by blast
  qed
qed

theorem dSolveUBC:
assumes contHyp:"\<forall> st. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol st[xfList\<leftarrow>uInput] t))"
and solHyp:"\<forall> st. solvesStoreIVP (\<lambda> t. (sol st[xfList\<leftarrow>uInput] t)) xfList st G"
and uniqHyp:"\<forall> st. \<forall> X. X solvesTheStoreIVP xfList withInitState st andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0..t}. (\<pi>\<^sub>2 xf) (X r) = 
(\<pi>\<^sub>2 xf) (sol st[xfList\<leftarrow>uInput] r))"
and diffAssgn: "\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. G (sol st[xfList\<leftarrow>uInput] t) \<longrightarrow> Q (sol st[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
subgoal using solHyp by simp
subgoal proof(clarify)
fix a::"real store" and X::"real \<Rightarrow> real store" and s::"real"
assume XisSol:"solvesStoreIVP X xfList a G" and sHyp:"0 \<le> s"
from this and uniqHyp have "\<forall> xf \<in> set xfList. \<forall> t \<in> {0..s}. 
(\<pi>\<^sub>2 xf) (X t) = (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t)" by auto
moreover have "\<forall> xf \<in> set xfList. continuous_on ({0..s} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol a[xfList\<leftarrow>uInput] t))" using contHyp sHyp by blast
ultimately show "(sol a[xfList\<leftarrow>uInput] s) = X s" 
using sHyp XisSol ubcStoreUniqueSol solHyp by simp
qed
subgoal using diffAssgn by simp
done

theorem dSolve_toSolveUBC:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (sol st[xfList\<leftarrow>uInput] t)"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (sol st[xfList\<leftarrow>uInput] t))) {0..t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. (\<lambda>t. (sol st[xfList\<leftarrow>uInput] t) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (d2z st) = (d2z st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and contHyp:"\<forall> st. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0..t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (sol st[xfList\<leftarrow>uInput] t))"
and uniqHyp:"\<forall> st. \<forall> X. solvesStoreIVP X xfList st G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0..t}. (\<pi>\<^sub>2 xf) (X r) = (\<pi>\<^sub>2 xf) (sol st[xfList\<leftarrow>uInput] r))"
and postCondHyp:"\<forall>st. P st \<longrightarrow> (\<forall>t\<ge>0. Q (sol st[xfList\<leftarrow>uInput] t))"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolveUBC)
subgoal using contHyp by simp
subgoal
  apply(rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
  using assms by auto
subgoal using uniqHyp by simp
using postCondHyp by simp

(* OBSERVATIONS *)
thm derivative_intros(173)
thm derivative_intros
thm derivative_intros(176)
thm derivative_eq_intros(8)
thm derivative_eq_intros(17)
thm derivative_eq_intros(6)
thm derivative_eq_intros(15)
thm derivative_eq_intros
thm continuous_intros

(* Can it still be refined??? *)
lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (ODEsystem [(''pos'',(\<lambda> s. s ''vel''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
apply(rule_tac uInput="[\<lambda> t s. s ''vel'' \<cdot> t + s ''pos'']" in dSolve_toSolveUBC) (* 12 subgoals *)
prefer 11 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
apply(simp_all add: vdiff_def varDiffs_def)
subgoal
  apply(clarify)
  apply(rule_tac f'1="\<lambda> x. st ''vel''" and g'1="\<lambda> x. 0" in derivative_intros(173))(* 3 goals appear. *)
  apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))           (* 3 goals appear. *)
  by(auto intro: derivative_intros)
subgoal by(clarify, rule continuous_intros)
subgoal by(simp add: solvesStoreIVP_def vdiff_def varDiffs_def)
done

-- "Differential Invariant."

datatype trms = Const real | Var string | Mns trms | Sum trms trms | Mult trms trms

primrec rval ::"trms \<Rightarrow> (real store \<Rightarrow> real)" where
"rval (Const r) = (\<lambda> s. r)"|
"rval (Var x) = (\<lambda> s. s x)"|
"rval (Mns \<theta>) = (\<lambda> s. - (rval \<theta> s))"|
"rval (Sum \<theta> \<eta>) = (\<lambda> s. rval \<theta> s + rval \<eta> s)"|
"rval (Mult \<theta> \<eta>) = (\<lambda> s. rval \<theta> s \<cdot> rval \<eta> s)"

datatype props = Eq trms trms | Less trms trms | Leq trms trms | And props props | Or props props

primrec pval ::"props \<Rightarrow> (real store \<Rightarrow> bool)" where
"pval (Eq \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s = (rval \<eta>) s)"|
"pval (Less \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s < (rval \<eta>) s)"|
"pval (Leq \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s \<le> (rval \<eta>) s)"|
"pval (And \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<and> (pval \<psi>) s)"|
"pval (Or \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<or> (pval \<psi>) s)"

primrec rdiff ::"trms \<Rightarrow> trms" where
"rdiff (Const r) = Const 0"|
"rdiff (Var x) = Var (vdiff x)"|
"rdiff (Mns \<theta>) = Mns (rdiff \<theta>)"|
"rdiff (Sum \<theta> \<eta>) = Sum (rdiff \<theta>) (rdiff \<eta>)"|
"rdiff (Mult \<theta> \<eta>) = Sum (Mult (rdiff \<theta>) \<eta>) (Mult \<theta> (rdiff \<eta>))"

primrec pdiff ::"props \<Rightarrow> props" where
"pdiff (Eq \<theta> \<eta>) = Eq (rdiff \<theta>) (rdiff \<eta>)"|
"pdiff (Less \<theta> \<eta>) = Leq (rdiff \<theta>) (rdiff \<eta>)"|
"pdiff (Leq \<theta> \<eta>) = Leq (rdiff \<theta>) (rdiff \<eta>)"|
"pdiff (And \<phi> \<psi>) = And (pdiff \<phi>) (pdiff \<psi>)"|
"pdiff (Or \<phi> \<psi>) = And (pdiff \<phi>) (pdiff \<psi>)"

lemma solvesStoreIVP_couldBeModified:
fixes F::"real \<Rightarrow> real store"
assumes storeIVP_vars:"\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) 
solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) withInitCond 0 \<mapsto> (a (\<pi>\<^sub>1 xf))) {0..t} UNIV"
and storeIVP_dvars:"\<forall> t \<ge> 0. \<forall>xf\<in>set xfList. (F t (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F t)"
shows "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. 
((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (vdiff (\<pi>\<^sub>1 xf))) (at r within {0..t})"
proof(clarify, rename_tac t r x f)
fix x f and t r::real
assume tHyp:"0 \<le> t" and xfHyp:"(x, f) \<in> set xfList" and rHyp:"r \<in> {0..t}"
from this and storeIVP_vars have "((\<lambda> t. F t x) solvesTheIVP (\<lambda> t. \<lambda> r. f (F t)) 
withInitCond 0 \<mapsto> (a x)) {0..t} UNIV" using tHyp by fastforce
then have "((\<lambda> t. F t x) has_vderiv_on (\<lambda> t. f (F t))) {0..t}" 
by (simp add: solves_ode_def solves_ivp_def)
thm has_vderiv_on_def
hence *:"\<forall>r\<in>{0..t}. ((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) r) (at r within {0..t})" 
by (simp add: has_vderiv_on_def tHyp)
have "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
using assms by auto
from this rHyp and xfHyp have "(F r (vdiff x)) = f (F r)" by force
then show "((\<lambda>t. F t (\<pi>\<^sub>1 (x, f))) has_vector_derivative 
F r (vdiff (\<pi>\<^sub>1 (x, f)))) (at r within {0..t})" using * rHyp by auto
qed

lemma derivationLemma_baseCase:
fixes F::"real \<Rightarrow> real store"
assumes solves:"solvesStoreIVP F xfList a G"
shows "\<forall> x \<in> (UNIV - varDiffs). \<forall> t \<ge> 0. \<forall>r\<in>{0..t}.
((\<lambda> t. F t x) has_vector_derivative F r (vdiff x)) (at r within {0..t})"
proof
fix x
assume "x \<in> UNIV - varDiffs"
then have notVarDiff:"\<forall> z. x \<noteq> vdiff z" using varDiffs_def by fastforce
  show "\<forall>t\<ge>0. \<forall>r\<in>{0..t}. ((\<lambda>t. F t x) has_vector_derivative F r (vdiff x)) (at r within {0..t})"
  proof(cases "x \<in> set (map \<pi>\<^sub>1 xfList)")
    case True
    from this and solves have "\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. 
    ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (vdiff (\<pi>\<^sub>1 xf))) (at r within {0..t})"
    apply(rule_tac a="a" in solvesStoreIVP_couldBeModified) using solves solves_store_ivpD by auto
    from this show ?thesis using True by auto
  next
    case False
    from this notVarDiff and solves have const:"\<forall> t \<ge> 0. F t x = a x" 
    using solves_store_ivpD(2) by (simp add: varDiffs_def)
    have constD:"\<forall> t \<ge> 0. \<forall>r\<in>{0..t}. ((\<lambda> r. a x) has_vector_derivative 0) (at r within {0..t})"
    by (auto intro: derivative_eq_intros)
    {fix t r::real 
      assume "t\<ge>0" and "r \<in> {0..t}" 
      hence "((\<lambda> s. a x) has_vector_derivative 0) (at r within {0..t})" by (simp add: constD)
      moreover have "\<And>s. s \<in> {0..t} \<Longrightarrow> (\<lambda> r. F r x) s = (\<lambda> r. a x) s" 
      using const by (simp add: \<open>0 \<le> t\<close>)
      ultimately have "((\<lambda> s. F s x) has_vector_derivative 0) (at r within {0..t})"
      using has_vector_derivative_imp by (metis \<open>r \<in> {0..t}\<close>)}
    hence isZero:"\<forall>t\<ge>0. \<forall>r\<in>{0..t}.((\<lambda> t. F t x) has_vector_derivative 0) (at r within {0..t})" by blast
    from False solves and notVarDiff have "\<forall> t \<ge> 0. F t (vdiff x) = 0"
    using solves_store_ivpD(3) by simp
    then show ?thesis using isZero by simp
  qed
qed

primrec trmVars :: "trms \<Rightarrow> string set" where
"trmVars (Const r) = {}"|
"trmVars (Var x) = {x}"|
"trmVars (Mns \<theta>) = trmVars \<theta>"|
"trmVars (Sum \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"trmVars (Mult \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"

lemma derivationLemma:
assumes "solvesStoreIVP F xfList a G"
and tHyp:"t \<ge> 0"
and termVarsHyp:"\<forall> x \<in> trmVars \<eta>. x \<in> (UNIV - varDiffs)"
shows "\<forall>r\<in>{0..t}. ((\<lambda> s. (rval \<eta>) (F s)) 
has_vector_derivative (rval (rdiff \<eta>)) (F r)) (at r within {0..t})"
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
  apply(subgoal_tac "((\<lambda>s. rval \<eta>1 (F s) *\<^sub>R rval \<eta>2 (F s)) has_vector_derivative 
  rval (rdiff \<eta>1) (F r) \<cdot> rval \<eta>2 (F r) + rval \<eta>1 (F r) \<cdot> rval (rdiff \<eta>2) (F r)) 
  (at r within {0..t})", simp)
  apply(rule_tac f'1="rval (rdiff \<eta>1) (F r)" and 
    g'1="rval (rdiff \<eta>2) (F r)" in derivative_eq_intros(25))
  by (simp_all add: has_field_derivative_iff_has_vector_derivative)
qed

fun substList ::"(string \<times> trms) list \<Rightarrow> trms \<Rightarrow> trms" where
"substList xTrmList (Const r) = Const r"|
"substList [] (Var x) = Var x"|
"substList ((y,\<xi>) # xTrmTail) (Var x) = (if x = y then \<xi> else substList xTrmTail (Var x))"|
"substList xTrmList (Mns \<theta>) = Mns (substList xTrmList \<theta>)"|
"substList xTrmList (Sum \<theta> \<eta>) = (Sum (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"substList xTrmList (Mult \<theta> \<eta>) = (Mult (substList xTrmList \<theta>) (substList xTrmList \<eta>))"

lemma substList_on_compl_of_varDiffs:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
assumes "set (map \<pi>\<^sub>1 xTrmList) \<subseteq> varDiffs"
shows "substList xTrmList \<eta> = \<eta>"
using assms apply(induction \<eta>, simp_all add: varDiffs_def)
by(induction xTrmList, auto)

lemma substList_help1:"set (map \<pi>\<^sub>1 ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)) \<subseteq> varDiffs"
apply(induction xfList uInput rule: cross_list.induct, simp_all add: varDiffs_def)
by auto

lemma substList_help2:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) \<eta> = \<eta>"
using assms substList_help1 substList_on_compl_of_varDiffs by blast

lemma substList_cross_vdiff_on_non_ocurring_var:
assumes "x \<notin> set list1"
shows "substList ((map vdiff list1) \<otimes> list2) (Var (vdiff x))
  = Var (vdiff x)"
using assms apply(induction list1 list2 rule: cross_list.induct, simp, simp, clarsimp)
by(simp add: vdiff_inj)

lemma diff_subst_prprty_4terms:
assumes solves:"\<forall> xf \<in> set xfList. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
and tHyp:"(t::real) \<ge> 0"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "rval (rdiff \<eta>) (F t) = 
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F t)"
using termVarsHyp apply(induction \<eta>) apply(simp_all add: substList_help2)
using listsHyp and solves apply(induction xfList uInput rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac y g xfTail \<theta> trmTail x)
fix x y::string and \<theta>::trms and g and xfTail::"((string \<times> (real store \<Rightarrow> real)) list)" and trmTail
assume IH:"\<And>x. x \<notin> varDiffs \<Longrightarrow> map \<pi>\<^sub>2 xfTail = map rval trmTail \<Longrightarrow>
\<forall>xf\<in>set xfTail. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t) \<Longrightarrow>
F t (vdiff x) = rval (substList (map (vdiff \<circ> \<pi>\<^sub>1) xfTail \<otimes> trmTail) (Var (vdiff x))) (F t)"
and 1:"x \<notin> varDiffs" and 2:"map \<pi>\<^sub>2 ((y, g) # xfTail) = map rval (\<theta> # trmTail)" 
and 3:"\<forall>xf\<in>set ((y, g) # xfTail). F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
hence *:"rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfTail) \<otimes> trmTail) (Var (vdiff x))) (F t) = 
F t (vdiff x)" using tHyp by auto
show "F t (vdiff x) =
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) (Var (vdiff x))) (F t)"
  proof(cases "x \<in> set ( map \<pi>\<^sub>1 ((y, g) # xfTail))")
    case True
    then have "x = y \<or> (x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail))" by auto
    moreover
    {assume "x = y"
      from this have "substList ((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) 
      (Var (vdiff x)) = \<theta>" by simp
      also from 3 tHyp have "F t (vdiff y) = g (F t)" by simp
      moreover from 2 have "rval \<theta> (F t) = g (F t)" by simp
      ultimately have ?thesis by (simp add: \<open>x = y\<close>)}
    moreover
    {assume "x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail)"
      then have "vdiff x \<noteq> vdiff y" using vdiff_inj by auto
      from this have "substList ((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) 
      (Var (vdiff x)) = substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfTail) \<otimes> trmTail) (Var (vdiff x))"
      by simp
      hence ?thesis using * by simp}
    ultimately show ?thesis by blast
  next
    case False
    then have "substList ((map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) \<otimes> (\<theta> # trmTail)) (Var (vdiff x))
    = Var (vdiff x)" using substList_cross_vdiff_on_non_ocurring_var
    by (metis (no_types, lifting) List.map.compositionality)
    thus ?thesis by simp
  qed
qed

lemma eqInVars_impl_eqInTrms:
assumes termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and initHyp:"\<forall>x. x \<notin> varDiffs \<longrightarrow> b x = a x"
shows "(rval \<eta>) a = (rval \<eta>) b"
using assms by(induction \<eta>, simp_all)

lemma non_empty_funList_implies_non_empty_trmList:
shows "\<forall> list. (x,f) \<in> set list \<and> map \<pi>\<^sub>2 list = map rval tList \<longrightarrow> 
(\<exists> \<theta>. rval \<theta> = f \<and> \<theta> \<in> set tList)"
by(induction tList, auto)

lemma dInvForTrms_prelim:
assumes substHyp:
"\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
shows "(rval \<eta>) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c = 0)"
proof(clarify)
fix c assume aHyp:"(rval \<eta>) a = 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "rval \<eta> a = rval \<eta> (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"rval \<eta> (F 0) = 0" using aHyp tcHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 
rval (rdiff \<eta>) (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "\<forall>r\<in>{0..t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)" 
using tcHyp solves_store_ivpD(4) by fastforce
from this and tcHyp have "\<forall>r\<in>{0..t}. rval (rdiff \<eta>) (F r) =
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r)"
using diff_subst_prprty_4terms termVarsHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. 
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r) = 0" 
using solves_store_ivpD(1) solves_store_ivpD(3) tcHyp by fastforce
ultimately have "\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 0) (at r within {0..t})" 
using obs2 by auto
from this and tcHyp have "\<forall>s\<in>{0..t}. ((\<lambda>x. rval \<eta> (F x)) has_derivative (\<lambda>x. x *\<^sub>R 0)) 
(at s within {0..t})" by (metis has_vector_derivative_def)
hence "rval \<eta> (F t) - rval \<eta> (F 0) = (\<lambda>x. x *\<^sub>R 0) (t - 0)" 
using mvt_very_simple and tcHyp by fastforce 
then show "rval \<eta> c = 0" using obs1 tcHyp by auto 
qed

theorem dInvForTrms:
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and eta_f:"f = rval \<eta>"
shows " PRE (\<lambda> s. f s = 0) (ODEsystem xfList with G) POST (\<lambda> s. f s = 0)"
using eta_f proof(clarsimp)
fix a b
assume "(a, b) \<in> \<lceil>\<lambda>s. rval \<eta> s = 0\<rceil>" and "f = rval \<eta>"
from this have aHyp:"a = b \<and> rval \<eta> a = 0" by (metis (full_types) d_p2r rdom_p2r_contents)
have "(rval \<eta>) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c = 0)"
using assms dInvForTrms_prelim by metis 
from this and aHyp have "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c = 0" by blast
thus "(a, b) \<in> wp (ODEsystem xfList with G ) \<lceil>\<lambda>s. rval \<eta> s = 0\<rceil>"
using aHyp by (simp add: boxProgrPred_chrctrztn) 
qed

lemma circular_motion:
      "PRE (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''y'')),(''y'',(\<lambda> s. - s ''x''))] with G)
      POST (\<lambda> s. (s ''x'') \<cdot> (s ''x'') + (s ''y'') \<cdot> (s ''y'') - (s ''r'') \<cdot> (s ''r'') = 0)"
apply(rule_tac \<eta>="Sum (Sum (Mult (Var ''x'') (Var ''x'')) (Mult (Var ''y'') (Var ''y'')))
(Mns (Mult (Var ''r'') (Var ''r'')))" and uInput="[Var ''y'', Mns (Var ''x'')]"in dInvForTrms)
apply(simp_all add: vdiff_def varDiffs_def) 
apply(clarsimp, erule_tac x="''r''" in allE)
by simp

primrec propVars :: "props \<Rightarrow> string set" where
"propVars (Eq \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (Less \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (Leq \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (And \<phi> \<psi>) = propVars \<phi> \<union> propVars \<psi>"|
"propVars (Or \<phi> \<psi>) = propVars \<phi> \<union> propVars \<psi>"

primrec subspList :: "(string \<times> trms) list \<Rightarrow> props \<Rightarrow> props" where
"subspList xTrmList (Eq \<theta> \<eta>) = (Eq (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"subspList xTrmList (Less \<theta> \<eta>) = (Less (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"subspList xTrmList (Leq \<theta> \<eta>) = (Leq (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"subspList xTrmList (And \<phi> \<psi>) = (And (subspList xTrmList \<phi>) (subspList xTrmList \<psi>))"|
"subspList xTrmList (Or \<phi> \<psi>) = (Or (subspList xTrmList \<phi>) (subspList xTrmList \<psi>))"

lemma diff_subst_prprty_4props:
assumes solves:"\<forall> xf \<in> set xfList. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t)"
and tHyp:"t \<ge> 0"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
shows "pval (pdiff \<phi>) (F t) = 
pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff \<phi>)) (F t)"
using propVarsHyp apply(induction \<phi>, simp_all)
using assms diff_subst_prprty_4terms apply fastforce
using assms diff_subst_prprty_4terms apply fastforce
using assms diff_subst_prprty_4terms by fastforce

lemma dInvForProps_prelim:
assumes substHyp:
"\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) st \<ge> 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
shows "(rval \<eta>) a > 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c > 0)"
and "(rval \<eta>) a \<ge> 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c \<ge> 0)"
proof(clarify)
fix c assume aHyp:"(rval \<eta>) a > 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "rval \<eta> a = rval \<eta> (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"rval \<eta> (F 0) > 0" using aHyp tcHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 
rval (rdiff \<eta>) (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "(\<forall>t\<ge>0. \<forall> xf \<in> set xfList. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t))"
using tcHyp solves_store_ivpD(4) by blast
from this and tcHyp have "\<forall>r\<in>{0..t}. rval (rdiff \<eta>) (F r) =
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r)"
using diff_subst_prprty_4terms termVarsHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. 
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r) \<ge> 0" 
using solves_store_ivpD(1) solves_store_ivpD(3) tcHyp by (metis atLeastAtMost_iff)
ultimately have *:"\<forall>r\<in>{0..t}. rval (rdiff \<eta>) (F r) \<ge> 0" by (simp)
from obs2 and tcHyp have "\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_derivative 
(\<lambda>x. x *\<^sub>R (rval (rdiff \<eta>) (F r)))) (at r within {0..t})" by (simp add: has_vector_derivative_def) 
hence "\<exists>r\<in>{0..t}. rval \<eta> (F t) - rval \<eta> (F 0) = t \<cdot> (rval (rdiff \<eta>) (F r))" 
using mvt_very_simple and tcHyp by fastforce
then obtain r where "rval (rdiff \<eta>) (F r) \<ge> 0 \<and> 0 \<le> r \<and> r \<le> t \<and> rval (rdiff \<eta>) (F t) \<ge> 0
\<and> rval \<eta> (F t) - rval \<eta> (F 0) = t \<cdot> (rval (rdiff \<eta>) (F r))"
using * tcHyp by fastforce
thus "rval \<eta> c > 0" 
using obs1 tcHyp by (metis cancel_comm_monoid_add_class.diff_cancel diff_ge_0_iff_ge 
diff_strict_mono linorder_neqE_linordered_idom linordered_field_class.sign_simps(45) not_le) 
next
show "0 \<le> rval \<eta> a \<longrightarrow> (\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> 0 \<le> rval \<eta> c)"
proof(clarify)
fix c assume aHyp:"(rval \<eta>) a \<ge> 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(6) by blast
from this have "rval \<eta> a = rval \<eta> (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"rval \<eta> (F 0) \<ge> 0" using aHyp tcHyp by simp
from tcHyp have obs2:"\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 
rval (rdiff \<eta>) (F r)) (at r within {0..t})" using derivationLemma termVarsHyp by blast
have "(\<forall>t\<ge>0. \<forall> xf \<in> set xfList. F t (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F t))"
using tcHyp solves_store_ivpD(4) by blast
from this and tcHyp have "\<forall>r\<in>{0..t}. rval (rdiff \<eta>) (F r) =
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r)"
using diff_subst_prprty_4terms termVarsHyp listsHyp by fastforce
also from substHyp have "\<forall>r\<in>{0..t}. 
rval (substList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff \<eta>)) (F r) \<ge> 0" 
using solves_store_ivpD(1) solves_store_ivpD(3) tcHyp by (metis atLeastAtMost_iff)
ultimately have *:"\<forall>r\<in>{0..t}. rval (rdiff \<eta>) (F r) \<ge> 0" by (simp)
from obs2 and tcHyp have "\<forall>r\<in>{0..t}. ((\<lambda>s. rval \<eta> (F s)) has_derivative 
(\<lambda>x. x *\<^sub>R (rval (rdiff \<eta>) (F r)))) (at r within {0..t})" by (simp add: has_vector_derivative_def) 
hence "\<exists>r\<in>{0..t}. rval \<eta> (F t) - rval \<eta> (F 0) = t \<cdot> (rval (rdiff \<eta>) (F r))" 
using mvt_very_simple and tcHyp by fastforce
then obtain r where "rval (rdiff \<eta>) (F r) \<ge> 0 \<and> 0 \<le> r \<and> r \<le> t \<and> rval (rdiff \<eta>) (F t) \<ge> 0
\<and> rval \<eta> (F t) - rval \<eta> (F 0) = t \<cdot> (rval (rdiff \<eta>) (F r))"
using * tcHyp by fastforce
thus "rval \<eta> c \<ge> 0" 
using obs1 tcHyp by (metis cancel_comm_monoid_add_class.diff_cancel diff_ge_0_iff_ge 
diff_strict_mono linorder_neqE_linordered_idom linordered_field_class.sign_simps(45) not_le)  
qed
qed

lemma less_pval_to_rval:
assumes "pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff (Less \<theta> \<eta>))) st"
shows "rval (substList ((map (vdiff\<circ>\<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff (Sum \<eta> (Mns \<theta>)))) st \<ge> 0"
using assms by(auto)

lemma leq_pval_to_rval:
assumes "pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff (Leq \<theta> \<eta>))) st"
shows "rval (substList ((map (vdiff\<circ>\<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff (Sum \<eta> (Mns \<theta>)))) st \<ge> 0"
using assms by(auto)

lemma dInv_prelim:
assumes substHyp:"\<forall> st. G st \<longrightarrow>  (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff \<phi>)) st"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
shows "(pval \<phi>) a \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (pval \<phi>) c)"
proof(clarify)
fix c assume aHyp:"pval \<phi> a" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto 
from aHyp propVarsHyp and substHyp show "pval \<phi> c"
proof(induction \<phi>)
case (Eq \<theta> \<eta>)
hence hyp:"\<forall>st. G st \<longrightarrow>  (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow> 
pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff (Eq \<theta> \<eta>))) st" by blast
then have "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow> 
rval (substList ((map (vdiff\<circ>\<pi>\<^sub>1) xfList) \<otimes> uInput) (rdiff (Sum \<theta> (Mns \<eta>)))) st = 0" by simp
also have "trmVars (Sum \<theta> (Mns \<eta>)) \<subseteq> UNIV - varDiffs" using Eq.prems(2) by simp
moreover have "rval (Sum \<theta> (Mns \<eta>)) a = 0" using Eq.prems(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> rval (Sum \<theta> (Mns \<eta>)) c = 0)"
using dInvForTrms_prelim listsHyp by blast
hence "rval (Sum \<theta> (Mns \<eta>)) (F t) = 0" using tcHyp cHyp by simp
from this have "(rval \<theta> (F t) = rval \<eta> (F t))" by simp
also have "pval (Eq \<theta> \<eta>) c = (rval \<theta> (F t) = rval \<eta> (F t))" using tcHyp by simp
ultimately show ?case by simp
next
case (Less \<theta> \<eta>)
hence "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow> 
0 \<le> rval (substList (map (vdiff \<circ> \<pi>\<^sub>1) xfList \<otimes> uInput) (rdiff (Sum \<eta> (Mns \<theta>)))) st" 
using less_pval_to_rval by metis
also from "Less.prems"(2)have "trmVars (Sum \<eta> (Mns \<theta>)) \<subseteq> UNIV - varDiffs" by simp
moreover have "rval (Sum \<eta> (Mns \<theta>)) a > 0" using "Less.prems"(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> rval (Sum \<eta> (Mns \<theta>)) c > 0)"
using dInvForProps_prelim(1) listsHyp by blast
hence "rval (Sum \<eta> (Mns \<theta>)) (F t) > 0" using tcHyp cHyp by simp
from this have "(rval \<eta> (F t) > rval \<theta> (F t))" by simp
also have "pval (Less \<theta> \<eta>) c = (rval \<theta> (F t) < rval \<eta> (F t))" using tcHyp by simp
ultimately show ?case by simp
next
case (Leq \<theta> \<eta>)
hence "\<forall>st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow> 
0 \<le> rval (substList (map (vdiff \<circ> \<pi>\<^sub>1) xfList \<otimes> uInput) (rdiff (Sum \<eta> (Mns \<theta>)))) st" 
using leq_pval_to_rval by metis
also from "Leq.prems"(2)have "trmVars (Sum \<eta> (Mns \<theta>)) \<subseteq> UNIV - varDiffs" by simp
moreover have "rval (Sum \<eta> (Mns \<theta>)) a \<ge> 0" using "Leq.prems"(1) by simp
ultimately have "(\<forall>c. (a, c) \<in> ODEsystem xfList with G  \<longrightarrow> rval (Sum \<eta> (Mns \<theta>)) c \<ge> 0)"
using dInvForProps_prelim(2) listsHyp by blast
hence "rval (Sum \<eta> (Mns \<theta>)) (F t) \<ge> 0" using tcHyp cHyp by simp
from this have "(rval \<eta> (F t) \<ge> rval \<theta> (F t))" by simp
also have "pval (Leq \<theta> \<eta>) c = (rval \<theta> (F t) \<le> rval \<eta> (F t))" using tcHyp by simp
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
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff \<phi>)) st"
and termVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and phi_p:"P = pval \<phi>"
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
assumes "\<forall> st. G st \<longrightarrow> (\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<longrightarrow> st (vdiff str) = 0) \<longrightarrow>
pval (subspList ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput) (pdiff \<phi>)) st"
and termVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and impls:"\<lceil>P\<rceil> \<subseteq> \<lceil>F\<rceil> \<and> \<lceil>F\<rceil> \<subseteq> \<lceil>Q\<rceil>"
and phi_f:"F = pval \<phi>"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac C="pval \<phi>" in dCut)
apply(subgoal_tac "\<lceil>F\<rceil> \<subseteq> wp (ODEsystem xfList with G ) \<lceil>F\<rceil>", simp)
using impls and phi_f apply blast
apply(subgoal_tac "PRE F (ODEsystem xfList with G) POST F", simp)
apply(rule_tac \<phi>="\<phi>" and uInput="uInput" in dInv)
  subgoal using assms(1) by simp
  subgoal using termVarsHyp by simp
  subgoal using listsHyp by simp
  subgoal using phi_f by simp
apply(subgoal_tac "PRE P (ODEsystem xfList with (\<lambda>s. G s \<and> F s)) POST Q", simp add: phi_f)
apply(rule dWeakening)
using impls by simp

declare d_p2r [simp del]
lemma motion_with_constant_velocity_and_invariants:
      "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      (ODEsystem [(''x'', \<lambda> s. s ''v'')] with (\<lambda> s. True))
      POST (\<lambda> s. s ''x''> 0)"
apply(rule_tac C = "\<lambda> s.  s ''v'' > 0" in dCut)
apply(rule_tac \<phi>="Less (Const 0) (Var ''v'')" and uInput="[Var ''v'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''v''" in allE, simp)
apply(rule_tac C = "\<lambda> s.  s ''x'' > 0" in dCut)
apply(rule_tac \<phi>="(Less (Const 0) (Var ''x'')) " and uInput="[Var ''v'']" 
  and F="\<lambda> s.  s ''x'' > 0" in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def)
using dWeakening by simp

lemma motion_with_constant_acceleration_and_invariants:
      "PRE (\<lambda> s. s ''y'' < s ''x''  \<and> s ''v'' \<ge> 0 \<and> s ''a'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v'')),(''v'',(\<lambda> s. s ''a''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''y'' < s ''x''))"
apply(rule_tac C = "\<lambda> s.  s ''a'' > 0" in dCut) 
apply(rule_tac \<phi> = "Less (Const 0) (Var ''a'')" and uInput="[Var ''v'', Var ''a'']"in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def, clarify, erule_tac x="''a''" in allE, simp)
apply(rule_tac C = "\<lambda> s.  s ''v'' \<ge> 0" in dCut)
apply(rule_tac \<phi> = "Leq (Const 0) (Var ''v'')" and uInput="[Var ''v'', Var ''a'']" in dInvFinal)
apply(simp_all add: vdiff_def varDiffs_def)
apply(rule_tac C = "\<lambda> s.  s ''x'' >  s ''y''" in dCut)
apply(rule_tac \<phi> = "Less (Var ''y'') (Var ''x'')" and uInput="[Var ''v'', Var ''a'']"in dInvFinal)
apply(simp_all add: varDiffs_def vdiff_def, clarify, erule_tac x="''y''" in allE, simp)
using dWeakening by simp
declare d_p2r [simp]

end