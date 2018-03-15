theory VC_diffKAD
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

(*lemma [simp]:"vdiff x = ''d[''@x@'']''"
by (simp add: vdiff_def)*)

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
(* At the beginning F is (almost) the initial state. *)
(\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str) \<and>
(\<forall> xf \<in> set xfList. (F 0 (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F 0)) \<and>
(* F preserves the guard statement and F sends varDiffs to derivs. *)
(\<forall> t \<ge> 0. G (F t) \<and>  
  (\<forall> r \<in> {0<--<t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)) \<and> 
(* F preserves the rest of the variables and F sends derivs of constants to 0. *)
  (\<forall> str. (str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str) \<and> 
          (str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)) \<longrightarrow> F t str = 0)) \<and> 
(* F solves the induced IVP. *)
  (\<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
  withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0--t} UNIV))"
  
lemma solves_store_ivpI:
assumes "\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str"
  and "\<forall> t \<ge> 0. G (F t)"
  and "\<forall> xf \<in> set xfList. (F 0 (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F 0)"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
  and "\<forall> t \<ge> 0.\<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)). F t str = 0" 
  and "\<forall> t \<ge> 0.\<forall> r \<in> {0<--<t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0--t} UNIV"
shows "F solvesTheStoreIVP xfList withInitState st andGuard G"
using assms solvesStoreIVP_def by auto

lemma solves_store_ivpD:
assumes "F solvesTheStoreIVP xfList withInitState st andGuard G"
shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> F 0 str = st str"
  and "\<forall> t \<ge> 0. G (F t)"
  and "\<forall> xf \<in> set xfList. (F 0 (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F 0)"
  and "\<forall> t \<ge> 0.\<forall> str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)\<union>varDiffs \<longrightarrow> F t str = st str"
  and "\<forall> t \<ge> 0.\<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)). F t str = 0"
  and "\<forall> t \<ge> 0.\<forall> r \<in> {0<--<t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
  and "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0--t} UNIV"
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

definition "vderiv_of f S = (SOME f'. (f has_vderiv_on f') S)"
abbreviation "toInit a \<equiv> (override_on a (\<lambda> str. 0) varDiffs)"

lemma toInit_begins[simp]: "take 2 x \<noteq> ''d['' \<Longrightarrow> toInit a x = a x"
apply(simp add: varDiffs_def override_on_def vdiff_def)
by(fastforce)

lemma override_on_upd:"x \<in> X \<Longrightarrow> (override_on f g X)(x := z) = (override_on f (g(x := z)) X)"
by(rule ext, simp add: override_on_def)

primrec toSol :: "((real \<Rightarrow> real store \<Rightarrow> real) \<times> string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> real \<Rightarrow> 
real store \<Rightarrow> real store" where
"toSol [] t a  = a"|
"toSol (uxf # tail) t a = (toSol tail t a)
(     (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (\<pi>\<^sub>1 uxf) t a, 
vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (if t = 0 
then (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) a
else vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<--< (2 *\<^sub>R t)} t))"

lemma toSol_crossList_emptyElim[simp]: "toSol (cross_list list []) t a  = a"
by(induction list, simp_all)

lemma toSol_crossList_onListArguments:
 "distinct (map \<pi>\<^sub>1 xfList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 xfList). var \<notin> varDiffs) \<longrightarrow>
length (xfList) = length (uInput) \<longrightarrow> (\<forall> uxf \<in>set (cross_list uInput xfList). 
(toSol (cross_list uInput xfList) t a) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = (\<pi>\<^sub>1 uxf) t a)"
apply(simp, induction xfList uInput rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac x f xfTail u uTail s y g)
fix x y::"string" and f g::"real store \<Rightarrow> real" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real)list"
and xfTail::"(string \<times> (real store \<Rightarrow> real))list" and u s::"real \<Rightarrow> real store \<Rightarrow> real"
let ?gLHS = "toSol (cross_list (u # uTail) ((x, f) # xfTail)) t a (\<pi>\<^sub>1 (\<pi>\<^sub>2 (s, y, g)))"
let ?goal = "?gLHS = \<pi>\<^sub>1 (s, y, g) t a"
assume IH:"distinct (map \<pi>\<^sub>1 xfTail) \<longrightarrow> (\<forall> xf \<in> set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs) \<longrightarrow>
length xfTail = length uTail \<longrightarrow> (\<forall>uxf\<in>set (cross_list uTail xfTail). 
toSol (cross_list uTail xfTail) t a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = \<pi>\<^sub>1 uxf t a)"
and distHyp:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and varsHyp:"\<forall>xf \<in> set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length ((x, f) # xfTail) = length (u # uTail)"
then have keyHyp:"\<forall>uxf\<in>set (cross_list uTail xfTail). 
toSol (cross_list uTail xfTail) t a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) = \<pi>\<^sub>1 uxf t a" by fastforce
assume "(s, y, g) \<in> set (cross_list (u # uTail) ((x, f) # xfTail))" 
from this have "(s, y, g) = (u, x, f) \<or> (s, y, g) \<in> set (cross_list uTail xfTail)" by simp
moreover
{assume eq:"(s, y, g) = (u, x, f)" 
  then have "?gLHS = ((toSol (cross_list uTail xfTail) t a)
  (y := s t a, vdiff y := if t = 0 then g a 
  else vderiv_of (\<lambda> r. s r a) {0<--< (2 *\<^sub>R t)} t)) y" by simp
  also have "((toSol (cross_list uTail xfTail) t a)
  (y := s t a, vdiff y := if t = 0 then g a 
  else vderiv_of (\<lambda> r. s r a) {0<--< (2 *\<^sub>R t)} t)) y = s t a" 
  using eq by (simp add: vdiff_def)
  ultimately have ?goal by simp}
moreover
{assume yTailHyp:"(s, y, g) \<in> set (cross_list uTail xfTail)"
  from this and keyHyp have 3:"toSol (cross_list uTail xfTail) t a y = 
  s t a" by fastforce
  from yTailHyp and distHyp have 2:"y \<noteq> x" using non_empty_crossListElim by force 
  from yTailHyp and varsHyp have 1:"y \<noteq> vdiff x" 
  using non_empty_crossListElim vdiff_invarDiffs by fastforce 
  from 1 and 2 have "?gLHS = toSol (cross_list uTail xfTail) t a y"  by (simp)
  then have "?goal" using 3 by simp}
ultimately show ?goal by blast
qed

lemma toSol_crossList_on_varDiffs:
assumes lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp3:"\<forall>uxf\<in>set (cross_list uInput xfList). (\<pi>\<^sub>1 uxf) 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists> g. (toSol (cross_list uInput xfList) 0 a) = (override_on a g varDiffs)"
using assms proof(induction xfList uInput rule: cross_list.induct)
case (1 list)
have "toSol (cross_list list []) 0 a = a" by simp
also have "override_on a a varDiffs = a" unfolding override_on_def by simp
ultimately show ?case by metis 
next
case (2 xf xfTail)
have "toSol (cross_list [] (xf # xfTail)) 0 a = a" by simp
also have "override_on a a varDiffs = a" unfolding override_on_def by simp
ultimately show ?case by metis 
next
case (3 xf xfTail u uTail)
let ?gLHS="toSol (cross_list (u # uTail) (xf # xfTail)) 0 a"
have observ:"vdiff (\<pi>\<^sub>1 xf) \<in> varDiffs" by (auto simp: varDiffs_def)
assume IH:"length xfTail = length uTail \<Longrightarrow> \<forall>xf\<in>set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs \<Longrightarrow>
\<forall>uxf\<in>set (cross_list uTail xfTail). \<pi>\<^sub>1 uxf 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) \<Longrightarrow>
\<exists>g. toSol (cross_list uTail xfTail) 0 a = override_on a g varDiffs"
assume "length (xf # xfTail) = length (u # uTail)"
and solHyp:"\<forall>uxf\<in>set (cross_list (u # uTail) (xf # xfTail)). \<pi>\<^sub>1 uxf 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and no_varDiffs:"\<forall>xf\<in>set (xf # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
from this and IH obtain g where "toSol (cross_list uTail xfTail) 0 a = 
override_on a g varDiffs" by force
then have 1:"?gLHS = (override_on a g varDiffs)(\<pi>\<^sub>1 xf := u 0 a, vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" by simp
also have 2:"(override_on a g varDiffs)(\<pi>\<^sub>1 xf := u 0 a, vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a) = 
(override_on a g varDiffs)(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" 
using override_on_def varDiffs_def "3.prems"(2) solHyp by auto 
also have 3:"(override_on a g varDiffs)(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a) = 
(override_on a (g(vdiff (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)) varDiffs)" using observ and override_on_upd by force
ultimately show ?case by auto
qed

lemma toSol_crossList_uxf_onX:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and uxfHyp:"(u, x, f) \<in>set (cross_list uInput xfList)"
shows "(toSol (cross_list uInput xfList) t a) x = u t a"
using assms and toSol_crossList_onListArguments by force

abbreviation mass_gets :: "((real \<Rightarrow> real store \<Rightarrow> real) \<times> string \<times> (real store \<Rightarrow> real)) list
 \<Rightarrow> real \<Rightarrow> real store rel" where
"mass_gets uxfList t \<equiv> {(s,toSol uxfList t (toInit s)) |s. True}"

lemma prelim_dSolve:
assumes solHyp:"(\<lambda>t. toSol (cross_list uInput xfList) t (toInit a)) solvesTheStoreIVP 
xfList withInitState a andGuard G"
and uniqHyp:"\<forall> X. X solvesTheStoreIVP xfList withInitState a andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. (toSol (cross_list uInput xfList) t (toInit a)) = X t)"
and diffAssgn: "\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit a))) \<longrightarrow> 
(\<forall> c. (a,c) \<in> (mass_gets (cross_list uInput xfList) t) \<longrightarrow> Q c)"
shows "\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> Q c"
proof(clarify)
fix c assume "(a,c) \<in> (ODEsystem xfList with G)"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where FHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" using guarDiffEqtn_def by auto 
from this and uniqHyp have "toSol (cross_list uInput xfList) t (toInit a) = F t" by blast
then have cHyp:"c = (toSol (cross_list uInput xfList) t (toInit a))" using FHyp by simp
hence "(a,c) \<in> (mass_gets (cross_list uInput xfList) t)" by (simp) 
moreover from solHyp have "\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit a))"
by (simp add: open_segment_eq_real_ivl solvesStoreIVP_def FHyp)
ultimately show "Q c" using diffAssgn FHyp by blast
qed

theorem dSolve:
assumes solHyp: "\<forall>st. (\<lambda>t. toSol (cross_list uInput xfList) t (toInit st)) 
solvesTheStoreIVP xfList withInitState st andGuard G"
and uniqHyp:"\<forall> st. \<forall> X. X solvesTheStoreIVP xfList withInitState st andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. (toSol (cross_list uInput xfList) t (toInit st)) = X t)"
and diffAssgn: "\<forall>st. P st \<longrightarrow> 
(\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit st))) \<longrightarrow> 
\<lfloor>wp (mass_gets (cross_list uInput xfList) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(clarsimp, subgoal_tac "a=b")
apply(clarify, subst boxProgrPred_chrctrztn)
apply(simp_all add: p2r_def)
apply(rule_tac uInput="uInput" in prelim_dSolve)
apply(simp add: solHyp, simp add: uniqHyp)
by (metis (no_types, lifting) diffAssgn wp_trafo)

(* We proceed to refine the previous rule by finding the necessary restrictions on 
"varFunList" and "uInput" so that the solution to the store-IVP is guaranteed. *)

lemma conds4InitState:(* toSol respects the initial state for non-primed strings. *)
assumes initHyp:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList). (\<pi>\<^sub>1 uxf) 0 st = st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> str. str \<notin> varDiffs \<longrightarrow> toSol (cross_list uInput xfList) 0 (toInit a) str = a str"
using assms apply(induction uInput xfList rule: cross_list.induct, simp_all)
by(simp add: varDiffs_def vdiff_def)

lemma conds4InitState2:(* toSol respects the initial state for affected primed strings. *)
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp3:"\<forall> st.  \<forall>uxf\<in>set (cross_list uInput xfList). 
  (\<pi>\<^sub>1 uxf) 0 (toInit st) = (toInit st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. \<forall>xf \<in> set xfList. toSol (cross_list uInput xfList) 0 (toInit st) (vdiff (\<pi>\<^sub>1 xf)) = 
\<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) 0 (toInit st))"
using assms apply(induction uInput xfList rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac u uTail x f xfTail a y g)
fix x y ::"string" and f g::"real store \<Rightarrow> real"  
and u s::"real \<Rightarrow> real store \<Rightarrow> real" and a::"real store" and
xfTail::"(string \<times> (real store \<Rightarrow> real)) list" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real) list"
assume IH:"(\<forall>st g. \<forall>xf\<in>set xfTail. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st \<Longrightarrow>
distinct (map \<pi>\<^sub>1 xfTail) \<Longrightarrow> length xfTail = length uTail \<Longrightarrow> \<forall>xf\<in>set xfTail. \<pi>\<^sub>1 xf \<notin> varDiffs \<Longrightarrow>
\<forall>st. \<forall>uxf\<in>set (cross_list uTail xfTail). \<pi>\<^sub>1 uxf 0 (toInit st) = toInit st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) \<Longrightarrow>
\<forall>st. \<forall>xf\<in>set xfTail. toSol (cross_list uTail xfTail) 0 (toInit st) (vdiff (\<pi>\<^sub>1 xf)) = 
  \<pi>\<^sub>2 xf (toSol (cross_list uTail xfTail) 0 (toInit st)))"
let ?gLHS = "toSol (cross_list (u # uTail) ((x, f) # xfTail)) 0 (toInit a) (vdiff (\<pi>\<^sub>1 (y, g)))"
let ?gRHS = "\<pi>\<^sub>2 (y, g) (toSol (cross_list (u # uTail) ((x, f) # xfTail)) 0 (toInit a))"
let ?goal = "?gLHS = ?gRHS"
assume eqFuncs:"\<forall>st g. \<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st"
and eqLengths:"length ((x, f) # xfTail) = length (u # uTail)"
and distinct:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and vars:"\<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp:"\<forall>st. \<forall>uxf\<in>set (cross_list (u # uTail) ((x, f) # xfTail)). \<pi>\<^sub>1 uxf 0 (toInit st) = 
toInit st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
from this obtain h1 where h1Def:"toSol (cross_list (u # uTail) ((x, f) # xfTail)) 0 (toInit a) = 
(override_on (toInit a) h1 varDiffs)" using toSol_crossList_on_varDiffs by blast 
from IH eqFuncs distinct eqLengths vars and solHyp have summary:"\<forall>xf\<in>set xfTail. 
  toSol (cross_list uTail xfTail) 0 (toInit a) (vdiff (\<pi>\<^sub>1 xf)) = 
  \<pi>\<^sub>2 xf (toSol (cross_list uTail xfTail) 0 (toInit a))" by simp
assume "(y, g) \<in> set ((x, f) # xfTail)"
then have "(y, g) = (x, f) \<or> (y, g) \<in> set xfTail" by simp
moreover
{assume eqHeads:"(y, g) = (x, f)"
  then have 1:"?gRHS =f (toSol ((u,x,f) # cross_list uTail xfTail) 0 (toInit a))" by simp
  have 2:"f (toSol ((u,x,f) # cross_list uTail xfTail) 0 (toInit a)) = 
  f (override_on (toInit a) h1 varDiffs)" using h1Def by simp
  have 3:"f (override_on (toInit a) h1 varDiffs) = f (toInit a)" using eqFuncs by simp
  have "f (toInit a) = ?gLHS" by (simp add: eqHeads)
  hence "?goal" using 1 2 and 3 by simp} 
moreover
{assume tailHyp:"(y, g) \<in> set xfTail"
  obtain h2 where h2Def:"toSol (cross_list uTail xfTail) 0 (toInit a) = 
  override_on (toInit a) h2 varDiffs" using toSol_crossList_on_varDiffs 
  eqLengths distinct vars and solHyp by force
  from eqFuncs and tailHyp have h2Hyp:"g (override_on (toInit a) h2 varDiffs) = 
  g (toInit a)" by force
  from tailHyp have *:"g (toSol (cross_list uTail xfTail) 0 (toInit a)) =
  toSol (cross_list uTail xfTail) 0 (toInit a) (vdiff y)" using summary by fastforce
  from tailHyp have "y \<noteq> x" using distinct non_empty_crossListElim by force
  hence dXnotdY:"vdiff x \<noteq> vdiff y" by(simp add: vdiff_def)
  have xNotdY:"x \<noteq> vdiff y" using vars vdiff_invarDiffs by auto 
  from * have "?gLHS = g (toSol (cross_list uTail xfTail) 0 (toInit a))" 
  using xNotdY and dXnotdY by simp
  then have "?gLHS = g (toInit a)" using h2Hyp and h2Def by simp
  also have "?gRHS = g (toInit a)" using eqFuncs h1Def and tailHyp by fastforce 
  ultimately have "?goal" by simp}
ultimately show "?goal" by blast
qed

lemma toSol_correctInPrimes:
"distinct (map \<pi>\<^sub>1 xfList) \<longrightarrow> (\<forall> var \<in> set (map \<pi>\<^sub>1 xfList). var \<notin> varDiffs) \<longrightarrow>
length xfList = length uInput \<longrightarrow> t > 0 \<longrightarrow>
(\<forall> uxf \<in>set (cross_list uInput xfList). 
  (toSol (cross_list uInput xfList) t a) (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) = 
  vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<--< (2 *\<^sub>R t)} t)"
apply(simp, induction uInput xfList rule: cross_list.induct, simp, simp, clarify)
proof(rename_tac u uTail x f xfTail s y g)
fix x y ::"string" and f g::"real store \<Rightarrow> real"  and u s::"real \<Rightarrow> real store \<Rightarrow> real" and
xfTail::"(string \<times> (real store \<Rightarrow> real)) list" and uTail::"(real \<Rightarrow> real store \<Rightarrow> real) list"
assume IH:"distinct (map \<pi>\<^sub>1 xfTail) \<longrightarrow> (\<forall>var\<in>set xfTail. \<pi>\<^sub>1 var \<notin> varDiffs) \<longrightarrow>
length xfTail = length uTail \<longrightarrow> 0 < t \<longrightarrow> (\<forall>uxf\<in>set (cross_list uTail xfTail).
  toSol (cross_list uTail xfTail) t a (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) =
  vderiv_of (\<lambda>r. \<pi>\<^sub>1 uxf r a) {0<--<2 \<cdot> t} t)"
assume lengthHyp:"length ((x, f) # xfTail) = length (u # uTail)" and tHyp:"0 < t"
and distHyp:"distinct (map \<pi>\<^sub>1 ((x, f) # xfTail))"
and varHyp:"\<forall>xf\<in>set ((x, f) # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
from this and IH have keyFact:"\<forall>uxf\<in>set (cross_list uTail xfTail).
  toSol (cross_list uTail xfTail) t a (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))) =
  vderiv_of (\<lambda>r. \<pi>\<^sub>1 uxf r a) {0<--<2 \<cdot> t} t" by simp
assume sygHyp:"(s, y, g) \<in> set (cross_list (u # uTail) ((x, f) # xfTail))"
let ?gLHS = "toSol (cross_list (u # uTail) ((x, f) # xfTail)) t a (vdiff (\<pi>\<^sub>1 (\<pi>\<^sub>2 (s, y, g))))"
let ?gRHS = "vderiv_of (\<lambda>r. \<pi>\<^sub>1 (s, y, g) r a) {0<--<2 \<cdot> t} t"
let ?goal = "?gLHS = ?gRHS"
let ?lhs = "((toSol (cross_list uTail xfTail) t a)(x := u t a, 
vdiff x := vderiv_of (\<lambda> r. u r a) {0<--< (2 \<cdot> t)} t)) (vdiff y)"
let ?rhs = "vderiv_of (\<lambda>r. s r a) {0<--< (2 \<cdot> t)} t"
from sygHyp have "(s, y, g) = (u, x, f) \<or> (s, y, g) \<in> set (cross_list uTail xfTail)" by simp 
moreover
{have "?gLHS = ?lhs" using tHyp by simp
  also have "?gRHS =?rhs" by simp
  ultimately have "?goal = (?lhs = ?rhs)" by simp}
moreover
{assume uxfEq:"(s, y, g) = (u, x, f)"
  then have "?lhs = vderiv_of (\<lambda> r. u r a) {0<--< (2 \<cdot> t)} t" by simp
  also have "vderiv_of (\<lambda> r. u r a) {0<--< (2 \<cdot> t)} t = ?rhs" 
  using uxfEq by simp
  ultimately have "?lhs = ?rhs" by simp}
moreover
{assume sygTail:"(s, y, g) \<in> set (cross_list uTail xfTail)"
  from this have "y \<noteq> x" using distHyp non_empty_crossListElim by force 
  hence dXnotdY:"vdiff x \<noteq> vdiff y" by(simp add: vdiff_def)
  have xNotdY:"x \<noteq> vdiff y" using varHyp using vdiff_invarDiffs by auto 
  then have "?lhs = toSol (cross_list uTail xfTail) t a (vdiff y)" 
  using xNotdY and dXnotdY by simp
  also have "toSol (cross_list uTail xfTail) t a (vdiff y) = ?rhs" 
  using keyFact sygTail by auto  
  ultimately have "?lhs = ?rhs" by simp}
ultimately show ?goal by blast
qed

lemma prelim_conds4vdiffs:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and keyFact:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList).\<forall>t>0. \<forall>r\<in>{0<--<t}.
  vderiv_of (\<lambda>r. (\<pi>\<^sub>1 uxf) r (toInit st)) {0<--< (2 *\<^sub>R r)} r =
  (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) (toSol (cross_list uInput xfList) r (toInit st))"
shows "\<forall> st. \<forall> t\<ge>0. \<forall>r\<in>{0<--<t}. \<forall> xf\<in>set xfList. 
(toSol (cross_list uInput xfList) r (toInit st)) (vdiff (\<pi>\<^sub>1 xf)) = 
\<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) r (toInit st))"
proof(clarify)
fix t r::real and x::string and f::"real store \<Rightarrow> real" and a::"real store"
assume tHyp:"0 \<le> t" and pairHyp:"(x, f) \<in> set xfList" and rHyp:"r \<in> {0<--<t}"
from this obtain u where xfuHyp: "(u,x,f) \<in> set (cross_list uInput xfList)"
by (metis crossList_length legnth_crossListEx1 lengthHyp)
  show "toSol (cross_list uInput xfList) r (toInit a) (vdiff (\<pi>\<^sub>1 (x, f))) = 
  \<pi>\<^sub>2 (x, f) (toSol (cross_list uInput xfList) r (toInit a))"
  proof(cases "t=0")
    case True
    then have "{0<--<t} = {}" by(simp add: open_segment_eq_real_ivl)
    from this and rHyp show ?thesis by simp
  next
    case False
    then have "t > 0" using tHyp by linarith
    hence rNotZero:"r > 0" using rHyp open_segment_eq_real_ivl by simp
    from this have "toSol (cross_list uInput xfList) r (toInit a) (vdiff x) =
    vderiv_of (\<lambda>s. u s (toInit a)) {0<--< (2 *\<^sub>R r)} r" 
    using tHyp xfuHyp assms toSol_correctInPrimes by fastforce
    also have "vderiv_of (\<lambda>s. u s (toInit a)) {0<--< (2 *\<^sub>R r)} r =
    f (toSol (cross_list uInput xfList) r (toInit a))" 
    using keyFact xfuHyp \<open>t > 0\<close> and rHyp by force
    ultimately show ?thesis by simp
  qed
qed

lemma keyFact_elim:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
shows keyFact:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList).\<forall>t>0. \<forall>r\<in>{0<--<t}.
  vderiv_of (\<lambda>r. (\<pi>\<^sub>1 uxf) r (toInit st)) {0<--< (2 *\<^sub>R r)} r =
  (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) (toSol (cross_list uInput xfList) r (toInit st))"
proof(clarify, rename_tac a u x f t r)
fix a::"real store" and t r::real and x::string
and f::"real store \<Rightarrow> real" and u::"real \<Rightarrow> real store \<Rightarrow> real"
assume uxfHyp:"(u, x, f) \<in> set (cross_list uInput xfList)" and tHyp:"0 < t" and rHyp1:"r \<in> {0<--<t}"
then have rHyp2:"0 < r \<and> r < t" by (simp add: open_segment_eq_real_ivl)
from uxfHyp and assms have "\<forall> s > 0. (toSol (cross_list uInput xfList) s (toInit a)) x = 
u s (toInit a)" using toSol_crossList_uxf_onX by (metis) 
hence 1:"\<And>s. s \<in> {0<--< 2 \<cdot> r} \<Longrightarrow> (\<lambda> s. (toSol (cross_list uInput xfList) s (toInit a)) x) s = 
(\<lambda> s. u s (toInit a)) s" using open_segment_eq_real_ivl rHyp2 by force
{have "{0<--<2 \<cdot> r} \<subseteq> {0--2 \<cdot> r}" using open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  also have "\<forall>xf\<in>set xfList. ((\<lambda>r. (toSol (cross_list uInput xfList) r (toInit a)) (\<pi>\<^sub>1 xf)) 
  has_vderiv_on (\<lambda>r. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) r (toInit a)))) {0--2 \<cdot> r}"
  using solHyp1 and rHyp2  by simp
  ultimately have "\<forall>xf\<in>set xfList. ((\<lambda>r. (toSol (cross_list uInput xfList) r (toInit a)) (\<pi>\<^sub>1 xf)) 
  has_vderiv_on (\<lambda>r. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) r (toInit a)))) {0<--<2 \<cdot> r}"
  using ODE_Auxiliarities.has_vderiv_on_subset by blast
  also from uxfHyp have xfHyp:"(x,f) \<in> set xfList" by (meson non_empty_crossListElim) 
  ultimately have "((\<lambda>r. (toSol (cross_list uInput xfList) r (toInit a)) x) 
  has_vderiv_on (\<lambda>r. f (toSol (cross_list uInput xfList) r (toInit a)))) {0<--<2 \<cdot> r}"
  using has_vderiv_on_subset open_closed_segment_subset by auto}
from this and 1 have derivHyp:"((\<lambda> r. u r (toInit a)) has_vderiv_on 
(\<lambda>r. f (toSol (cross_list uInput xfList) r (toInit a)))) {0<--<2 \<cdot> r}" 
using has_vderiv_on_cong by auto
then have "\<forall> s \<in> {0<--<2 \<cdot> r}. ((\<lambda> r. u r (toInit a)) has_vector_derivative 
f (toSol (cross_list uInput xfList) s (toInit a))) (at s within {0<--<2 \<cdot> r})"
by (simp add: has_vderiv_on_def)
{fix f' assume "((\<lambda>s. u s (toInit a)) has_vderiv_on f') {0<--<2 \<cdot> r}"
  then have f'Hyp:"\<forall> rr \<in> {0<--<2 \<cdot> r}. ((\<lambda>s. u s (toInit a)) has_derivative (\<lambda>s. s *\<^sub>R (f' rr))) 
  (at rr within {0<--<2 \<cdot> r})" by(simp add: has_vderiv_on_def has_vector_derivative_def) 
  {fix rr assume rrHyp:"rr \<in> {0 <--< 2 \<cdot> r}"
    have boxDef:"box 0 (2 \<cdot> r) = {0<--<2 \<cdot> r} \<and> rr \<in> box 0 (2 \<cdot> r)" 
    using rHyp2 rrHyp open_segment_eq_real_ivl by auto
    have rr1:"((\<lambda>r. u r (toInit a)) has_derivative (\<lambda>s. s *\<^sub>R (f' rr))) (at rr within box 0 (2 \<cdot> r))"
    using tHyp boxDef rrHyp f'Hyp by force
    from derivHyp have "\<forall> rr \<in> {0<--<2 \<cdot> r}. ((\<lambda> s. u s (toInit a)) has_derivative 
    (\<lambda>s. s *\<^sub>R (f (toSol (cross_list uInput xfList) rr (toInit a))))) (at rr within {0<--<2 \<cdot> r})" 
    by(simp add: has_vderiv_on_def has_vector_derivative_def)
    hence rr2:"((\<lambda> s. u s (toInit a)) has_derivative 
    (\<lambda>s. s *\<^sub>R (f (toSol (cross_list uInput xfList) rr (toInit a))))) (at rr within box 0 (2 \<cdot> r))"
    using rrHyp boxDef by force
    from boxDef rr1 and rr2 have "(\<lambda>s. s *\<^sub>R (f' rr)) = 
    (\<lambda>s. s *\<^sub>R (f (toSol (cross_list uInput xfList) rr (toInit a))))"
    using frechet_derivative_unique_within_open_interval by blast 
    hence "f' rr = f (toSol (cross_list uInput xfList) rr (toInit a))" 
    by (metis lambda_one real_scaleR_def)}
  from this have "\<forall> rr \<in> {0<--< 2 \<cdot> r}. f' rr = 
  (f (toSol (cross_list uInput xfList) rr (toInit a)))" by force}
then have f'Hyp:"\<forall> f'. ((\<lambda>s. u s (toInit a)) has_vderiv_on f') {0<--<2 \<cdot> r} \<longrightarrow> 
(\<forall> rr \<in> {0<--< 2 \<cdot> r}. f' rr = (f (toSol (cross_list uInput xfList) rr (toInit a))))" by force
have "((\<lambda>s. u s (toInit a)) has_vderiv_on 
(vderiv_of (\<lambda>r. u r (toInit a)) {0<--< (2 *\<^sub>R r)})) {0<--<2 \<cdot> r}"
by(simp add: vderiv_of_def, metis derivHyp someI_ex)
from this and f'Hyp have "\<forall> rr \<in> {0<--< 2 \<cdot> r}. 
(vderiv_of (\<lambda>r. u r (toInit a)) {0<--< (2 *\<^sub>R r)}) rr = 
(f (toSol (cross_list uInput xfList) rr (toInit a)))" by blast
thus "vderiv_of (\<lambda>r. \<pi>\<^sub>1 (u, x, f) r (toInit a)) {0<--<2 *\<^sub>R r} r = 
\<pi>\<^sub>2 (\<pi>\<^sub>2 (u, x, f)) (toSol (cross_list uInput xfList) r (toInit a))" 
using rHyp2 open_segment_eq_real_ivl by force
qed

lemma conds4vdiffs:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and lengthHyp:"length xfList = length uInput"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
shows "\<forall> st. \<forall> t\<ge>0. \<forall>r\<in>{0<--<t}. \<forall> xf\<in>set xfList. 
(toSol (cross_list uInput xfList) r (toInit st)) (vdiff (\<pi>\<^sub>1 xf)) = 
\<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) r (toInit st))"
apply(rule prelim_conds4vdiffs)
subgoal using distinctHyp by simp
subgoal using varsHyp by simp
subgoal using lengthHyp by simp
subgoal using assms and keyFact_elim by blast
done

lemma conds4Consts: (* toSol sends variables not in the system (i.e. constants) to zero.  *)
assumes varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
shows "\<forall> t \<ge> 0. \<forall> str \<in> (varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)). 
(toSol (cross_list uInput xfList) t (toInit a)) str = 0"
using assms by(induction xfList uInput rule: cross_list.induct, simp_all)

lemma conds4RestOfStrings: (* NONE, i.e. toSol keeps the initial state everywhere else. *)
"\<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> 
(toSol (cross_list uInput xfList) t (toInit a)) str = a str"
apply(induction xfList uInput rule: cross_list.induct)
by(auto simp: varDiffs_def)

lemma conds4solvesIVP:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
(\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (cross_list uInput xfList). 
  (\<pi>\<^sub>1 uxf) 0 (toInit st) = (toInit st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. \<forall>t\<ge>0.\<forall>xf\<in>set xfList. ((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
solvesTheIVP (\<lambda>t r. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st))) 
withInitCond  0 \<mapsto> st (\<pi>\<^sub>1 xf)) {0--t} UNIV"
apply(rule allI, rule allI, rule impI, rule ballI, rule solves_ivpI, rule solves_odeI)
subgoal using solHyp1 by simp
subgoal using solHyp2 by simp
proof(clarify, rename_tac a t x f)
fix t::real and x::string and f::"real store \<Rightarrow> real" and a::"real store"
assume tHyp:"0 \<le> t" and xfHyp:"(x, f) \<in> set xfList"
then obtain u where uxfHyp:"(u, x, f) \<in> set (cross_list uInput xfList)"
by (metis crossList_map_projElim in_set_impl_in_set_zip2 lengthHyp map_fst_zip map_snd_zip)
from varsHyp have toInitHyp:"(toInit a) x = a x" using override_on_def xfHyp by auto
from uxfHyp and solHyp3 have "u 0 (toInit a) = (toInit a) x" by fastforce
also have "toSol (cross_list uInput xfList) 0 (toInit a) (\<pi>\<^sub>1 (x, f)) = u 0 (toInit a)" 
using toSol_crossList_uxf_onX uxfHyp and assms by fastforce
ultimately show "toSol (cross_list uInput xfList) 0 (toInit a) (\<pi>\<^sub>1 (x, f)) = a (\<pi>\<^sub>1 (x, f))"
using toInitHyp by simp
qed

lemma conds4storeIVP_on_toSol:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and initHyp:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList). (\<pi>\<^sub>1 uxf) 0 st = st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol (cross_list uInput xfList) t (toInit st))"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
(\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (cross_list uInput xfList). 
  (\<pi>\<^sub>1 uxf) 0 (toInit st) = (toInit st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<forall> st. solvesStoreIVP (\<lambda> t. toSol (cross_list uInput xfList) t (toInit st)) xfList st G"
apply(rule allI, rule solves_store_ivpI)
subgoal using conds4InitState initHyp by blast
subgoal using guardHyp by simp
subgoal using conds4InitState2 and assms by blast
subgoal using conds4RestOfStrings by blast
subgoal using conds4Consts varsHyp  by blast
subgoal using conds4vdiffs and assms by blast
subgoal using conds4solvesIVP and assms by blast
done

theorem dSolve_toSolve:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and initHyp:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList). (\<pi>\<^sub>1 uxf) 0 st = st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol (cross_list uInput xfList) t (toInit st))"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
(\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (cross_list uInput xfList). 
  (\<pi>\<^sub>1 uxf) 0 (toInit st) = (toInit st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and uniqHyp:"\<forall> st. \<forall> X. X solvesTheStoreIVP xfList withInitState st andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. (toSol (cross_list uInput xfList) t (toInit st)) = X t)"
and diffAssgn: "\<forall>st. P st \<longrightarrow> 
(\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit st))) \<longrightarrow> 
\<lfloor>wp (mass_gets (cross_list uInput xfList) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
subgoal using assms and conds4storeIVP_on_toSol by simp
subgoal by (simp add: uniqHyp)
using diffAssgn by simp

(* As before, we keep refining the rule dSolve. This time we find the necessary restrictions on 
to attain uniqueness. *)

(* OBSERVATIONS *)
term "unique_on_bounded_closed t0 T x0 f X L"
thm unique_on_bounded_closed_def
thm unique_on_bounded_closed_axioms_def
thm unique_on_closed_def
(* These equivalences help Isabelle a lot. *)
thm closed_segment_eq_real_ivl
thm open_segment_eq_real_ivl

lemma conds4UniqSol:
assumes sHyp:"s \<ge> 0"
assumes contHyp:"\<forall> xf \<in> set xfList. continuous_on ({0--s} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a)))"
shows "\<forall> xf \<in> set xfList. unique_on_bounded_closed 0 {0--s} (a (\<pi>\<^sub>1 xf)) 
(\<lambda>t (r::real). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a))) 
UNIV (if s = 0 then 1 else 1/(s+1))"
apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def 
unique_on_closed_def compact_interval_def compact_interval_axioms_def nonempty_set_def 
interval_def self_mapping_def self_mapping_axioms_def closed_domain_def global_lipschitz_def 
lipschitz_def, rule conjI)
subgoal using contHyp continuous_rhs_def by fastforce 
subgoal 
  apply(simp add: closed_segment_eq_real_ivl)
  using contHyp continuous_rhs_def real_Icc_closed_segment sHyp by fastforce 
done

lemma solves_store_ivp_at_beginning_overrides:
assumes Fsolves:"solvesStoreIVP F xfList a G"
shows "F 0 = override_on a (F 0) varDiffs"
using assms unfolding solvesStoreIVP_def 
and override_on_def by auto

lemma ubcStoreUniqueSol:
assumes sHyp:"s \<ge> 0"
assumes contHyp:"\<forall> xf \<in> set xfList. continuous_on ({0--s} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a)))"
and eqDerivs:"\<forall> xf \<in> set xfList. \<forall> t \<in> {0--s}. 
(\<pi>\<^sub>2 xf) (F t) = (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a))"
and Fsolves:"solvesStoreIVP F xfList a G"
and solHyp:"solvesStoreIVP (\<lambda> t. (toSol (cross_list uInput xfList) t (toInit a))) xfList a G"
shows "(toSol (cross_list uInput xfList) s (toInit a)) = F s"
proof
  fix str::"string" show "(toSol (cross_list uInput xfList) s (toInit a)) str = F s str"
  proof(cases "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs")
  case False
    then have notInVars:"str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs" by simp
    from solHyp have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> 
    (toSol (cross_list uInput xfList) t (toInit a)) str = a str"
    by (simp add: solvesStoreIVP_def) 
    hence 1:"(toSol (cross_list uInput xfList) s (toInit a)) str = a str" using sHyp notInVars
    by blast
    from Fsolves have "\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<union> varDiffs \<longrightarrow> F t str = a str" 
    by (simp add: solvesStoreIVP_def) 
    then have 2:"F s str = a str" using sHyp notInVars by blast
    thus "toSol (cross_list uInput xfList) s (toInit a) str = F s str" using 1 and 2 by simp
  next case True
    then have "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>) \<or> str \<in> varDiffs" by simp
    moreover
    {assume "str \<in> (\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>)" from this obtain f::"((char list \<Rightarrow> real) \<Rightarrow> real)" where 
      strfHyp:"(str, f) \<in> set xfList" by fastforce
      (* Expand hypothesis for arbitrary solution. *)
      from Fsolves and sHyp have "(\<forall> xf \<in> set xfList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP 
      (\<lambda>t r. \<pi>\<^sub>2 xf (F t)) withInitCond  0 \<mapsto> a (\<pi>\<^sub>1 xf)) {0--s} UNIV)" 
      by (simp add: solvesStoreIVP_def)
      then have expand1:"\<forall> xf \<in> set xfList.((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (F t))){0--s} UNIV \<and> F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" by (simp add: solves_ivp_def)
      hence expand2:"\<forall> xf \<in> set xfList. \<forall> t \<in> {0--s}.
      ((\<lambda>r. F r (\<pi>\<^sub>1 xf)) has_vector_derivative 
      (\<lambda>r. (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a))) t) (at t within {0--s})" 
      using eqDerivs by (simp add: solves_ode_def has_vderiv_on_def)
      (* Re-express hypothesis for arbitrary solution in terms of user solution.*)
      then have "\<forall> xf \<in> set xfList. ((\<lambda>t. F t (\<pi>\<^sub>1 xf)) solves_ode 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a)))){0--s} UNIV \<and> 
      F 0 (\<pi>\<^sub>1 xf) = a (\<pi>\<^sub>1 xf)" 
      by (simp add: has_vderiv_on_def solves_ode_def expand1 expand2) 
      then have 1:"((\<lambda>t. F t str) solvesTheIVP 
      (\<lambda>t r. f (toSol (cross_list uInput xfList) t (toInit a))) withInitCond  0 \<mapsto> a str) 
      {0--s} UNIV" using strfHyp solves_ivp_def by fastforce
      (* Expand hypothesis for user's solution. *)
      from solHyp and strfHyp have 2:"((\<lambda> t. toSol (cross_list uInput xfList) t (toInit a) str) 
      solvesTheIVP (\<lambda>t r. f (toSol (cross_list uInput xfList) t (toInit a))) 
      withInitCond  0 \<mapsto> a str) {0--s} UNIV" 
      using solvesStoreIVP_def sHyp by fastforce
      (* Show user's solution and arbitrary solution are the same. *)
      from sHyp and contHyp have "\<forall> xf \<in> set xfList. unique_on_bounded_closed 0 {0--s} (a (\<pi>\<^sub>1 xf)) 
      (\<lambda>t r. (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a))) 
      UNIV (if s = 0 then 1 else 1/(s+1))" using conds4UniqSol by simp
      from this have 3:"unique_on_bounded_closed 0 {0--s} (a str) 
      (\<lambda>t r. f (toSol (cross_list uInput xfList) t (toInit a))) 
      UNIV (if s = 0 then 1 else 1/(s+1))" using strfHyp by fastforce
      from 1 2 and 3 have "toSol (cross_list uInput xfList) s (toInit a) str = F s str"
      using unique_on_bounded_closed.ivp_unique_solution by blast}
    moreover
    {assume "str \<in> varDiffs"
      then obtain x where xDef:"str = vdiff x" by (auto simp: varDiffs_def)
      have "toSol (cross_list uInput xfList) s (toInit a) str = F s str "
      proof(cases "x \<in> set (map \<pi>\<^sub>1 xfList)")
      case True
        then obtain f::"((char list \<Rightarrow> real) \<Rightarrow> real)" where 
        strFhyp:"(x, f) \<in> set xfList" by fastforce
        show ?thesis
        proof(cases "s = 0")
        case True
          from this and Fsolves have "F s str = f (F s)"
          using solvesStoreIVP_def strFhyp xDef by auto
          moreover from solHyp and True have "toSol (cross_list uInput xfList) s (toInit a) str = 
          f (toSol (cross_list uInput xfList) s (toInit a))" 
          using solvesStoreIVP_def strFhyp xDef by auto
          ultimately show ?thesis using eqDerivs strFhyp by auto 
        next
        case False (* str \<in> varDiffs \<and> (x, f) \<in> set xfList \<and> s \<noteq> 0*)
          then have "s > 0" using sHyp by simp
          hence "2 \<cdot> s > 0" by simp
          from this and Fsolves have "\<forall>r\<in>{0<--<2 \<cdot> s}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = 
          \<pi>\<^sub>2 xf (F r)" by (metis less_eq_real_def solves_store_ivpD(6)) 
          from this have 1:"F s str = f (F s)"
          using strFhyp xDef \<open>0 < s\<close> open_segment_eq_real_ivl by fastforce 
          from \<open>2 \<cdot> s > 0\<close> and solHyp have "\<forall>r\<in>{0<--<2 \<cdot> s}. \<forall> xf \<in> set xfList. 
          toSol (cross_list uInput xfList) r (toInit a) (vdiff (\<pi>\<^sub>1 xf)) = 
          \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) r (toInit a))" 
          by (metis less_eq_real_def solves_store_ivpD(6)) 
          from this have 2:"toSol (cross_list uInput xfList) s (toInit a) str = 
          f (toSol (cross_list uInput xfList) s (toInit a))"
          using strFhyp xDef \<open>0 < s\<close> open_segment_eq_real_ivl by fastforce 
          from 1 and 2 show ?thesis using eqDerivs strFhyp by auto 
        qed   
      next
      case False
        then have strHyp:"str \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)" 
        using xDef \<open>str \<in> varDiffs\<close>  vdiff_inj by (metis (no_types, lifting) DiffI imageE set_map) 
        from this Fsolves and sHyp have "F s str = 0" 
        using solvesStoreIVP_def by simp
        also have "toSol (cross_list uInput xfList) s (toInit a) str = 0" 
        using strHyp solHyp sHyp solvesStoreIVP_def by simp
        ultimately show ?thesis by simp
      qed}
    ultimately show "toSol (cross_list uInput xfList) s (toInit a) str = F s str" by blast
  qed
qed

theorem dSolveUBC:
assumes contHyp:"\<forall> st. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit st)))"
and solHyp:"\<forall> st. solvesStoreIVP (\<lambda> t. (toSol (cross_list uInput xfList) t (toInit st))) xfList st G"
and uniqHyp:"\<forall> st. \<forall> X. X solvesTheStoreIVP xfList withInitState st andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0--t}. (\<pi>\<^sub>2 xf) (X r) = 
(\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) r (toInit st)))"
and diffAssgn: "\<forall>st. P st \<longrightarrow> 
(\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit st))) \<longrightarrow> 
\<lfloor>wp (mass_gets (cross_list uInput xfList) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolve)
subgoal using solHyp by simp
subgoal proof(clarify)
fix a::"real store" and X::"real \<Rightarrow> real store" and s::"real"
assume XisSol:"solvesStoreIVP X xfList a G" and sHyp:"0 \<le> s"
from this and uniqHyp have "\<forall> xf \<in> set xfList. \<forall> t \<in> {0--s}. 
(\<pi>\<^sub>2 xf) (X t) = (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a))" 
by(auto simp: closed_segment_eq_real_ivl) (* This equivalence helps Isabelle a lot. *)
moreover have "\<forall> xf \<in> set xfList. continuous_on ({0--s} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit a)))" 
using contHyp sHyp by blast
moreover from solHyp have "(\<lambda>t. toSol (cross_list uInput xfList) t (toInit a)) solvesTheStoreIVP 
xfList withInitState a andGuard G" by simp
ultimately show "toSol (cross_list uInput xfList) s (toInit a) = X s" 
using sHyp XisSol ubcStoreUniqueSol by simp
qed
subgoal using diffAssgn by simp
done

theorem dSolve_toSolveUBC:
assumes funcsHyp:"\<forall> st. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on st g varDiffs) = \<pi>\<^sub>2 xf st" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and initHyp:"\<forall> st. \<forall> uxf \<in> set (cross_list uInput xfList). (\<pi>\<^sub>1 uxf) 0 st = st (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and guardHyp:"\<forall> st. \<forall>t\<ge>0. G (toSol (cross_list uInput xfList) t (toInit st))"
and solHyp1:"\<forall> st. \<forall>t\<ge>0. \<forall> xf \<in> set xfList. 
((\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) 
has_vderiv_on (\<lambda>t. \<pi>\<^sub>2 xf (toSol (cross_list uInput xfList) t (toInit st)))) {0--t}" 
and solHyp2:"\<forall> st. \<forall>t\<ge>0. \<forall>xf\<in>set xfList. 
(\<lambda>t. (toSol (cross_list uInput xfList) t (toInit st)) (\<pi>\<^sub>1 xf)) \<in> {0--t} \<rightarrow> UNIV"
and solHyp3:"\<forall> st. \<forall>uxf\<in>set (cross_list uInput xfList). 
  (\<pi>\<^sub>1 uxf) 0 (toInit st) = (toInit st) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and contHyp:"\<forall> st. \<forall> t\<ge>0. \<forall> xf \<in> set xfList. continuous_on ({0--t} \<times> UNIV) 
(\<lambda>(t, (r::real)). (\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) t (toInit st)))"
and uniqHyp:"\<forall> st. \<forall> X. X solvesTheStoreIVP xfList withInitState st andGuard G \<longrightarrow> 
(\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. \<forall> r \<in> {0--t}. (\<pi>\<^sub>2 xf) (X r) = 
(\<pi>\<^sub>2 xf) (toSol (cross_list uInput xfList) r (toInit st)))"
and diffAssgn: "\<forall>st. P st \<longrightarrow> 
(\<forall>t\<ge>0. (\<forall>r \<in> {0<--< t}. G (toSol (cross_list uInput xfList) r (toInit st))) \<longrightarrow> 
\<lfloor>wp (mass_gets (cross_list uInput xfList) t) \<lceil>Q\<rceil>\<rfloor> st)"
shows "PRE P (ODEsystem xfList with G) POST Q"
apply(rule_tac uInput="uInput" in dSolveUBC)
subgoal using contHyp by simp
subgoal
  apply(rule_tac uInput="uInput" in conds4storeIVP_on_toSol)
  using assms by auto
subgoal using uniqHyp by simp
using diffAssgn by simp

thm dSolve
thm dSolve_toSolve
thm dSolveUBC
thm dSolve_toSolveUBC
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

lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (ODEsystem [(''pos'',(\<lambda> s. s ''vel''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
apply(rule_tac uInput="[\<lambda> t s. s ''vel'' \<cdot> t + s ''pos'']" in dSolve_toSolveUBC) (* 12 subgoals *)
prefer 12 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
apply(simp_all add: vdiff_def varDiffs_def)
subgoal
  apply(clarify)
  apply(rule_tac f'1="\<lambda> x. st ''vel''" and g'1="\<lambda> x. 0" in derivative_intros(173))(* 3 goals appear. *)
  apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))           (* 3 goals appear. *)
  by(auto intro: derivative_intros)
subgoal by(clarify, rule continuous_intros)
subgoal
  proof(clarify, simp add: closed_segment_eq_real_ivl, safe)
  fix st X and t r::"real"
  assume " X solvesTheStoreIVP [(''pos'', \<lambda>s. s ''vel'')] withInitState st andGuard (\<lambda>s. True)"
  from this have 1:"\<forall>t\<ge>0. \<forall>str. str \<notin> (\<pi>\<^sub>1\<lbrakk>set [(''pos'', \<lambda>s. s ''vel'')]\<rbrakk>) \<union> varDiffs \<longrightarrow> 
  X t str = st str" by (simp add: solvesStoreIVP_def)
  assume "0 \<le> r" and "r \<le> t"
  from this and 1 have "\<forall>str. str \<noteq> ''pos'' \<and> str \<notin> varDiffs \<longrightarrow> X t str = st str" by simp
  then show "X r ''vel'' = st ''vel''" using vdiff_def by (simp add: varDiffs_def "1" \<open>0 \<le> r\<close>)
  qed
done

lemma "PRE (\<lambda> s. s ''station'' < s ''x''  \<and> s ''v'' \<ge> 0 \<and> s ''a'' > 0)  
      (ODEsystem [(''x'',(\<lambda> s. s ''v'')),(''v'',(\<lambda> s. s ''a''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''x''))"
apply(rule_tac uInput="[\<lambda> t s. s ''a'' \<cdot> t ^ 2/2 + s ''v'' \<cdot> t + s ''x'', 
  \<lambda> t s. s ''a'' \<cdot> t + s ''v'']" in dSolve_toSolveUBC)
prefer 12 subgoal by(simp add: wp_trafo vdiff_def add_strict_increasing2)
prefer 7 subgoal (* DERIVATIVES *)
    apply(simp add: vdiff_def, clarify, rule conjI)
    apply(rule_tac f'1="\<lambda>x. st ''a'' \<cdot> x + st ''v''" and g'1="\<lambda> x. 0" in derivative_intros(173))
    apply(rule_tac f'1="\<lambda>x. st ''a'' \<cdot> x" and g'1="\<lambda> x. st ''v''" in derivative_intros(173))
    subgoal sorry (*(* OBS: *) thm derivative_eq_intros(1)*)
    apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x. 1" in derivative_intros(176))
    by(rule derivative_intros, simp_all)+
prefer 9 subgoal (* CONTINUITY *)
    apply(auto simp: vdiff_def)
    prefer 2 apply(rule continuous_intros)
    sorry
prefer 9 subgoal (* UNIQUENESS *)
    apply(auto simp: vdiff_def closed_segment_eq_real_ivl)
    prefer 2 subgoal by(simp add: solvesStoreIVP_def vdiff_def varDiffs_def)
    proof-
    fix st X and t r::real 
    assume solHyp:"solvesStoreIVP X [(''x'', \<lambda>s. s ''v''), (''v'', \<lambda>s. s ''a'')] st (\<lambda> s. True)"
    and rHyp:"0 \<le> r" and tHyp:"r \<le> t"
    then have 1:"((\<lambda>t. X t ''v'') solvesTheIVP (\<lambda>t r. X t ''a'') 
    withInitCond  0 \<mapsto> st ''v'') {0--t} UNIV" by (simp add: solvesStoreIVP_def)
    from solHyp rHyp and tHyp have "\<forall> t \<ge> 0. X t ''a'' = st ''a''" 
    using solvesStoreIVP_def by (simp add: varDiffs_def vdiff_def)
    hence obs:"\<forall> s \<in> {0--t}. X s ''a'' = st ''a''" 
    using rHyp tHyp closed_segment_eq_real_ivl by simp
    have 2:"((\<lambda>t. st ''a'' \<cdot> t + st ''v'') solvesTheIVP (\<lambda>t r. X t ''a'') 
    withInitCond  0 \<mapsto> st ''v'') {0--t} UNIV"
      apply(simp add: solves_ivp_def solves_ode_def)
      apply(rule_tac f'1="\<lambda> x. st ''a''" and g'1="\<lambda> x. 0" in derivative_intros(173))
      apply(rule_tac f'1="\<lambda> x.0" and g'1="\<lambda> x.1" in derivative_intros(176))
      apply(rule derivative_intros, simp)+
      apply(simp, rule derivative_intros, simp)
      using obs by simp
    have 3:"unique_on_bounded_closed 0 {0--t} (st ''v'') (\<lambda>t r. X t ''a'') UNIV  (if t = 0 then 1 else 1/(t+1))"
      apply(simp add: unique_on_bounded_closed_def unique_on_bounded_closed_axioms_def 
        unique_on_closed_def compact_interval_def compact_interval_axioms_def nonempty_set_def 
        interval_def self_mapping_def self_mapping_axioms_def closed_domain_def global_lipschitz_def 
        lipschitz_def, rule conjI)
      using rHyp tHyp obs apply(simp_all add: continuous_rhs_def closed_segment_eq_real_ivl, clarify)
      apply (auto)
      sorry
    from 1 2 and 3 have "\<forall> s \<in> {0--t}. X s ''v'' = st ''a'' \<cdot> s + st ''v''"
    using unique_on_bounded_closed.ivp_unique_solution by blast
    thus "X r ''v'' = st ''a'' \<cdot> r + st ''v''" using rHyp tHyp closed_segment_eq_real_ivl by simp
    qed
by(auto simp: varDiffs_def vdiff_def)

-- "Differential Invariant."
(* Observation *)
value "0 = 1 / (0::real)"
lemma "0 = a / (0::real)"
by(auto)
thm has_field_derivative_iff_has_vector_derivative
thm derivative_eq_intros(37)
thm derivative_eq_intros(25)

datatype trms = Const real | Var string | Mns trms | Sum trms trms | Mult trms trms
(* Const real | Var string | Mns trms | Inv trms | Sum trms trms | Mult trms trms *)

primrec rval ::"trms \<Rightarrow> (real store \<Rightarrow> real)" where
"rval (Const r) = (\<lambda> s. r)"|
"rval (Var x) = (\<lambda> s. s x)"|
"rval (Mns \<theta>) = (\<lambda> s. - (rval \<theta> s))"|
(*"rval (Inv \<theta>) = (\<lambda> s. 1/(rval \<theta> s))"|*)
"rval (Sum \<theta> \<eta>) = (\<lambda> s. rval \<theta> s + rval \<eta> s)"|
"rval (Mult \<theta> \<eta>) = (\<lambda> s. rval \<theta> s \<cdot> rval \<eta> s)"

datatype props = Eq trms trms | Less trms trms | Neg props | And props props | Or props props

primrec pval ::"props \<Rightarrow> (real store \<Rightarrow> bool)" where
"pval (Eq \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s = (rval \<eta>) s)"|
"pval (Less \<theta> \<eta>) = (\<lambda> s. (rval \<theta>) s < (rval \<eta>) s)"|
"pval (Neg \<phi>) = (\<lambda> s. \<not> (pval \<phi>) s)"|
"pval (And \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<and> (pval \<psi>) s)"|
"pval (Or \<phi> \<psi>) = (\<lambda> s. (pval \<phi>) s \<or> (pval \<psi>) s)"

primrec rdiff ::"trms \<Rightarrow> trms" where
"rdiff (Const r) = Const 0"|
"rdiff (Var x) = Var (vdiff x)"|
"rdiff (Mns \<theta>) = Mns (rdiff \<theta>)"|
(*"rdiff (Inv \<theta>) = Mult (Mns (rdiff \<theta>)) (Inv (Mult \<theta> \<theta>))"|*)
"rdiff (Sum \<theta> \<eta>) = Sum (rdiff \<theta>) (rdiff \<eta>)"|
"rdiff (Mult \<theta> \<eta>) = Sum (Mult (rdiff \<theta>) \<eta>) (Mult \<theta> (rdiff \<eta>))"

(*value "rval (Sum (Mult (Var ''x'') (Const c)) (Inv (Var ''y'')))"
value "rval (rdiff (Sum (Mult (Var ''x'') (Const c)) (Inv (Var ''y''))))"
value "rval (Sum (Mult (Var ''y'') (Inv (Var ''x''))) (Const c) )"
value "rval (rdiff (Sum (Mult (Var ''y'') (Inv (Var ''x''))) (Const c) ))"*)

primrec pdiff ::"props \<Rightarrow> props" where
"pdiff (Eq \<theta> \<eta>) = Eq (rdiff \<theta>) (rdiff \<eta>)"|
"pdiff (Less \<theta> \<eta>) = Or (Less (rdiff \<theta>) (rdiff \<eta>)) (Eq (rdiff \<theta>) (rdiff \<eta>))"|
"pdiff (Neg \<phi>) = pdiff \<phi>"|
"pdiff (And \<phi> \<psi>) = And (pdiff \<phi>) (pdiff \<psi>)"|
"pdiff (Or \<phi> \<psi>) = Or (pdiff \<phi>) (pdiff \<psi>)"

(*value "pval (Eq (Mult (Var ''x'') (Const c)) (Sum (Var ''y'') (Var ''z'')))"
value "pval (pdiff (Eq (Mult (Var ''x'') (Const c)) (Sum (Var ''y'') (Var ''z''))))"
value "(pval (Less (Var ''x'') (Var ''z''))) (\<lambda> str. if str = ''x'' then 0 else 1)"
value "(pval (pdiff (Less (Var ''x'') (Var ''z'')))) (\<lambda> str. if str = ''d[x]'' then 2 else 1)"
value "pval (And (Or (Less (Var ''x'') (Const c)) (Less (Const c) (Var ''x''))) 
                (Neg (Eq (Mult (Var ''x'') (Const c)) (Sum (Inv (Var ''y'')) (Var ''z'')))))"
value "pval (pdiff (And (Or (Less (Var ''x'') (Const c)) (Less (Const c) (Var ''x''))) 
                (Neg (Eq (Mult (Var ''x'') (Const c)) (Sum (Inv (Var ''y'')) (Var ''z''))))) )"*)

(*primrec subst :: "trms \<Rightarrow> string \<Rightarrow> trms \<Rightarrow> trms" where
"subst \<xi> y (Const r) = Const r"|
"subst \<xi> y (Var x) = (if x = y then \<xi> else Var x)"|
"subst \<xi> y (Mns \<theta>) = Mns (subst \<xi> y \<theta>)"|
(*"subst \<xi> y (Inv \<theta>) = Inv (subst \<xi> y \<theta>)"|*)
"subst \<xi> y (Sum \<theta> \<eta>) = (Sum (subst \<xi> y \<theta>) (subst \<xi> y \<eta>))"|
"subst \<xi> y (Mult \<theta> \<eta>) = (Mult (subst \<xi> y \<theta>) (subst \<xi> y \<eta>))"

primrec subsp :: "trms \<Rightarrow> string \<Rightarrow> props \<Rightarrow> props" where
"subsp \<xi> y (Eq \<theta> \<eta>) = (Eq (subst \<xi> y \<theta>) (subst \<xi> y \<eta>))"|
"subsp \<xi> y (Less \<theta> \<eta>) = (Less (subst \<xi> y \<theta>) (subst \<xi> y \<eta>))"|
"subsp \<xi> y (Neg \<phi>) = Neg (subsp \<xi> y \<phi>)"|
"subsp \<xi> y (And \<phi> \<psi>) = (And (subsp \<xi> y \<phi>) (subsp \<xi> y \<psi>))"|
"subsp \<xi> y (Or \<phi> \<psi>) = (Or (subsp \<xi> y \<phi>) (subsp \<xi> y \<psi>))"

lemma preSubstLemma:"(rval (subst \<theta> x \<eta>)) a = (rval \<eta>) (a(x := (rval \<theta>) a))"
by(induction \<eta>, simp_all)

lemma substLemma:"(pval (subsp \<theta> x \<phi>)) a = (pval \<phi>) (a(x := (rval \<theta>) a))"
apply(induction \<phi>, simp_all only: subsp.simps pval.simps)
using preSubstLemma by auto

lemma preSubstPrprty:"(pval (Eq (Var x) \<theta>)) a \<Longrightarrow> (rval (subst \<theta> x \<eta>)) a = (rval \<eta>) a"
by(induction \<eta>, simp_all)

lemma substPrprty:"(pval (Eq (Var x) \<theta>)) a \<Longrightarrow> (pval (subsp \<theta> x \<phi>)) a = (pval \<phi>) a"
apply(induction \<phi>, simp_all only: subsp.simps pval.simps)
using preSubstPrprty by auto *)

lemma storeIVP_on_its_vdiffs:
fixes F::"real \<Rightarrow> real store"
assumes storeIVP_dvars:"\<forall> t \<ge> 0. \<forall> r \<in> {0<--<t}. 
\<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
and srtoreIVP_init_dvars:"\<forall> xf \<in>set xfList. F 0 (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)"
shows "\<forall> t \<ge> 0. \<forall> r \<in> {0--t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
proof(clarify)
fix x f and t r::real
assume tHyp:"0 \<le> t" and rHyp:"r \<in> {0--t}" and xfHyp:"(x, f) \<in> set xfList"
{assume "r = 0" then have "F r (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (F r)" 
  using xfHyp and srtoreIVP_init_dvars by blast}
hence r0:"r = 0 \<longrightarrow> F r (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (F r)" by simp
show "F r (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (F r)"
  proof(cases "t=0")
    case True
    then have "r = 0" 
    using rHyp by (simp add: closed_segment_eq_real_ivl)
    then show ?thesis using r0 by simp
  next
    case False
    then show ?thesis 
    proof(cases "r = 0")
      case True
      then show ?thesis 
      using r0 by simp
    next
      case False then have trHypRef:"2 \<cdot> t \<ge> 0 \<and> r \<in> {0<--<2 \<cdot> t}" 
      using closed_segment_eq_real_ivl open_segment_eq_real_ivl rHyp tHyp by auto
      thus ?thesis using storeIVP_dvars xfHyp by (metis fst_conv snd_conv)
    qed
  qed
qed

lemma solvesStoreIVP_couldBeModified:
fixes F::"real \<Rightarrow> real store"
assumes storeIVP_vars:"\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) 
solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) withInitCond 0 \<mapsto> (a (\<pi>\<^sub>1 xf))) {0--t} UNIV"
and storeIVP_dvars:"\<forall> t \<ge> 0. \<forall> r \<in> {0<--<t}. \<forall>xf\<in>set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
and srtoreIVP_init_dvars:"\<forall> xf \<in>set xfList. F 0 (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)"
shows "\<forall> t \<ge> 0. \<forall> r \<in> {0--t}. \<forall> xf \<in> set xfList. 
((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (vdiff (\<pi>\<^sub>1 xf))) (at r within {0--t})"
proof(clarify)
fix x f and t r::real
assume rHyp:"r \<in> {0--t}" and tHyp:"0 \<le> t" and xfHyp:"(x, f) \<in> set xfList" 
from this and storeIVP_vars have "((\<lambda> t. F t x) solvesTheIVP (\<lambda> t. \<lambda> r. f (F t)) 
withInitCond 0 \<mapsto> (a x)) {0--t} UNIV" using tHyp by fastforce
then have "((\<lambda> t. F t x) has_vderiv_on (\<lambda> t. f (F t))) {0--t}" 
by (simp add: solves_ode_def solves_ivp_def)
hence *:"((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) r) (at r within {0--t})" 
by (simp add: has_vderiv_on_def rHyp tHyp)
have "\<forall> t \<ge> 0. \<forall> r \<in> {0--t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
using assms storeIVP_on_its_vdiffs by blast
from this rHyp tHyp and xfHyp have "(F r (vdiff x)) = f (F r)" by force
then show "((\<lambda>t. F t (\<pi>\<^sub>1 (x, f))) has_vector_derivative 
F r (vdiff (\<pi>\<^sub>1 (x, f)))) (at r within {0--t})" using * by auto
qed

lemma derivationLemma_baseCase:
fixes F::"real \<Rightarrow> real store"
assumes solves:"solvesStoreIVP F xfList a G"
shows "\<forall> x \<in> (UNIV - varDiffs). \<forall> t \<ge> 0. \<forall> r \<in> {0--t}.
((\<lambda> t. F t x) has_vector_derivative F r (vdiff x)) (at r within {0--t})"
proof
fix x
assume "x \<in> UNIV - varDiffs"
then have notVarDiff:"\<forall> z. x \<noteq> vdiff z" using varDiffs_def by fastforce
  show "\<forall>t\<ge>0. \<forall>r\<in>{0--t}. ((\<lambda>t. F t x) has_vector_derivative F r (vdiff x)) (at r within {0--t})"
  proof(cases "x \<in> set (map \<pi>\<^sub>1 xfList)")
    case True
    from this and solves have "\<forall> t \<ge> 0. \<forall> r \<in> {0--t}. \<forall> xf \<in> set xfList. 
    ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative F r (vdiff (\<pi>\<^sub>1 xf))) (at r within {0--t})"
    apply(rule_tac a="a" in solvesStoreIVP_couldBeModified) using solves solves_store_ivpD by auto
    from this show ?thesis using True by auto
  next
    case False
    from this notVarDiff and solves have const:"\<forall> t \<ge> 0. F t x = a x" 
    using solves_store_ivpD(4) by (simp add: varDiffs_def)
    have "\<forall> t \<ge> 0. \<forall> r \<in> {0--t}.((\<lambda> t. a x) has_vector_derivative 0) (at r within {0--t})"
    by (auto intro: derivative_eq_intros)
    from this and const have isZero:"\<forall> t \<ge> 0. \<forall> r \<in> {0--t}.((\<lambda> t. F t x) 
    has_vector_derivative 0) (at r within {0--t})"
    by (metis Interval_Integral.has_vector_derivative_weaken atLeastAtMost_iff  
      closed_segment_real has_vector_derivative_const subset_refl)
    have "vdiff x \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>)"
    by (metis (no_types, lifting) Diff_iff image_iff list.set_map varDiffsI vdiff_inj False) 
    from this solves and notVarDiff have "\<forall> t \<ge> 0.\<forall> r \<in> {0--t}. F r (vdiff x) = 0"
    using solves_store_ivpD(5) closed_segment_real by simp
    then show ?thesis using isZero by simp
  qed
qed

(*lemma has_real_vector_derivative_divide:
fixes f::"real \<Rightarrow> real"
assumes "f t \<noteq> 0"
and "(f has_vector_derivative f' t) (at t within S)"
shows "((\<lambda> s. 1/(f s)) has_vector_derivative - (f' t)/ (f t \<cdot> f t)) (at t within S)"
proof-
from assms have 1:"(f has_field_derivative f' t) (at t within S)" 
using has_field_derivative_iff_has_vector_derivative by simp
have 2:"- (f' t)/ (f t \<cdot> f t) = - (inverse (f t) \<cdot> (f' t) \<cdot> inverse (f t)) \<and> 
(\<lambda> s. 1/(f s)) = (\<lambda>s. inverse (f s))"
by (simp add: divide_inverse_commute)
hence "((\<lambda> s. 1/(f s)) has_field_derivative - (f' t)/ (f t \<cdot> f t)) (at t within S)" 
using 1 derivative_eq_intros(37) \<open>f t \<noteq> 0\<close> by force
thus "((\<lambda>s. 1 / f s) has_vector_derivative - f' t / (f t \<cdot> f t)) (at t within S)"
using has_field_derivative_iff_has_vector_derivative by simp
qed*)

primrec trmVars :: "trms \<Rightarrow> string set" where
"trmVars (Const r) = {}"|
"trmVars (Var x) = {x}"|
"trmVars (Mns \<theta>) = trmVars \<theta>"|
(*"trmVars (Inv \<theta>) = trmVars \<theta>"|*)
"trmVars (Sum \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"trmVars (Mult \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"

(*lemma toStar:"(op *\<^sub>R::real \<Rightarrow> real \<Rightarrow> real) = (op \<cdot>::real \<Rightarrow> real \<Rightarrow> real)"
apply(rule ext) using scaleR_conv_of_real by auto

primrec well_defined ::"(real store) \<Rightarrow> trms \<Rightarrow> bool" where
"well_defined a (Const r) = True"|
"well_defined a (Var x) = True"|
"well_defined a (Mns \<theta>) = well_defined a \<theta>"|
"well_defined a (Inv \<theta>) = (well_defined a \<theta> \<and> rval \<theta> a \<noteq> 0)"|
"well_defined a (Sum \<theta> \<eta>) = (well_defined a \<theta> \<and> well_defined a \<eta>)"|
"well_defined a (Mult \<theta> \<eta>) = (well_defined a \<theta> \<and> well_defined a \<eta>)"

lemma "(rval \<theta> a = 0) \<Longrightarrow> \<not> well_defined a (Inv \<theta>)"
by(induction \<theta>, simp_all)*)

lemma derivationLemma:
assumes "solvesStoreIVP F xfList a G"
and tHyp:"t \<ge> 0"
and termVarsHyp:"\<forall> x \<in> trmVars \<eta>. x \<in> (UNIV - varDiffs)"
(*shows "\<forall> r \<in> {0--t}.  well_defined (F r) \<eta> \<longrightarrow> ((\<lambda> s. (rval \<eta>) (F s)) 
has_vector_derivative (rval (rdiff \<eta>)) (F r)) (at r within {0--t})"*)
shows "\<forall> r \<in> {0--t}.  ((\<lambda> s. (rval \<eta>) (F s)) 
has_vector_derivative (rval (rdiff \<eta>)) (F r)) (at r within {0--t})"
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
(*next
  case (Inv \<eta>)
  then show ?case
  proof(clarsimp)
    fix r::real
    assume rHyp:"r \<in> {0--t}" and "well_defined (F r) \<eta>" and "rval \<eta> (F r) \<noteq> 0"
    and IH:"\<forall>r\<in>{0--t}. well_defined (F r) \<eta> \<longrightarrow> ((\<lambda>s. rval \<eta> (F s)) 
    has_vector_derivative rval (rdiff \<eta>) (F r)) (at r within {0--t})"
    from this have rvalRdiff:"((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 
    rval (rdiff \<eta>) (F r)) (at r within {0--t})" by simp
    then show "((\<lambda>s. 1 / rval \<eta> (F s)) has_vector_derivative 
    - (rval (rdiff \<eta>) (F r) / (rval \<eta> (F r) \<cdot> rval \<eta> (F r)))) (at r within {0--t})" 
    using rvalRdiff has_real_vector_derivative_divide \<open>rval \<eta> (F r) \<noteq> 0\<close> by simp
    qed*)
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
  (at r within {0--t})", simp)
  apply(rule_tac f'1="rval (rdiff \<eta>1) (F r)" and 
    g'1="rval (rdiff \<eta>2) (F r)" in derivative_eq_intros(25))
  by (simp_all add: has_field_derivative_iff_has_vector_derivative)
qed

fun substList ::"(string \<times> trms) list \<Rightarrow> trms \<Rightarrow> trms" where
"substList xTrmList (Const r) = Const r"|
"substList [] (Var x) = Var x"|
"substList ((y,\<xi>) # xTrmTail) (Var x) = (if x = y then \<xi> else substList xTrmTail (Var x))"|
"substList xTrmList (Mns \<theta>) = Mns (substList xTrmList \<theta>)"|
(*"substList xTrmList (Inv \<theta>) = Inv (substList xTrmList \<theta>)"|*)
"substList xTrmList (Sum \<theta> \<eta>) = (Sum (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"substList xTrmList (Mult \<theta> \<eta>) = (Mult (substList xTrmList \<theta>) (substList xTrmList \<eta>))"

(*lemma single_substList:"substList [(x,\<theta>)] \<eta> = subst \<theta> x \<eta>"
by(induction \<eta>, simp_all)*)

lemma substList_on_compl_of_varDiffs:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
assumes "set (map \<pi>\<^sub>1 xTrmList) \<subseteq> varDiffs"
shows "substList xTrmList \<eta> = \<eta>"
using assms apply(induction \<eta>, simp_all add: varDiffs_def)
by(induction xTrmList, auto)

lemma substList_help1:"set (map \<pi>\<^sub>1 (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput)) \<subseteq> varDiffs"
apply(induction xfList uInput rule: cross_list.induct, simp_all add: varDiffs_def)
by auto

lemma substList_help2:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) \<eta> = \<eta>"
using assms substList_help1 substList_on_compl_of_varDiffs by blast

lemma solvesStoreIVP_couldBeModified2:
assumes "\<forall> xf \<in> set xfList. F (0::real) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)"
and "\<forall>t\<ge>(0::real). \<forall>r\<in>{0<--<t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
shows "\<forall>t\<ge>(0::real). \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
proof(clarify)
fix t r::real and x f
assume tHyp:"0 \<le> t" and rHyp:"r \<in> {0--t}" and xfHyp:"(x, f) \<in> set xfList"
show "F r (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (F r)"
  proof(cases "r = 0")
    case True
    then show ?thesis 
    using assms(1) rHyp tHyp and xfHyp by auto
  next
  case False
    from this rHyp and tHyp have "r \<in> {0<--<2\<cdot>t} \<and> 2\<cdot>t \<ge> 0"
    using closed_segment_eq_real_ivl open_segment_eq_real_ivl by simp
    then show ?thesis using assms(2) and xfHyp by fastforce
  qed
qed

lemma solvesStoreIVP_couldBeModified3:
assumes "\<forall>t\<ge>(0::real). \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
shows "\<forall> xf \<in> set xfList. F (0::real) (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)"
and "\<forall>t\<ge>(0::real). \<forall>r\<in>{0<--<t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
using assms proof(auto simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl)
fix x f
have "(0::real) \<in> {0..0}" by(simp add: atLeast_def)
assume "(x, f) \<in> set xfList"
from this and assms(1) have "\<forall>r\<in>{0..0}. F r (vdiff (\<pi>\<^sub>1 (x, f))) = \<pi>\<^sub>2 (x, f) (F r)"
using closed_segment_eq_real_ivl atLeastAtMost_iff by blast 
thus "F 0 (vdiff x) = f (F 0)" by auto
qed

lemma substList_cross_vdiff_on_non_ocurring_var:
assumes "x \<notin> set list1"
shows "substList (cross_list (map vdiff list1) list2) (Var (vdiff x))
  = Var (vdiff x)"
using assms apply(induction list1 list2 rule: cross_list.induct, simp, simp, clarsimp)
by(simp add: vdiff_inj)

lemma diff_subst_prprty_4terms:
assumes solves:"\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
and tHyp:"t \<ge> 0"
and rHyp:"r \<in> {0--t}"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "rval (rdiff \<eta>) (F r) = 
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) (F r)"
using termVarsHyp apply(induction \<eta>) apply(simp_all add: substList_help2)
using listsHyp and solves apply(induction xfList uInput rule: cross_list.induct, simp, simp)
proof(clarify, rename_tac y g xfTail \<theta> trmTail x)
fix x y::string and \<theta>::trms and g and xfTail::"((string \<times> (real store \<Rightarrow> real)) list)" and trmTail
assume IH:"\<And>x. x \<notin> varDiffs \<Longrightarrow> map \<pi>\<^sub>2 xfTail = map rval trmTail \<Longrightarrow>
\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall>xf\<in>set xfTail. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r) \<Longrightarrow>
F r (vdiff x) = rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfTail) trmTail) (Var (vdiff x))) (F r)"
and 1:"x \<notin> varDiffs" and 2:"map \<pi>\<^sub>2 ((y, g) # xfTail) = map rval (\<theta> # trmTail)" 
and 3:"\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall>xf\<in>set ((y, g) # xfTail). F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
hence *:"rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfTail) trmTail) (Var (vdiff x))) (F r) = 
F r (vdiff x)" using rHyp tHyp by auto
show "F r (vdiff x) =
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) (\<theta> # trmTail)) (Var (vdiff x))) (F r)"
  proof(cases "x \<in> set ( map \<pi>\<^sub>1 ((y, g) # xfTail))")
    case True
    then have "x = y \<or> (x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail))" by auto
    moreover
    {assume "x = y"
      from this have "substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) (\<theta> # trmTail)) 
      (Var (vdiff x)) = \<theta>" by simp
      also from 3 tHyp and rHyp have "F r (vdiff y) = g (F r)" by simp
      moreover from 2 have "rval \<theta> (F r) = g (F r)" by simp
      ultimately have ?thesis by (simp add: \<open>x = y\<close>)}
    moreover
    {assume "x \<noteq> y \<and> x \<in> set (map \<pi>\<^sub>1 xfTail)"
      then have "vdiff x \<noteq> vdiff y" using vdiff_inj by auto
      from this have "substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) (\<theta> # trmTail)) 
      (Var (vdiff x)) = substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfTail) trmTail) (Var (vdiff x))"
      by simp
      hence ?thesis using * by simp}
    ultimately show ?thesis by blast
  next
    case False
    then have "substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) ((y, g) # xfTail)) (\<theta> # trmTail)) (Var (vdiff x))
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
"\<forall> st. (\<forall> str \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>). st str = 0) \<longrightarrow>
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
shows "(rval \<eta>) a = 0 \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (rval \<eta>) c = 0)"
proof(clarify)
fix c assume aHyp:"(rval \<eta>) a = 0" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" 
using guarDiffEqtn_def by auto
then have "\<forall>x. x \<notin> varDiffs \<longrightarrow> F 0 x = a x" using solves_store_ivpD(1) by blast
from this have "rval \<eta> a = rval \<eta> (F 0)" using termVarsHyp eqInVars_impl_eqInTrms by blast
hence obs1:"rval \<eta> (F 0) = 0" using aHyp tcHyp by simp
(*from FHyp have deriv:"\<forall>r\<in>{0--t}. well_defined (F r) \<eta> \<longrightarrow> ((\<lambda>s. rval \<eta> (F s)) 
has_vector_derivative rval (rdiff \<eta>) (F r)) (at r within {0--t})"*)
from tcHyp have obs2:"\<forall>r\<in>{0--t}. ((\<lambda>s. rval \<eta> (F s)) has_vector_derivative 
rval (rdiff \<eta>) (F r)) (at r within {0--t})" using derivationLemma termVarsHyp by blast
have "(\<forall>xf\<in>set xfList. F 0 (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)) \<and> 
(\<forall>t\<ge>0. \<forall>r\<in>{0<--<t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r))"
using tcHyp solves_store_ivpD(3) solves_store_ivpD(6) by blast
then have "\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
using solvesStoreIVP_couldBeModified2 by blast
from this and tcHyp have "\<forall> \<theta>. \<forall>r\<in>{0--t}. rval (rdiff \<eta>) (F r) =
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) (F r)"
using diff_subst_prprty_4terms termVarsHyp listsHyp by blast
also from substHyp have "\<forall>r\<in>{0--t}. 
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) (F r) = 0" 
using solves_store_ivpD(5) tcHyp using closed_segment_eq_real_ivl by auto 
(*ultimately have "\<forall>r\<in>{0--t}. well_defined (F r) \<eta> \<longrightarrow> ((\<lambda>s. rval \<eta> (F s)) 
has_vector_derivative 0) (at r within {0--t})" using deriv by auto*)
ultimately have "\<forall>r\<in>{0--t}. ((\<lambda>s. rval \<eta> (F s)) 
has_vector_derivative 0) (at r within {0--t})" using obs2 by auto
from this and tcHyp have "\<forall>s\<in>{0..t}. ((\<lambda>x. rval \<eta> (F x)) has_derivative (\<lambda>x. x *\<^sub>R 0)) 
(at s within {0..t})" by (metis has_vector_derivative_def closed_segment_eq_real_ivl)
hence "rval \<eta> (F t) - rval \<eta> (F 0) = (\<lambda>x. x *\<^sub>R 0) (t - 0)" 
using mvt_very_simple and tcHyp by fastforce 
then show "rval \<eta> c = 0" using obs1 tcHyp by auto 
qed

theorem dInvForTrms:
assumes "\<forall> st. (\<forall> str \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>). st str = 0) \<longrightarrow>
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) st = 0"
and termVarsHyp:"trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and eta_f:"(\<lambda> s. f s) = (\<lambda> s. rval \<eta> s)"
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

lemma "PRE (\<lambda> s. (s ''s'') \<cdot> (s ''s'') + (s ''c'') \<cdot> (s ''c'') - (s ''r'') \<cdot> (s ''r'') = 0)  
      (ODEsystem [(''s'',(\<lambda> s. s ''c'')),(''c'',(\<lambda> s. - s ''s''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''s'') \<cdot> (s ''s'') + (s ''c'') \<cdot> (s ''c'') - (s ''r'') \<cdot> (s ''r'') = 0)"
apply(rule_tac \<eta>="Sum (Sum (Mult (Var ''s'') (Var ''s'')) (Mult (Var ''c'') (Var ''c'')))
(Mns (Mult (Var ''r'') (Var ''r'')))" and uInput="[Var ''c'', Mns (Var ''s'')]"in dInvForTrms)
by(simp_all add: varDiffs_def vdiff_def)

primrec propVars :: "props \<Rightarrow> string set" where
"propVars (Eq \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (Less \<theta> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (Neg \<phi>) = propVars \<phi>"|
"propVars (And \<phi> \<psi>) = propVars \<phi> \<union> propVars \<psi>"|
"propVars (Or \<phi> \<psi>) = propVars \<phi> \<union> propVars \<psi>"

primrec subspList :: "(string \<times> trms) list \<Rightarrow> props \<Rightarrow> props" where
"subspList xTrmList (Eq \<theta> \<eta>) = (Eq (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"subspList xTrmList (Less \<theta> \<eta>) = (Less (substList xTrmList \<theta>) (substList xTrmList \<eta>))"|
"subspList xTrmList (Neg \<phi>) = Neg (subspList xTrmList \<phi>)"|
"subspList xTrmList (And \<phi> \<psi>) = (And (subspList xTrmList \<phi>) (subspList xTrmList \<psi>))"|
"subspList xTrmList (Or \<phi> \<psi>) = (Or (subspList xTrmList \<phi>) (subspList xTrmList \<psi>))"

lemma diff_subst_prprty_4props:
assumes solves:"\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
and tHyp:"t \<ge> 0"
and rHyp:"r \<in> {0--t}"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
shows "pval (pdiff \<phi>) (F r) = 
pval (subspList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (pdiff \<phi>)) (F r)"
using propVarsHyp apply(induction \<phi>, simp_all)
using assms diff_subst_prprty_4terms apply fastforce
using assms diff_subst_prprty_4terms by fastforce

thm pval.simps
lemma dInv_prelim:
assumes substHyp:"\<forall> st. G st \<longrightarrow> 
pval (subspList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (pdiff \<phi>)) st"
and propVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
shows "(pval \<phi>) a \<longrightarrow> (\<forall> c. (a,c) \<in> (ODEsystem xfList with G) \<longrightarrow> (pval \<phi>) c)"
proof(clarify)
fix c assume aHyp:"pval \<phi> a" and cHyp:"(a, c) \<in> ODEsystem xfList with G"
from this obtain t::"real" and F::"real \<Rightarrow> real store" 
where tcHyp:"t\<ge>0 \<and> F t = c \<and> solvesStoreIVP F xfList a G" 
using guarDiffEqtn_def by auto
have "(\<forall>xf\<in>set xfList. F 0 (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F 0)) \<and> 
(\<forall>t\<ge>0. \<forall>r\<in>{0<--<t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r))"
using tcHyp solves_store_ivpD(3) solves_store_ivpD(6) by blast
then have *:"\<forall>t\<ge>0. \<forall>r\<in>{0--t}. \<forall> xf \<in> set xfList. F r (vdiff (\<pi>\<^sub>1 xf)) = \<pi>\<^sub>2 xf (F r)"
using solvesStoreIVP_couldBeModified2 by blast
from tcHyp and substHyp have "\<forall>r\<in>{0--t}. 
pval (subspList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (pdiff \<phi>)) (F r)" 
using solves_store_ivpD(2) using closed_segment_eq_real_ivl by fastforce 
from this aHyp and propVarsHyp show "pval \<phi> c"
proof(induction \<phi>)
case (Eq \<theta> \<eta>)
hence hyp:"pval (Eq \<theta> \<eta>) a \<and> propVars (Eq \<theta> \<eta>) \<subseteq> UNIV - varDiffs \<and> (\<forall>r\<in>{0--t}. 
pval (subspList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (pdiff (Eq \<theta> \<eta>))) (F r))" by blast
then have "trmVars \<theta> \<subseteq> UNIV - varDiffs \<and> trmVars \<eta> \<subseteq> UNIV - varDiffs" by simp
also have "\<forall>r\<in>{0--t}. rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<theta>)) (F r) = 
rval (substList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (rdiff \<eta>)) (F r)"
by (metis Eq.prems(1) pdiff.simps(1) pval.simps(1) subspList.simps(1))
ultimately have "\<forall>r\<in>{0--t}. rval (rdiff \<theta>) (F r) = rval (rdiff \<eta>) (F r)"
by (metis diff_subst_prprty_4terms * tcHyp listsHyp)
thm pdiff.simps
thm pval.simps
thm rval.simps
thm rdiff.simps
thm dInvForTrms
thm dInvForTrms_prelim
thm diff_subst_prprty_4terms
(* checar si ayuda: diff_subst_prprty_4props *)
hence "\<forall>r\<in>{0--t}. rval (Sum (rdiff \<theta>) (Mns (rdiff \<eta>))) (F r) = 0" by simp
from hyp have "rval (Sum \<theta> (Mns \<eta>)) a = 0" by simp
have "pval (Eq \<theta> \<eta>) c = (rval \<theta> (F t) = rval \<eta> (F t))" using tcHyp by simp
thus ?case using closed_segment_eq_real_ivl   sorry
next
case (Less \<theta> \<eta>)
then show ?case sorry
next
case (Neg \<phi>)
then show ?case sorry
next
case (And \<phi>1 \<phi>2)
then show ?case sorry
next
case (Or \<phi>1 \<phi>2)
then show ?case sorry
qed
qed

theorem dInv:
assumes "\<forall> st. (\<forall> str \<in> varDiffs - (vdiff\<lbrakk>\<pi>\<^sub>1\<lbrakk>set xfList\<rbrakk>\<rbrakk>). st str = 0) \<longrightarrow>
pval (subspList (cross_list (map (vdiff \<circ> \<pi>\<^sub>1) xfList) uInput) (pdiff \<phi>)) st"
and termVarsHyp:"propVars \<phi> \<subseteq> (UNIV - varDiffs)"
and listsHyp:"map \<pi>\<^sub>2 xfList = map rval uInput"
and phi_p:"P = pval \<phi>"
shows " PRE P (ODEsystem xfList with G) POST P"
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