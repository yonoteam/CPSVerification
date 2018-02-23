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

lemma storeIVP_def_couldBeModified:
assumes "\<forall> t \<ge> 0. \<forall> xf \<in> set xfList. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 xf) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 xf))) {0--t} UNIV"
assumes "\<forall> t \<ge> 0. \<forall> r \<in> {0<--<t}. \<forall> xf \<in> set xfList. (F r (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F r)"
shows "\<forall> xf \<in> set xfList. \<forall> r>0. ((\<lambda> t. F t (\<pi>\<^sub>1 xf)) has_vector_derivative 
(\<lambda> t. F t (vdiff (\<pi>\<^sub>1 xf))) r) (at r within {0<--<2 \<cdot> r})"
proof(clarify)
fix x f and r::real
assume "0 < r" then have rHyp:"0 < 2 \<cdot> r" by auto
assume xfHyp:"(x, f) \<in> set xfList" 
from this and assms(1) have "((\<lambda> t. F t (\<pi>\<^sub>1 (x, f))) solvesTheIVP (\<lambda> t. \<lambda> r. (\<pi>\<^sub>2 (x, f)) (F t)) 
withInitCond 0 \<mapsto> (st (\<pi>\<^sub>1 (x, f)))) {0--2 \<cdot> r} UNIV"  using less_eq_real_def rHyp by blast 
then have "((\<lambda> t. F t x) has_vderiv_on (\<lambda> t. f (F t))) {0--2 \<cdot> r}" 
by (simp add: solves_ode_def solves_ivp_def)
hence *:"\<forall> s \<in> {0--2 \<cdot> r}. ((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) s) 
(at s within {0--2 \<cdot> r})" by (simp add: has_vderiv_on_def rHyp real_Icc_closed_segment) 
have "{0<--<2\<cdot>r} \<subseteq> {0--2 \<cdot> r}" using open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
from this and * have dHyp:"\<forall> s \<in> {0<--<2\<cdot>r}. ((\<lambda> t. F t x) has_vector_derivative (\<lambda> t. f (F t)) s) 
(at s within {0<--<2\<cdot>r})" using Derivative.has_vector_derivative_within_subset by blast 
from rHyp have "\<forall> s \<in> {0<--<2 \<cdot> r}. \<forall> xf \<in> set xfList. (F s (vdiff (\<pi>\<^sub>1 xf))) = (\<pi>\<^sub>2 xf) (F s)"
using assms(2) less_eq_real_def by blast
then have "\<forall> s \<in> {0<--<2 \<cdot> r}. (F s (vdiff x)) = f (F s)" 
using xfHyp open_segment_eq_real_ivl by force
from this and dHyp show "((\<lambda>t. F t (\<pi>\<^sub>1 (x, f))) has_vector_derivative F r 
(vdiff (\<pi>\<^sub>1 (x, f)))) (at r within {0<--<2 \<cdot> r})"
using \<open>0 < r\<close> open_segment_eq_real_ivl by auto
qed
  
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
(* The rule "dSolve" requires an input from the user, i.e. the unique list of solutions to the 
system of ODE's, i.e. uInput::"(real \<Rightarrow> (real store) \<Rightarrow> real) list". This fact forces us to handle
several lists. For that reason, in this section we change the name "xfList" for "varFunList".
Moreover, we combine the user input with the list of variables in a single list "varSolList" to
compute the corresponding solution to the store-IVP. *)
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
thm derivative_eq_intros
thm continuous_intros

lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (ODEsystem [(''pos'',(\<lambda> s. s ''vel''))] with (\<lambda> s. True))
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
apply(rule_tac uInput="[\<lambda> t s. s ''vel'' \<cdot> t + s ''pos'']" in dSolve_toSolveUBC) (* 11 subgoals *)
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