section {* VC\_diffKAD *}
theory VC_diffKAD_auxiliarities
imports
Main
"afpModified/VC_KAD"
"Ordinary_Differential_Equations.IVP/Initial_Value_Problem"

begin

subsection{* VC\_KAD Preliminaries *}

text {* To make our notation less code-like and more mathematical we declare: *}
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
no_notation Archimedean_Field.floor ("\<lfloor>_\<rfloor>")
no_notation Set.image (" ` ")
no_notation Range_Semiring.antirange_semiring_class.ars_r ("r")

notation p2r ("\<lceil>_\<rceil>")
notation r2p ("\<lfloor>_\<rfloor>")
notation Set.image ("_\<lparr>_\<rparr>")
notation Product_Type.prod.fst ("\<pi>\<^sub>1")
notation Product_Type.prod.snd ("\<pi>\<^sub>2")
notation rel_ad ("\<Delta>\<^sup>c\<^sub>1")

text {* Their definitions are repeated below. *}
lemma "\<lceil>P\<rceil> = {(s, s) |s. P s}" by (simp add: p2r_def)
lemma "\<lfloor>R\<rfloor> = (\<lambda>x. x \<in> r2s R)" by (simp add: r2p_def) -- "where"
lemma "r2s R = {x |x. \<exists> y. (x,y) \<in> R}" by blast -- "Moreover"
lemma "\<pi>\<^sub>1 (x,y) = x \<and> \<pi>\<^sub>2 (x,y) = y" by simp
lemma "\<Delta>\<^sup>c\<^sub>1 R = {(x, x) |x. \<nexists>y. (x, y) \<in> R}" by (simp add: rel_ad_def)
lemma "wp R Q = \<Delta>\<^sup>c\<^sub>1 (R ; \<Delta>\<^sup>c\<^sub>1 Q)" by (simp add: rel_antidomain_kleene_algebra.fbox_def)

text {* Observe also, the following consequences and facts:*}
proposition "\<pi>\<^sub>1\<lparr>R\<rparr> = r2s R" 
by (simp add: fst_eq_Domain)

proposition "\<Delta>\<^sup>c\<^sub>1 R = Id - {(s, s) |s. s \<in> (\<pi>\<^sub>1\<lparr>R\<rparr>)}" 
by(simp add: image_def rel_ad_def, fastforce)

proposition "P \<subseteq> Q \<Longrightarrow> wp R P \<subseteq> wp R Q"
by(simp add: rel_antidomain_kleene_algebra.dka.dom_iso rel_antidomain_kleene_algebra.fbox_iso)

proposition boxProgrPred_IsProp: "wp R \<lceil>P\<rceil> \<subseteq> Id"
by(simp add: rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def)

proposition rdom_p2r_contents:"(a, b) \<in> rdom \<lceil>P\<rceil> = ((a = b) \<and> P a)" 
proof-
have "(a, b) \<in> rdom \<lceil>P\<rceil> = ((a = b) \<and> (a, a) \<in> rdom \<lceil>P\<rceil>)" using p2r_subid by fastforce 
also have "... = ((a = b) \<and> (a, a) \<in> \<lceil>P\<rceil>)" by simp
also have "... = ((a = b) \<and> P a)" by (simp add: p2r_def) 
ultimately show ?thesis by simp
qed

(* Should not add these "complement_rule's" to simp... *)
proposition rel_ad_rule1: "(x,x) \<notin> \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> \<Longrightarrow> P x"
by(auto simp: rel_ad_def p2r_subid p2r_def)

proposition rel_ad_rule2: "(x,x) \<in> \<Delta>\<^sup>c\<^sub>1 \<lceil>P\<rceil> \<Longrightarrow> \<not> P x"
by(metis ComplD VC_KAD.p2r_neg_hom rel_ad_rule1 empty_iff mem_Collect_eq p2s_neg_hom 
rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.am1 relcomp.relcompI)

proposition rel_ad_rule3: "R \<subseteq> Id \<Longrightarrow> (x,x) \<notin> R \<Longrightarrow> (x,x) \<in> \<Delta>\<^sup>c\<^sub>1 R"
by(metis IdI Un_iff d_p2r rel_antidomain_kleene_algebra.addual.ars3 
rel_antidomain_kleene_algebra.addual.ars_r_def rpr)

proposition rel_ad_rule4: "(x,x) \<in> R \<Longrightarrow> (x,x) \<notin> \<Delta>\<^sup>c\<^sub>1 R"
by(metis empty_iff rel_antidomain_kleene_algebra.addual.ars1 relcomp.relcompI)

proposition boxProgrPred_chrctrztn:"(x,x) \<in> wp R \<lceil>P\<rceil> = (\<forall> y. (x,y) \<in> R \<longrightarrow> P y)"
by(metis boxProgrPred_IsProp rel_ad_rule1 rel_ad_rule2 rel_ad_rule3 
rel_ad_rule4 d_p2r wp_simp wp_trafo)

proposition "P \<subseteq> Id \<Longrightarrow> (x,x) \<in> wp R P = (\<forall> y. (x,y) \<in> R \<longrightarrow> \<lfloor>P\<rfloor> y)"
by (metis boxProgrPred_chrctrztn rpr)

proposition "x \<in> r2s (wp R P) = (\<forall>y. (x, y) \<in> R \<longrightarrow> \<lfloor>P\<rfloor> y)"
by(simp add: r2p_def rel_antidomain_kleene_algebra.fbox_def rel_ad_def 
Domain_iff relcomp.simps)

subsection{* ODEs Preliminaries *}

text {* Once again, we repeat some definitions. *}
lemma "{a..b} = {x. a \<le> x \<and> x \<le> b}" by fastforce
lemma "{a<..<b} = {x. a < x \<and> x < b}" by fastforce
lemma "(x solves_ode f) {0..t} R = ((x has_vderiv_on (\<lambda>t. f t (x t))) {0..t} \<and> x \<in> {0..t} \<rightarrow> R)"
using solves_ode_def by simp
lemma "f \<in> A \<rightarrow> B = (f \<in> {f. \<forall> x. x \<in> A \<longrightarrow> (f x) \<in> B})" using Pi_def by auto
lemma "(f has_vderiv_on f'){0..t} = (\<forall>x\<in>{0..t}. (f has_vector_derivative f' x) (at x within {0..t}))"
using has_vderiv_on_def by simp
lemma "(f has_vector_derivative f') (at x within {0..t}) = 
(f has_derivative (\<lambda>x. x *\<^sub>R f')) (at x within {0..t})" using has_vector_derivative_def by auto

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

subsection{* VC\_diffKAD Preliminaries *}

text {* In dL, the set of possible program variables is split in two, the set of variables $V$ and 
their primed counterparts $V'$. To implement this, we use Isabelle's string-type and define a 
function that primes a given string. We then define the set of primed-strings based on it. *}

definition vdiff ::"string \<Rightarrow> string" ("\<partial> _" [55] 70) where
"(\<partial> x) = ''d[''@x@'']''" (* Alternatively, we could have use: "''d''@x@''/dt''" *)

definition varDiffs :: "string set" where
"varDiffs = {str. \<exists> x. str = \<partial> x}"

proposition vdiff_inj:"(\<partial> x) = (\<partial> y) \<Longrightarrow> x = y"
by(simp add: vdiff_def)

proposition vdiff_noFixPoints:"str \<noteq> (\<partial> str)"
by(simp add: vdiff_def)

lemma varDiffsI:"x = (\<partial> z) \<Longrightarrow> x \<in> varDiffs"
by(simp add: varDiffs_def vdiff_def)

lemma varDiffsE:
assumes "x \<in> varDiffs"
obtains y where "x = ''d[''@y@'']'' "
using assms unfolding varDiffs_def vdiff_def by auto

proposition vdiff_invarDiffs:"(\<partial> str) \<in> varDiffs"
by (simp add: varDiffsI)

subsubsection{* (primed) dSolve preliminaries *}

text {* The verification components check that a given external input solves
the problem at hand. This input is entered as a list. Thus, we introduce
a function to combine lists in a component-wise manner. *}
(* A "cartesian product" of lists. *)
fun cross_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" (infixl "\<otimes>" 63) where
"[] \<otimes> list = []"|
"list \<otimes> [] = []"|
"(x # xtail) \<otimes> (y # ytail) = (x,y) # (xtail \<otimes> ytail)"

-- "The following lines, test the behavior of our function with other more intuitive functions"
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

text{* "Next, we derive some properties of the cross\_list function."*}

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
assumes "\<forall> xzList. xzList = (map \<pi>\<^sub>1 xyList) \<otimes> zList" 
and "(y, z) \<in> set ((map \<pi>\<^sub>2 xyList) \<otimes> zList)" 
shows "(\<exists> x. (x,y) \<in> set xyList \<and> (x,z) \<in> set xzList)"
using assms by(induction xyList zList rule: cross_list.induct, auto)

lemma crossList_length:
"length xList = length yList \<Longrightarrow> length (xList \<otimes> yList) = length xList"
by(induction xList yList rule: cross_list.induct, simp_all)

lemma crossList_lengthEx:
"length xList = length yList \<Longrightarrow> 
\<forall> x \<in> set xList. \<exists> y \<in> set yList. (x,y) \<in> set (xList \<otimes> yList)"
apply(induction xList yList rule: cross_list.induct)
prefer 3 apply(rule ballI, simp, erule disjE, simp) subgoal by blast
by simp_all

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

text {* Now we need to define how to handle the given input in order to return a state at the 
end of a (differential) evolution. First, we say what the behavior of said state will be on
primed-strings. *}

abbreviation varDiffs_to_zero ::"real store \<Rightarrow> real store" ("d2z") where
"d2z a \<equiv> (override_on a (\<lambda> str. 0) varDiffs)" 

proposition varDiffs_to_zero_vdiff[simp]: "(d2z a) (\<partial> x) = 0"
apply(simp add: override_on_def varDiffs_def)
by auto

proposition varDiffs_to_zero_beginning[simp]: "take 2 x \<noteq> ''d['' \<Longrightarrow> (d2z a) x = a x"
apply(simp add: varDiffs_def override_on_def vdiff_def) 
by fastforce

-- "Next, for each entry of the input-list, we update the state using said entry."

definition "vderiv_of f S = (SOME f'. (f has_vderiv_on f') S)"

primrec state_list_upd :: "((real \<Rightarrow> real store \<Rightarrow> real) \<times> string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real \<Rightarrow> real store \<Rightarrow> real store" where
"state_list_upd [] t a  = a"|
"state_list_upd (uxf # tail) t a = (state_list_upd tail t a)
(     (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (\<pi>\<^sub>1 uxf) t a, 
    \<partial> (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (if t = 0 then (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) a
else vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r a) {0<..< (2 *\<^sub>R t)} t))"

abbreviation state_list_cross_upd ::"real store \<Rightarrow>  (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> (char list \<Rightarrow> real)" ("_[_\<leftarrow>_] _" [64,64,64] 63) where
"s[xfList\<leftarrow>uInput] t \<equiv> state_list_upd (uInput \<otimes> xfList) t s"

proposition state_list_cross_upd_empty[simp]: "(a[[]\<leftarrow>list] t) = a"
by(induction list, simp_all)

lemma inductive_state_list_cross_upd_its_vars:
assumes distHyp:"distinct (map \<pi>\<^sub>1 ((y, g) # xftail))"
and varHyp:"\<forall>xf\<in>set((y, g) # xftail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and indHyp:"(u, x, f) \<in> set (utail \<otimes> xftail) \<Longrightarrow> (a[xftail\<leftarrow>utail] t) x = u t a"
and disjHyp:"(u, x, f) = (v, y, g) \<or> (u, x, f) \<in> set (utail \<otimes> xftail)"
shows "(a[(y, g) # xftail\<leftarrow>v # utail] t) x = u t a"
using disjHyp proof
  assume "(u, x, f) = (v, y, g)"
  hence "(a[(y, g) # xftail\<leftarrow>v # utail] t) x = ((a[xftail\<leftarrow>utail] t)(x := u t a, 
  \<partial> x := if t = 0 then f a else vderiv_of (\<lambda> r. u r a) {0<..< (2 *\<^sub>R t)} t)) x" by simp
  also have "... = u t a" by (simp add: vdiff_def)
  ultimately show ?thesis by simp
next
  assume yTailHyp:"(u, x, f) \<in> set (utail \<otimes> xftail)"
  from this and indHyp have 3:"(a[xftail\<leftarrow>utail] t) x = u t a" by fastforce
  from yTailHyp and distHyp have 2:"y \<noteq> x" using non_empty_crossListElim by force 
  from yTailHyp and varHyp have 1:"x \<noteq> \<partial> y" 
  using non_empty_crossListElim vdiff_invarDiffs by fastforce 
  from 1 and 2 have "(a[(y, g) # xftail\<leftarrow>v # utail] t) x = (a[xftail\<leftarrow>utail] t) x"  by simp
  thus ?thesis using 3 by simp
qed

theorem state_list_cross_upd_its_vars:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and its_var: "(u,x,f) \<in> set (uInput \<otimes> xfList)"
shows "(a[xfList\<leftarrow>uInput] t) x = u t a"
using assms apply(induction xfList uInput rule: cross_list.induct, simp, simp)
apply(clarify, rule inductive_state_list_cross_upd_its_vars) by simp_all

lemma override_on_upd:"x \<in> X \<Longrightarrow> (override_on f g X)(x := z) = (override_on f (g(x := z)) X)"
by (rule ext, simp add: override_on_def)

lemma inductive_state_list_cross_upd_its_dvars:
assumes "\<exists>g. (a[xfTail\<leftarrow>uTail] 0) = override_on a g varDiffs"
and "\<forall>xf\<in>set (xf # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and "\<forall>uxf\<in>set (u # uTail \<otimes> xf # xfTail). \<pi>\<^sub>1 uxf 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists>g. (a[xf # xfTail\<leftarrow>u # uTail] 0) = override_on a g varDiffs"
proof-
let ?gLHS="(a[(xf # xfTail)\<leftarrow>(u # uTail)] 0)"
have observ:"\<partial> (\<pi>\<^sub>1 xf) \<in> varDiffs" by (auto simp: varDiffs_def)
from assms(1) obtain g where "(a[xfTail\<leftarrow>uTail] 0) = override_on a g varDiffs" by force
then have "?gLHS = (override_on a g varDiffs)(\<pi>\<^sub>1 xf := u 0 a, \<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" by simp
also have "\<dots> = (override_on a g varDiffs)(\<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)" 
using override_on_def varDiffs_def assms by auto 
also have "... = (override_on a (g(\<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf a)) varDiffs)" 
using observ and override_on_upd by force
ultimately show ?thesis by auto
qed

proposition state_list_cross_upd_its_dvars:
assumes lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp3:"\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 a = a (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists> g. (a[xfList\<leftarrow>uInput] 0) = (override_on a g varDiffs)"
using assms proof(induction xfList uInput rule: cross_list.induct)
case (1 list)
have "(a[[]\<leftarrow>list] 0) = override_on a a varDiffs"
unfolding override_on_def by simp
thus ?case by metis 
next
case (2 xf xfTail)
have "(a[(xf # xfTail)\<leftarrow>[]] 0) = override_on a a varDiffs" 
unfolding override_on_def by simp
thus ?case by metis 
next
case (3 xf xfTail u uTail)
then have "\<exists>g. (a[xfTail\<leftarrow>uTail] 0) = override_on a g varDiffs" by simp
thus ?case using inductive_state_list_cross_upd_its_dvars "3.prems" by blast
qed

--"Finally, we combine all previous transformations into one single expression."

abbreviation state_to_sol::"real store \<Rightarrow>  (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> (char list \<Rightarrow> real)" 
("sol _[_\<leftarrow>_] _" [64,64,64] 63) where "sol s[xfList\<leftarrow>uInput] t  \<equiv> d2z s[xfList\<leftarrow>uInput] t"


subsubsection{* dInv preliminaries *}

text {* Here, we introduce syntactic notation to talk about differential invariants. *}

no_notation Antidomain_Semiring.antidomain_left_monoid_class.am_add_op (infixl "\<oplus>" 65)
no_notation Dioid.times_class.opp_mult (infixl "\<odot>" 70)
no_notation Lattices.inf_class.inf (infixl "\<sqinter>" 70)
no_notation Lattices.sup_class.sup (infixl "\<squnion>" 65)

datatype trms = Const real ("t\<^sub>C _" [54] 70) | Var string ("t\<^sub>V _" [54] 70) | 
                Mns trms ("\<ominus> _" [54] 65) | Sum trms trms (infixl "\<oplus>" 65) | 
                Mult trms trms (infixl "\<odot>" 68)

primrec tval ::"trms \<Rightarrow> (real store \<Rightarrow> real)" ("\<lbrakk>_\<rbrakk>\<^sub>t" [55] 60) where
"\<lbrakk>t\<^sub>C r\<rbrakk>\<^sub>t = (\<lambda> s. r)"|
"\<lbrakk>t\<^sub>V x\<rbrakk>\<^sub>t = (\<lambda> s. s x)"|
"\<lbrakk>\<ominus> \<theta>\<rbrakk>\<^sub>t = (\<lambda> s. - (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<oplus> \<eta>\<rbrakk>\<^sub>t = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s + (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<odot> \<eta>\<rbrakk>\<^sub>t = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s \<cdot> (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"

datatype props = Eq trms trms (infixr "\<doteq>" 60) | Less trms trms (infixr "\<prec>" 62) | 
                 Leq trms trms (infixr "\<preceq>" 61) | And props props (infixl "\<sqinter>" 63) | 
                 Or props props (infixl "\<squnion>" 64)

primrec pval ::"props \<Rightarrow> (real store \<Rightarrow> bool)" ("\<lbrakk>_\<rbrakk>\<^sub>P" [55] 60) where
"\<lbrakk>\<theta> \<doteq> \<eta>\<rbrakk>\<^sub>P = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s = (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<prec> \<eta>\<rbrakk>\<^sub>P = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s < (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<preceq> \<eta>\<rbrakk>\<^sub>P = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s \<le> (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<phi> \<sqinter> \<psi>\<rbrakk>\<^sub>P = (\<lambda> s. (\<lbrakk>\<phi>\<rbrakk>\<^sub>P) s \<and> (\<lbrakk>\<psi>\<rbrakk>\<^sub>P) s)"|
"\<lbrakk>\<phi> \<squnion> \<psi>\<rbrakk>\<^sub>P = (\<lambda> s. (\<lbrakk>\<phi>\<rbrakk>\<^sub>P) s \<or> (\<lbrakk>\<psi>\<rbrakk>\<^sub>P) s)"

primrec tdiff ::"trms \<Rightarrow> trms" ("\<partial>\<^sub>t _" [54] 70) where
"(\<partial>\<^sub>t t\<^sub>C r) = t\<^sub>C 0"|
"(\<partial>\<^sub>t t\<^sub>V x) = t\<^sub>V (\<partial> x)"|
"(\<partial>\<^sub>t \<ominus> \<theta>) = \<ominus> (\<partial>\<^sub>t \<theta>)"|
"(\<partial>\<^sub>t (\<theta> \<oplus> \<eta>)) = (\<partial>\<^sub>t \<theta>) \<oplus> (\<partial>\<^sub>t \<eta>)"|
"(\<partial>\<^sub>t (\<theta> \<odot> \<eta>)) = ((\<partial>\<^sub>t \<theta>) \<odot> \<eta>) \<oplus> (\<theta> \<odot> (\<partial>\<^sub>t \<eta>))"

primrec pdiff ::"props \<Rightarrow> props" ("\<partial>\<^sub>P _" [54] 70) where
"(\<partial>\<^sub>P (\<theta> \<doteq> \<eta>)) = ((\<partial>\<^sub>t \<theta>) \<doteq> (\<partial>\<^sub>t \<eta>))"|
"(\<partial>\<^sub>P (\<theta> \<prec> \<eta>)) = ((\<partial>\<^sub>t \<theta>) \<preceq> (\<partial>\<^sub>t \<eta>))"|
"(\<partial>\<^sub>P (\<theta> \<preceq> \<eta>)) = ((\<partial>\<^sub>t \<theta>) \<preceq> (\<partial>\<^sub>t \<eta>))"|
"(\<partial>\<^sub>P (\<phi> \<sqinter> \<psi>)) = (\<partial>\<^sub>P \<phi>) \<sqinter> (\<partial>\<^sub>P \<psi>)"|
"(\<partial>\<^sub>P (\<phi> \<squnion> \<psi>)) = (\<partial>\<^sub>P \<phi>) \<sqinter> (\<partial>\<^sub>P \<psi>)"

primrec trmVars :: "trms \<Rightarrow> string set" where
"trmVars (t\<^sub>C r) = {}"|
"trmVars (t\<^sub>V x) = {x}"|
"trmVars (\<ominus> \<theta>) = trmVars \<theta>"|
"trmVars (\<theta> \<oplus> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"trmVars (\<theta> \<odot> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"

fun substList ::"(string \<times> trms) list \<Rightarrow> trms \<Rightarrow> trms" ("_\<langle>_\<rangle>" [54] 80) where
"xTrmList\<langle>t\<^sub>C r\<rangle> = t\<^sub>C r"|
"[]\<langle>t\<^sub>V x\<rangle> = t\<^sub>V x"|
"((y,\<xi>) # xTrmTail)\<langle>Var x\<rangle> = (if x = y then \<xi> else xTrmTail\<langle>Var x\<rangle>)"|
"xTrmList\<langle>\<ominus> \<theta>\<rangle> = \<ominus> (xTrmList\<langle>\<theta>\<rangle>)"|
"xTrmList\<langle>\<theta> \<oplus> \<eta>\<rangle> = (xTrmList\<langle>\<theta>\<rangle>) \<oplus> (xTrmList\<langle>\<eta>\<rangle>)"|
"xTrmList\<langle>\<theta> \<odot> \<eta>\<rangle> = (xTrmList\<langle>\<theta>\<rangle>) \<odot> (xTrmList\<langle>\<eta>\<rangle>)"

lemma substList_on_compl_of_varDiffs:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
assumes "set (map \<pi>\<^sub>1 xTrmList) \<subseteq> varDiffs"
shows "xTrmList\<langle>\<eta>\<rangle> = \<eta>"
using assms apply(induction \<eta>, simp_all add: varDiffs_def)
by(induction xTrmList, auto)

lemma substList_help1:"set (map \<pi>\<^sub>1 ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)) \<subseteq> varDiffs"
apply(induction xfList uInput rule: cross_list.induct, simp_all add: varDiffs_def)
by auto

lemma substList_help2:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<eta>\<rangle> = \<eta>"
using assms substList_help1 substList_on_compl_of_varDiffs by blast

lemma substList_cross_vdiff_on_non_ocurring_var:
assumes "x \<notin> set list1"
shows "((map vdiff list1) \<otimes> list2)\<langle>t\<^sub>V (\<partial> x)\<rangle> = t\<^sub>V (\<partial> x)"
using assms apply(induction list1 list2 rule: cross_list.induct, simp, simp, clarsimp)
by(simp add: vdiff_inj)

primrec propVars :: "props \<Rightarrow> string set" where
"propVars (\<theta> \<doteq> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<theta> \<prec> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<theta> \<preceq> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<phi> \<sqinter> \<psi>) = propVars \<phi> \<union> propVars \<psi>"|
"propVars (\<phi> \<squnion> \<psi>) = propVars \<phi> \<union> propVars \<psi>"

primrec subspList :: "(string \<times> trms) list \<Rightarrow> props \<Rightarrow> props" ("_\<restriction>_\<restriction>" [54] 80) where
"xTrmList\<restriction>\<theta> \<doteq> \<eta>\<restriction> = ((xTrmList\<langle>\<theta>\<rangle>) \<doteq> (xTrmList\<langle>\<eta>\<rangle>))"|
"xTrmList\<restriction>\<theta> \<prec> \<eta>\<restriction> = ((xTrmList\<langle>\<theta>\<rangle>) \<prec> (xTrmList\<langle>\<eta>\<rangle>))"|
"xTrmList\<restriction>\<theta> \<preceq> \<eta>\<restriction> = ((xTrmList\<langle>\<theta>\<rangle>) \<preceq> (xTrmList\<langle>\<eta>\<rangle>))"|
"xTrmList\<restriction>\<phi> \<sqinter> \<psi>\<restriction> = ((xTrmList\<restriction>\<phi>\<restriction>) \<sqinter> (xTrmList\<restriction>\<psi>\<restriction>))"|
"xTrmList\<restriction>\<phi> \<squnion> \<psi>\<restriction> = ((xTrmList\<restriction>\<phi>\<restriction>) \<squnion> (xTrmList\<restriction>\<psi>\<restriction>))"

end