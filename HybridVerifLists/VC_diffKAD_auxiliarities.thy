section {* VC\_diffKAD *}
theory VC_diffKAD_auxiliarities
imports
Main
"../afpModified/VC_KAD"
"Ordinary_Differential_Equations.ODE_Analysis"

begin

subsection{* Stack Theories Preliminaries: VC\_KAD and ODEs *}

text {* To make our notation less code-like and more mathematical we declare: *}
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
     and Archimedean_Field.floor ("\<lfloor>_\<rfloor>")
     and Set.image (" ` ")
     and Range_Semiring.antirange_semiring_class.ars_r ("r")

notation p2r ("\<lceil>_\<rceil>")
     and r2p ("\<lfloor>_\<rfloor>")
     and Set.image ("_\<lparr>_\<rparr>")
     and Product_Type.prod.fst ("\<pi>\<^sub>1")
     and Product_Type.prod.snd ("\<pi>\<^sub>2")
     and List.zip (infixl "\<otimes>" 63)
     and rel_ad ("\<Delta>\<^sup>c\<^sub>1")

text {* This and more notation is explained by the following lemmata. *}
lemma shows "\<lceil>P\<rceil> = {(s, s) |s. P s}"
    and "\<lfloor>R\<rfloor> = (\<lambda>x. x \<in> r2s R)"
    and "r2s R = {x |x. \<exists> y. (x,y) \<in> R}"
    and "\<pi>\<^sub>1 (x,y) = x \<and> \<pi>\<^sub>2 (x,y) = y"
    and "\<Delta>\<^sup>c\<^sub>1 R = {(x, x) |x. \<nexists>y. (x, y) \<in> R}"
    and "wp R Q = \<Delta>\<^sup>c\<^sub>1 (R ; \<Delta>\<^sup>c\<^sub>1 Q)"
    and "[x1,x2,x3,x4] \<otimes> [y1,y2] = [(x1,y1),(x2,y2)]"
    and "{a..b} = {x. a \<le> x \<and> x \<le> b}"
    and "{a<..<b} = {x. a < x \<and> x < b}"
    and "(x solves_ode f) {0..t} R = ((x has_vderiv_on (\<lambda>t. f t (x t))) {0..t} \<and> x \<in> {0..t} \<rightarrow> R)"
    and "f \<in> A \<rightarrow> B = (f \<in> {f. \<forall> x. x \<in> A \<longrightarrow> (f x) \<in> B})"
    and "(x has_vderiv_on x'){0..t} = 
      (\<forall>r\<in>{0..t}. (x has_vector_derivative x' r) (at r within {0..t}))"
    and "(x has_vector_derivative x' r) (at r within {0..t}) = 
      (x has_derivative (\<lambda>x. x *\<^sub>R x' r)) (at r within {0..t})"
apply(simp_all add: p2r_def r2p_def rel_ad_def rel_antidomain_kleene_algebra.fbox_def 
  solves_ode_def has_vderiv_on_def)
apply(blast, fastforce, fastforce)
using has_vector_derivative_def by auto

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

\<^cancel>\<open>..."Should not add these "complement_rule's" to simp..."\<close>
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

lemma (in antidomain_kleene_algebra) fbox_starI: 
assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
shows "d p \<le> |x\<^sup>\<star>] q"
proof-
from \<open>d i \<le> |x] i\<close> have "d i \<le> |x] (d i)"
  using local.fbox_simp by auto 
hence "|1] p \<le> |x\<^sup>\<star>] i" using \<open>d p \<le> d i\<close> by (metis (no_types) 
  local.dual_order.trans local.fbox_one local.fbox_simp local.fbox_star_induct_var)
thus ?thesis using \<open>d i \<le> d q\<close> by (metis (full_types)
  local.fbox_mult local.fbox_one local.fbox_seq_var local.fbox_simp)
qed

proposition cons_eq_zipE:
"(x, y) # tail = xList \<otimes> yList \<Longrightarrow> \<exists>xTail yTail. x # xTail = xList \<and> y # yTail = yList"
by(induction xList, simp_all, induction yList, simp_all)

proposition set_zip_left_rightD:
"(x, y) \<in> set (xList \<otimes> yList) \<Longrightarrow> x \<in> set xList \<and> y \<in> set yList"
apply(rule conjI)
apply(rule_tac y="y" and ys="yList" in set_zip_leftD, simp)
apply(rule_tac x="x" and xs="xList" in set_zip_rightD, simp)
done

declare zip_map_fst_snd [simp]

subsection{* VC\_diffKAD Preliminaries *}

text {* In dL, the set of possible program variables is split in two, the set of variables $V$ and 
their primed counterparts $V'$. To implement this, we use Isabelle's string-type and define a 
function that primes a given string. We then define the set of primed-strings based on it. *}

definition vdiff ::"string \<Rightarrow> string" ("\<partial> _" [55] 70) where
"(\<partial> x) = ''d[''@x@'']''" (* Alternatively, we could have use: "''d''@x@''/dt''" *)

definition varDiffs :: "string set" where
"varDiffs = {y. \<exists> x. y = \<partial> x}"

proposition vdiff_inj:"(\<partial> x) = (\<partial> y) \<Longrightarrow> x = y"
by(simp add: vdiff_def)

proposition vdiff_noFixPoints:"x \<noteq> (\<partial> x)"
by(simp add: vdiff_def)

lemma varDiffsI:"x = (\<partial> z) \<Longrightarrow> x \<in> varDiffs"
by(simp add: varDiffs_def vdiff_def)

lemma varDiffsE:
assumes "x \<in> varDiffs"
obtains y where "x = ''d[''@y@'']'' "
using assms unfolding varDiffs_def vdiff_def by auto

proposition vdiff_invarDiffs:"(\<partial> x) \<in> varDiffs"
by (simp add: varDiffsI)

subsubsection{* (primed) dSolve preliminaries *}

text {* This subsubsection is to define a function that takes a system of ODEs (expressed 
as a list $xfList$), a presumed solution $uInput = [u_1,\dots,u_n]$, a state $s$ and a 
time $t$, and outputs the induced flow $sol\, s[xfList\leftarrow uInput]\, t$. *}

abbreviation varDiffs_to_zero ::"real store \<Rightarrow> real store" ("sol") where
"sol a \<equiv> (override_on a (\<lambda> x. 0) varDiffs)" 

proposition varDiffs_to_zero_vdiff[simp]: "(sol s) (\<partial> x) = 0"
apply(simp add: override_on_def varDiffs_def)
by auto

proposition varDiffs_to_zero_beginning[simp]: "take 2 x \<noteq> ''d['' \<Longrightarrow> (sol s) x = s x"
apply(simp add: varDiffs_def override_on_def vdiff_def) 
by fastforce

\<comment> \<open>Next, for each entry of the input-list, we update the state using said entry.\<close>

definition "vderiv_of f S = (SOME f'. (f has_vderiv_on f') S)"

primrec state_list_upd :: "((real \<Rightarrow> real store \<Rightarrow> real) \<times> string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
real \<Rightarrow> real store \<Rightarrow> real store" where
"state_list_upd [] t s  = s"|
"state_list_upd (uxf # tail) t s = (state_list_upd tail t s)
(     (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (\<pi>\<^sub>1 uxf) t s, 
    \<partial> (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf)) := (if t = 0 then (\<pi>\<^sub>2 (\<pi>\<^sub>2 uxf)) s
else vderiv_of (\<lambda> r. (\<pi>\<^sub>1 uxf) r s) {0<..< (2 *\<^sub>R t)} t))"

abbreviation state_list_cross_upd ::"real store \<Rightarrow>  (string \<times> (real store \<Rightarrow> real)) list \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real) list \<Rightarrow> real \<Rightarrow> (char list \<Rightarrow> real)" ("_[_\<leftarrow>_] _" [64,64,64] 63) where
"s[xfList\<leftarrow>uInput] t \<equiv> state_list_upd (uInput \<otimes> xfList) t s"

proposition state_list_cross_upd_empty[simp]: "(s[[]\<leftarrow>list] t) = s"
by(induction list, simp_all)

lemma inductive_state_list_cross_upd_its_vars:
assumes distHyp:"distinct (map \<pi>\<^sub>1 ((y, g) # xftail))"
and varHyp:"\<forall>xf\<in>set((y, g) # xftail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and indHyp:"(u, x, f) \<in> set (utail \<otimes> xftail) \<Longrightarrow> (s[xftail\<leftarrow>utail] t) x = u t s"
and disjHyp:"(u, x, f) = (v, y, g) \<or> (u, x, f) \<in> set (utail \<otimes> xftail)"
shows "(s[(y, g) # xftail\<leftarrow>v # utail] t) x = u t s"
using disjHyp proof
  assume "(u, x, f) = (v, y, g)"
  hence "(s[(y, g) # xftail\<leftarrow>v # utail] t) x = ((s[xftail\<leftarrow>utail] t)(x := u t s, 
  \<partial> x := if t = 0 then f s else vderiv_of (\<lambda> r. u r s) {0<..< (2 *\<^sub>R t)} t)) x" by simp
  also have "... = u t s" by (simp add: vdiff_def)
  ultimately show ?thesis by simp
next
  assume yTailHyp:"(u, x, f) \<in> set (utail \<otimes> xftail)"
  from this and indHyp have 3:"(s[xftail\<leftarrow>utail] t) x = u t s" by fastforce
  from yTailHyp and distHyp have 2:"y \<noteq> x" using set_zip_left_rightD by force 
  from yTailHyp and varHyp have 1:"x \<noteq> \<partial> y" 
  using set_zip_left_rightD vdiff_invarDiffs by fastforce 
  from 1 and 2 have "(s[(y, g) # xftail\<leftarrow>v # utail] t) x = (s[xftail\<leftarrow>utail] t) x"  by simp
  thus ?thesis using 3 by simp
qed

theorem state_list_cross_upd_its_vars:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and its_var: "(u,x,f) \<in> set (uInput \<otimes> xfList)"
shows "(s[xfList\<leftarrow>uInput] t) x = u t s"
using assms apply(induct xfList uInput arbitrary: x rule: list_induct2', simp, simp, simp)
by(clarify, rule inductive_state_list_cross_upd_its_vars, simp_all)

lemma override_on_upd:"x \<in> X \<Longrightarrow> (override_on f g X)(x := z) = (override_on f (g(x := z)) X)"
by (rule ext, simp add: override_on_def)

lemma inductive_state_list_cross_upd_its_dvars:
assumes "\<exists>g. (s[xfTail\<leftarrow>uTail] 0) = override_on s g varDiffs"
and "\<forall>xf\<in>set (xf # xfTail). \<pi>\<^sub>1 xf \<notin> varDiffs"
and "\<forall>uxf\<in>set (u # uTail \<otimes> xf # xfTail). \<pi>\<^sub>1 uxf 0 s = s (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists>g. (s[xf # xfTail\<leftarrow>u # uTail] 0) = override_on s g varDiffs"
proof-
let ?gLHS="(s[(xf # xfTail)\<leftarrow>(u # uTail)] 0)"
have observ:"\<partial> (\<pi>\<^sub>1 xf) \<in> varDiffs" by (auto simp: varDiffs_def)
from assms(1) obtain g where "(s[xfTail\<leftarrow>uTail] 0) = override_on s g varDiffs" by force
then have "?gLHS = (override_on s g varDiffs)(\<pi>\<^sub>1 xf := u 0 s, \<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf s)" by simp
also have "\<dots> = (override_on s g varDiffs)(\<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf s)" 
using override_on_def varDiffs_def assms by auto 
also have "... = (override_on s (g(\<partial> (\<pi>\<^sub>1 xf) := \<pi>\<^sub>2 xf s)) varDiffs)" 
using observ and override_on_upd by force
ultimately show ?thesis by auto
qed

theorem state_list_cross_upd_its_dvars:
assumes lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall>uxf\<in>set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 s = s (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
shows "\<exists> g. (s[xfList\<leftarrow>uInput] 0) = (override_on s g varDiffs)"
using assms proof(induct xfList uInput rule: list_induct2')
case 1
  have "(s[[]\<leftarrow>[]] 0) = override_on s s varDiffs"
  unfolding override_on_def by simp
  thus ?case by metis
next
  case (2 xf xfTail)
  have "(s[(xf # xfTail)\<leftarrow>[]] 0) = override_on s s varDiffs" 
  unfolding override_on_def by simp
  thus ?case by metis 
next
  case (3 u utail)
  have "(s[[]\<leftarrow>utail] 0) = override_on s s varDiffs"
  unfolding override_on_def by simp
  thus ?case by force
next
  case (4 xf xfTail u uTail)
  then have "\<exists>g. (s[xfTail\<leftarrow>uTail] 0) = override_on s g varDiffs" by simp
  thus ?case using inductive_state_list_cross_upd_its_dvars "4.prems" by blast
qed

lemma vderiv_unique_within_open_interval:
assumes "(f has_vderiv_on f') {0<..< t}" and "t>0"
    and "(f has_vderiv_on f''){0<..< t}" and tauHyp:"\<tau> \<in> {0<..< t}"
shows "f' \<tau> = f'' \<tau>"
using assms apply(simp add: has_vderiv_on_def has_vector_derivative_def)
using frechet_derivative_unique_within_open_interval by (metis box_real(1) scaleR_one tauHyp)

lemma has_vderiv_on_cong_open_interval:
assumes gHyp:"\<forall> \<tau> > 0. f \<tau> = g \<tau>" and tHyp: "t>0"
and fHyp:"(f has_vderiv_on f') {0<..<t}" 
shows "(g has_vderiv_on f') {0<..<t}"
proof-
from gHyp have "\<And>\<tau>. \<tau> \<in> {0<..< t} \<Longrightarrow> f \<tau> = g \<tau>" using tHyp by force
hence eqDs:"(f has_vderiv_on f') {0<..<t} = (g has_vderiv_on f') {0<..<t}"
apply(rule_tac has_vderiv_on_cong) by auto
thus "(g has_vderiv_on f') {0<..<t}" using eqDs fHyp by simp
qed

lemma closed_vderiv_on_cong_to_open_vderiv:
assumes gHyp:"\<forall> \<tau> > 0. f \<tau> = g \<tau>" 
and fHyp:"\<forall>t\<ge>0. (f has_vderiv_on f') {0..t}" 
and tHyp: "t>0" and cHyp: "c > 1"
shows "vderiv_of g {0<..< (c *\<^sub>R t)} t = f' t"
proof-
have ctHyp:"c \<cdot> t > 0" using tHyp and cHyp by auto
from fHyp have "(f has_vderiv_on f') {0<..<c \<cdot> t}" using has_vderiv_on_subset 
by (metis greaterThanLessThan_subseteq_atLeastAtMost_iff less_eq_real_def)
then have derivHyp:"(g has_vderiv_on f') {0<..<c \<cdot> t}" 
using gHyp ctHyp and has_vderiv_on_cong_open_interval by blast
hence f'Hyp:"\<forall> f''. (g has_vderiv_on f'') {0<..<c \<cdot> t} \<longrightarrow> (\<forall> \<tau> \<in> {0<..< c \<cdot> t}. f' \<tau> = f'' \<tau>)"
using vderiv_unique_within_open_interval ctHyp by blast 
also have "(g has_vderiv_on (vderiv_of g {0<..< (c *\<^sub>R t)})) {0<..<c \<cdot> t}"
by(simp add: vderiv_of_def, metis derivHyp someI_ex)
ultimately show"vderiv_of g {0<..<c *\<^sub>R t} t = f' t" using tHyp cHyp by force
qed

lemma vderiv_of_to_sol_its_vars:
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall> xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp2:"\<forall>t\<ge>0. ((\<lambda>\<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>) x) 
has_vderiv_on (\<lambda>\<tau>. f (sol s[xfList\<leftarrow>uInput] \<tau>))) {0..t}" 
and tHyp: "t>0" and uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)"
shows "vderiv_of (\<lambda>\<tau>. u \<tau> (sol s)) {0<..< (2 *\<^sub>R t)} t = f (sol s[xfList\<leftarrow>uInput] t)"
apply(rule_tac f="(\<lambda>\<tau>. (sol s[xfList\<leftarrow>uInput] \<tau>) x)" in closed_vderiv_on_cong_to_open_vderiv)
subgoal using assms and state_list_cross_upd_its_vars by metis
by(simp_all add: solHyp2 tHyp)

lemma inductive_to_sol_zero_its_dvars:
assumes eqFuncs:"\<forall> s. \<forall>g. \<forall>xf\<in>set ((x, f) # xfs). \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s"
and eqLengths:"length ((x, f) # xfs) = length (u # us)"
and distinct:"distinct (map \<pi>\<^sub>1 ((x, f) # xfs))"
and vars:"\<forall>xf\<in>set ((x, f) # xfs). \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall>uxf\<in>set ((u # us) \<otimes> ((x, f) # xfs)). \<pi>\<^sub>1 uxf 0 (sol s) = sol s (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and disjHyp:"(y, g) = (x, f) \<or> (y, g) \<in> set xfs"
and indHyp:"(y, g) \<in> set xfs \<Longrightarrow> (sol s[xfs\<leftarrow>us] 0) (\<partial> y) = g (sol s[xfs\<leftarrow>us] 0)"
shows "(sol s[(x, f) # xfs\<leftarrow>u # us] 0) (\<partial> y) = g (sol s[(x, f) # xfs\<leftarrow>u # us] 0)"
proof-
from assms obtain h1 where h1Def:"(sol s[((x, f) # xfs)\<leftarrow>(u # us)] 0) = 
(override_on (sol s) h1 varDiffs)" using state_list_cross_upd_its_dvars by blast 
from disjHyp show "(sol s[(x, f) # xfs\<leftarrow>u # us] 0) (\<partial> y) = g (sol s[(x, f) # xfs\<leftarrow>u # us] 0)"
proof
  assume eqHeads:"(y, g) = (x, f)"
  then have "g (sol s[(x, f) # xfs\<leftarrow>u # us] 0) = f (sol s)" using h1Def eqFuncs by simp
  also have "... = (sol s[(x, f) # xfs\<leftarrow>u # us] 0) (\<partial> y)" using eqHeads by auto
  ultimately show ?thesis by linarith
next
  assume tailHyp:"(y, g) \<in> set xfs"
  then have "y \<noteq> x" using distinct set_zip_left_rightD by force
  hence "\<partial> x \<noteq> \<partial> y" by(simp add: vdiff_def)
  have "x \<noteq> \<partial> y" using vars vdiff_invarDiffs by auto 
  obtain h2 where h2Def:"(sol s[xfs\<leftarrow>us] 0) = override_on (sol s) h2 varDiffs" 
  using state_list_cross_upd_its_dvars eqLengths distinct vars and solHyp1 by force
  have "(sol s[(x, f) # xfs\<leftarrow>u # us] 0) (\<partial> y) = g (sol s[xfs\<leftarrow>us] 0)" 
  using tailHyp indHyp \<open>x \<noteq> \<partial> y\<close> and \<open>\<partial> x \<noteq> \<partial> y\<close> by simp
  also have "... = g (override_on (sol s) h2 varDiffs)" using h2Def by simp
  also have "... = g (sol s)" using eqFuncs and tailHyp by force
  also have "... = g (sol s[(x, f) # xfs\<leftarrow>u # us] 0)" 
  using eqFuncs h1Def tailHyp and eq_snd_iff by fastforce
  ultimately show ?thesis by simp
  qed
qed

lemma to_sol_zero_its_dvars:
assumes funcsHyp:"\<forall> s. \<forall> g. \<forall> xf \<in> set xfList. \<pi>\<^sub>2 xf (override_on s g varDiffs) = \<pi>\<^sub>2 xf s" 
and distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall>xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and solHyp1:"\<forall> uxf \<in> set (uInput \<otimes> xfList). (\<pi>\<^sub>1 uxf) 0 (sol s) = (sol s) (\<pi>\<^sub>1 (\<pi>\<^sub>2 uxf))"
and ygHyp:"(y, g) \<in> set xfList"
shows "(sol s[xfList\<leftarrow>uInput] 0)(\<partial> y) = g (sol s[xfList\<leftarrow>uInput] 0)"
using assms apply(induct xfList uInput rule: list_induct2', simp, simp, simp, clarify)
by(rule inductive_to_sol_zero_its_dvars, simp_all)

lemma inductive_to_sol_greater_than_zero_its_dvars:
assumes lengthHyp:"length ((y, g) # xfs) = length (v # vs)"
and distHyp:"distinct (map \<pi>\<^sub>1 ((y, g) # xfs))"
and varHyp:" \<forall>xf\<in>set ((y, g) # xfs). \<pi>\<^sub>1 xf \<notin> varDiffs"
and indHyp:"(u,x,f) \<in> set (vs \<otimes> xfs) \<Longrightarrow> (s[xfs\<leftarrow>vs]t)(\<partial> x) = vderiv_of (\<lambda>r. u r s) {0<..<2*\<^sub>Rt} t"
and disjHyp:"(v, y, g) = (u, x, f) \<or> (u, x, f) \<in> set (vs \<otimes> xfs)" and tHyp:"t > 0"
shows "(s[(y, g) # xfs\<leftarrow>v # vs] t) (\<partial> x) = vderiv_of (\<lambda>r. u r s) {0<..<2 *\<^sub>R t} t"
proof-
let ?lhs = "((s[xfs\<leftarrow>vs] t)(y := v t s, \<partial> y := vderiv_of (\<lambda> r. v r s) {0<..< (2 \<cdot> t)} t)) (\<partial> x)"
let ?rhs = "vderiv_of (\<lambda>r. u r s) {0<..< (2 \<cdot> t)} t"
have "(s[(y, g) # xfs\<leftarrow>v # vs] t) (\<partial> x) = ?lhs" using tHyp by simp
also have "vderiv_of (\<lambda>r. u r s) {0<..<2 *\<^sub>R t} t =?rhs" by simp
ultimately have obs:"?thesis = (?lhs = ?rhs)" by simp
from disjHyp have "?lhs = ?rhs" 
proof
  assume uxfEq:"(v, y, g) = (u, x, f)"
  then have "?lhs = vderiv_of (\<lambda> r. u r s) {0<..< (2 \<cdot> t)} t" by simp
  also have "vderiv_of (\<lambda> r. u r s) {0<..< (2 \<cdot> t)} t = ?rhs" using uxfEq by simp
  ultimately show "?lhs = ?rhs" by simp
next
  assume sygTail:"(u, x, f) \<in> set (vs \<otimes> xfs)"
  from this have "y \<noteq> x" using distHyp set_zip_left_rightD by force 
  hence "\<partial> x \<noteq> \<partial> y" by(simp add: vdiff_def)
  have "y \<noteq> \<partial> x" using varHyp using vdiff_invarDiffs by auto 
  then have "?lhs = (s[xfs\<leftarrow>vs] t) (\<partial> x)" using \<open>y \<noteq> \<partial> x\<close> and \<open>\<partial> x \<noteq> \<partial> y\<close> by simp
  also have "(s[xfs\<leftarrow>vs] t) (\<partial> x) = ?rhs" using indHyp sygTail by simp
  ultimately show "?lhs = ?rhs" by simp
qed
from this and obs show ?thesis by simp
qed

lemma to_sol_greater_than_zero_its_dvars: 
assumes distinctHyp:"distinct (map \<pi>\<^sub>1 xfList)" 
and lengthHyp:"length xfList = length uInput"
and varsHyp:"\<forall>xf \<in> set xfList. \<pi>\<^sub>1 xf \<notin> varDiffs"
and uxfHyp:"(u, x, f) \<in> set (uInput \<otimes> xfList)" and tHyp:"t > 0"
shows "(s[xfList\<leftarrow>uInput] t) (\<partial> x) = vderiv_of (\<lambda> r. u r s) {0<..< (2 *\<^sub>R t)} t"
using assms apply(induct xfList uInput rule: list_induct2', simp, simp, simp, clarify)
by(rule_tac f="f" in inductive_to_sol_greater_than_zero_its_dvars, auto)

subsubsection{* dInv preliminaries *}

text {* Here, we introduce syntactic notation to talk about differential invariants. *}

no_notation Antidomain_Semiring.antidomain_left_monoid_class.am_add_op (infixl "\<oplus>" 65)
no_notation Dioid.times_class.opp_mult (infixl "\<odot>" 70)
no_notation Lattices.inf_class.inf (infixl "\<sqinter>" 70)
no_notation Lattices.sup_class.sup (infixl "\<squnion>" 65)

datatype trms = Const real ("t\<^sub>C _" [54] 70) | Var string ("t\<^sub>V _" [54] 70) | 
                Mns trms ("\<ominus> _" [54] 65) | Sum trms trms (infixl "\<oplus>" 65) | 
                Mult trms trms (infixl "\<odot>" 68)

primrec tval ::"trms \<Rightarrow> (real store \<Rightarrow> real)" ("(1\<lbrakk> _ \<rbrakk>\<^sub>t)") where
"\<lbrakk>t\<^sub>C r\<rbrakk>\<^sub>t = (\<lambda> s. r)"|
"\<lbrakk>t\<^sub>V x\<rbrakk>\<^sub>t = (\<lambda> s. s x)"|
"\<lbrakk>\<ominus> \<theta>\<rbrakk>\<^sub>t = (\<lambda> s. - (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<oplus> \<eta>\<rbrakk>\<^sub>t = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s + (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"|
"\<lbrakk>\<theta> \<odot> \<eta>\<rbrakk>\<^sub>t = (\<lambda> s. (\<lbrakk>\<theta>\<rbrakk>\<^sub>t) s \<cdot> (\<lbrakk>\<eta>\<rbrakk>\<^sub>t) s)"

datatype props = Eq trms trms (infixr "\<doteq>" 60) | Less trms trms (infixr "\<prec>" 62) | 
                 Leq trms trms (infixr "\<preceq>" 61) | And props props (infixl "\<sqinter>" 63) | 
                 Or props props (infixl "\<squnion>" 64)

primrec pval ::"props \<Rightarrow> (real store \<Rightarrow> bool)" ("(1\<lbrakk>_\<rbrakk>\<^sub>P)") where
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
"xtList\<langle>t\<^sub>C r\<rangle> = t\<^sub>C r"|
"[]\<langle>t\<^sub>V x\<rangle> = t\<^sub>V x"|
"((y,\<xi>) # xtTail)\<langle>Var x\<rangle> = (if x = y then \<xi> else xtTail\<langle>Var x\<rangle>)"|
"xtList\<langle>\<ominus> \<theta>\<rangle> = \<ominus> (xtList\<langle>\<theta>\<rangle>)"|
"xtList\<langle>\<theta> \<oplus> \<eta>\<rangle> = (xtList\<langle>\<theta>\<rangle>) \<oplus> (xtList\<langle>\<eta>\<rangle>)"|
"xtList\<langle>\<theta> \<odot> \<eta>\<rangle> = (xtList\<langle>\<theta>\<rangle>) \<odot> (xtList\<langle>\<eta>\<rangle>)"

proposition substList_on_compl_of_varDiffs:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
and "set (map \<pi>\<^sub>1 xtList) \<subseteq> varDiffs"
shows "xtList\<langle>\<eta>\<rangle> = \<eta>"
using assms apply(induction \<eta>, simp_all add: varDiffs_def)
by(induction xtList, auto)

lemma substList_help1:"set (map \<pi>\<^sub>1 ((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)) \<subseteq> varDiffs"
apply(induct xfList uInput rule: list_induct2', simp_all add: varDiffs_def)
by auto

lemma substList_help2:
assumes "trmVars \<eta> \<subseteq> (UNIV - varDiffs)"
shows "((map (vdiff \<circ> \<pi>\<^sub>1) xfList) \<otimes> uInput)\<langle>\<eta>\<rangle> = \<eta>"
using assms substList_help1 substList_on_compl_of_varDiffs by blast

lemma substList_cross_vdiff_on_non_ocurring_var:
assumes "x \<notin> set list1"
shows "((map vdiff list1) \<otimes> list2)\<langle>t\<^sub>V (\<partial> x)\<rangle> = t\<^sub>V (\<partial> x)"
using assms apply(induct list1 list2 rule: list_induct2', simp, simp, clarsimp)
by(simp add: vdiff_def)

primrec propVars :: "props \<Rightarrow> string set" where
"propVars (\<theta> \<doteq> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<theta> \<prec> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<theta> \<preceq> \<eta>) = trmVars \<theta> \<union> trmVars \<eta>"|
"propVars (\<phi> \<sqinter> \<psi>) = propVars \<phi> \<union> propVars \<psi>"|
"propVars (\<phi> \<squnion> \<psi>) = propVars \<phi> \<union> propVars \<psi>"

primrec subspList :: "(string \<times> trms) list \<Rightarrow> props \<Rightarrow> props" ("_\<restriction>_\<restriction>" [54] 80) where
"xtList\<restriction>\<theta> \<doteq> \<eta>\<restriction> = ((xtList\<langle>\<theta>\<rangle>) \<doteq> (xtList\<langle>\<eta>\<rangle>))"|
"xtList\<restriction>\<theta> \<prec> \<eta>\<restriction> = ((xtList\<langle>\<theta>\<rangle>) \<prec> (xtList\<langle>\<eta>\<rangle>))"|
"xtList\<restriction>\<theta> \<preceq> \<eta>\<restriction> = ((xtList\<langle>\<theta>\<rangle>) \<preceq> (xtList\<langle>\<eta>\<rangle>))"|
"xtList\<restriction>\<phi> \<sqinter> \<psi>\<restriction> = ((xtList\<restriction>\<phi>\<restriction>) \<sqinter> (xtList\<restriction>\<psi>\<restriction>))"|
"xtList\<restriction>\<phi> \<squnion> \<psi>\<restriction> = ((xtList\<restriction>\<phi>\<restriction>) \<squnion> (xtList\<restriction>\<psi>\<restriction>))"

subsubsection{* ODE Extras *}

text{* For exemplification purposes, we compile some concrete derivatives used commonly in classical
mechanics. A more general approach should be taken that generates this theorems as instantiations. *}

named_theorems ubc_definitions "definitions used in the locale unique_on_bounded_closed"

declare unique_on_bounded_closed_def [ubc_definitions]
    and unique_on_bounded_closed_axioms_def [ubc_definitions]
    and unique_on_closed_def [ubc_definitions]
    and compact_interval_def [ubc_definitions]
    and compact_interval_axioms_def [ubc_definitions]
    and self_mapping_def [ubc_definitions]
    and self_mapping_axioms_def [ubc_definitions]
    and continuous_rhs_def [ubc_definitions]
    and closed_domain_def [ubc_definitions]
    and global_lipschitz_def [ubc_definitions]
    and interval_def [ubc_definitions]
    and nonempty_set_def [ubc_definitions]
    and lipschitz_on_def [ubc_definitions]

named_theorems poly_deriv "temporal compilation of derivatives representing galilean transformations"
named_theorems galilean_transform "temporal compilation of vderivs representing galilean transformations"
named_theorems galilean_transform_eq "the equational version of galilean-transform"

lemma vector_derivative_line_at_origin:"((\<cdot>) a has_vector_derivative a) (at x within T)"
by (auto intro: derivative_eq_intros)

lemma [poly_deriv]:"((\<cdot>) a has_derivative (\<lambda>x. x *\<^sub>R a)) (at x within T)"
using vector_derivative_line_at_origin unfolding has_vector_derivative_def by simp

lemma quadratic_monomial_derivative:
"((\<lambda>t::real. a \<cdot> t\<^sup>2) has_derivative (\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t))) (at x within T)"
apply(rule_tac g'1="\<lambda> t. 2 \<cdot> x \<cdot> t" in derivative_eq_intros(6))
apply(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15))
by (auto intro: derivative_eq_intros) 

lemma quadratic_monomial_derivative2:
"((\<lambda>t::real. a \<cdot> t\<^sup>2 / 2) has_derivative (\<lambda>t. a \<cdot> x \<cdot> t)) (at x within T)"
apply(rule_tac f'1="\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t)" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
using quadratic_monomial_derivative by auto

lemma quadratic_monomial_vderiv[poly_deriv]:"((\<lambda>t. a \<cdot> t\<^sup>2 / 2) has_vderiv_on (\<cdot>) a) T"
apply(simp add: has_vderiv_on_def has_vector_derivative_def, clarify)
using quadratic_monomial_derivative2 by (simp add: mult_commute_abs)

lemma galilean_position[galilean_transform]:
"((\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) has_vderiv_on (\<lambda>t. a \<cdot> t + v)) T"
apply(rule_tac f'="\<lambda> x. a \<cdot> x + v" and g'1="\<lambda> x. 0" in derivative_intros(190))
apply(rule_tac f'1="\<lambda> x. a \<cdot> x" and g'1="\<lambda> x. v" in derivative_intros(190))
using poly_deriv(2) by(auto intro: derivative_intros)

lemma [poly_deriv]:
"t \<in> T \<Longrightarrow> ((\<lambda>\<tau>. a \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + x) has_derivative (\<lambda>x. x *\<^sub>R (a \<cdot> t + v))) (at t within T)"
using galilean_position unfolding has_vderiv_on_def has_vector_derivative_def by simp

lemma [galilean_transform_eq]:
"t > 0 \<Longrightarrow> vderiv_of (\<lambda>t. a \<cdot> t^2 / 2 + v \<cdot> t + x) {0<..<2 \<cdot> t} t = a \<cdot> t + v"
proof-
let ?f = "vderiv_of (\<lambda>t. a \<cdot> t^2 / 2 + v \<cdot> t + x) {0<..<2 \<cdot> t}" 
assume "t > 0" hence "t \<in> {0<..<2 \<cdot> t}" by auto
have "\<exists> f. ((\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) has_vderiv_on f) {0<..<2 \<cdot> t}"
using galilean_position by blast
hence "((\<lambda>t. a \<cdot> t^2 / 2 + v \<cdot> t + x) has_vderiv_on ?f) {0<..<2 \<cdot> t}"
unfolding vderiv_of_def  by (metis (mono_tags, lifting) someI_ex)
also have "((\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) has_vderiv_on (\<lambda>t. a \<cdot> t + v)) {0<..<2 \<cdot> t}"
using galilean_position by simp
ultimately show "(vderiv_of (\<lambda>t. a \<cdot> t^2 / 2 + v \<cdot> t + x) {0<..<2 \<cdot> t}) t = a \<cdot> t + v"
apply(rule_tac f'="?f" and \<tau>="t" and t="2\<cdot>t" in vderiv_unique_within_open_interval)
using \<open>t \<in> {0<..<2 \<cdot> t}\<close> by auto
qed

(* A remainder of how not to prove the above theorem... *)
lemma "t > 0 \<Longrightarrow> vderiv_of (\<lambda>t. a \<cdot> t^2 / 2 + v \<cdot> t + x) {0<..<2 \<cdot> t} t = a \<cdot> t + v"
unfolding vderiv_of_def apply(subst some1_equality[of _ "(\<lambda>t. a \<cdot> t + v)"]) 
apply(rule_tac a="\<lambda>t. a \<cdot> t + v" in ex1I)
apply(simp_all add: galilean_position)
apply(rule ext, rename_tac f \<tau>)
apply(rule_tac f="\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x" and t="2 \<cdot> t" and f'="f" in vderiv_unique_within_open_interval)
apply(simp_all add: galilean_position)
oops

lemma galilean_velocity[galilean_transform]:"((\<lambda>r. a \<cdot> r + v) has_vderiv_on (\<lambda>t. a)) T"
apply(rule_tac f'1="\<lambda> x. a" and g'1="\<lambda> x. 0" in derivative_intros(190))
unfolding has_vderiv_on_def by(auto intro: derivative_eq_intros)

lemma [galilean_transform_eq]:
"t > 0 \<Longrightarrow> vderiv_of (\<lambda>r. a \<cdot> r + v) {0<..<2 \<cdot> t} t = a"
proof-
let ?f = "vderiv_of (\<lambda>r. a \<cdot> r + v) {0<..<2 \<cdot> t}" 
assume "t > 0" hence "t \<in> {0<..<2 \<cdot> t}" by auto
have "\<exists> f. ((\<lambda>r. a \<cdot> r + v) has_vderiv_on f) {0<..<2 \<cdot> t}"
using galilean_velocity by blast
hence "((\<lambda>r. a \<cdot> r + v) has_vderiv_on ?f) {0<..<2 \<cdot> t}"
unfolding vderiv_of_def  by (metis (mono_tags, lifting) someI_ex)
also have "((\<lambda>r. a \<cdot> r + v) has_vderiv_on (\<lambda>t. a)) {0<..<2 \<cdot> t}"
using galilean_velocity by simp
ultimately show "(vderiv_of (\<lambda>r. a \<cdot> r + v) {0<..<2 \<cdot> t}) t = a"
apply(rule_tac f'="?f" and \<tau>="t" and t="2\<cdot>t" in vderiv_unique_within_open_interval)
using \<open>t \<in> {0<..<2 \<cdot> t}\<close> by auto
qed

lemma [galilean_transform]:
"((\<lambda>t. v \<cdot> t - a \<cdot> t\<^sup>2 / 2 + x) has_vderiv_on (\<lambda>x. v - a \<cdot> x)) {0..t}"
apply(subgoal_tac "((\<lambda>t. - a \<cdot> t\<^sup>2 / 2 + v \<cdot> t  +x) has_vderiv_on (\<lambda>x. - a \<cdot> x + v)) {0..t}", simp)
by(rule galilean_transform)

lemma [galilean_transform_eq]:"t > 0 \<Longrightarrow> vderiv_of (\<lambda>t. v \<cdot> t - a \<cdot> t^2 / 2 + x) {0<..<2 \<cdot> t} t = v - a \<cdot> t"
apply(subgoal_tac "vderiv_of (\<lambda>t. - a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) {0<..<2 \<cdot> t} t = - a \<cdot> t + v", simp)
by(rule galilean_transform_eq)

lemma [galilean_transform]:
"((\<lambda>t. v - a \<cdot> t) has_vderiv_on (\<lambda>x. - a)) {0..t}"
apply(subgoal_tac "((\<lambda>t. - a \<cdot> t + v) has_vderiv_on (\<lambda>x. - a)) {0..t}", simp)
by(rule galilean_transform)

lemma [galilean_transform_eq]:"t > 0 \<Longrightarrow> vderiv_of (\<lambda>r. v - a \<cdot> r) {0<..<2 \<cdot> t} t = - a"
apply(subgoal_tac "vderiv_of (\<lambda>t. - a \<cdot> t + v) {0<..<2 \<cdot> t} t = - a", simp)
by(rule galilean_transform_eq)

lemma [simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> \<pi>\<^sub>1) x)"
by auto

end