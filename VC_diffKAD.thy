theory VC_diffKAD
imports
Main
"HOL.Transcendental"
"../afp-2017-10-18/thys/Algebraic_VCs/AVC_KAD/VC_KAD"

begin

(* Options:
    · EXTEND the store to include the primed variables and treat them syntactically.
    · Work WITHIN the relational semantics.
I suggest doing the second option as the first one may avoid continuity and differentiability. *)

definition isFlow :: "(real \<Rightarrow> real store) \<Rightarrow> string \<Rightarrow> real store \<Rightarrow> (real store \<Rightarrow> real) \<Rightarrow> 
(real store pred) \<Rightarrow> bool" where
"isFlow F var st ev P \<equiv> (F 0 = st) \<and> 
(\<forall> (x::real). x \<ge> 0 \<longrightarrow>
  (\<forall> t. 0 < t \<and> t < x \<longrightarrow> ((\<lambda> y. F y var) has_derivative ev \<circ> F) (at t)) \<and>
  (\<forall> t. 0 \<le> t \<and> t \<le> x \<longrightarrow> P (F t) \<and> (\<forall> y. y\<noteq>var \<longrightarrow> F t y = st y))  \<and>
  continuous (at_left 0) (\<lambda> y. F y var) \<and> continuous (at_right x) (\<lambda> y. F y var))"

definition guarDiffEqtn :: "string \<Rightarrow> (real store \<Rightarrow> real) \<Rightarrow> (real store pred) \<Rightarrow> real store rel" 
("D [ _ ] = _ while _ " [70, 70, 70] 61) where
"D [var] = ev while guard = {(s,(F::real \<Rightarrow> real store) t) |s t F. t \<ge> 0 \<and> (isFlow F var s ev guard)}"

(* PROOF OF dL CALCULUS. *)
(* This lemma is here just to make the reader familiarize with the notation to come. *)
lemma p2rIsCollect:"{s. P s} \<subseteq> {s. Q s} \<equiv> p2r P \<subseteq> p2r Q"
by (simp add: Collect_mono_iff)

(* Differential Weakening. *)
lemma dEvolutionImpliesGuard:"snd ` (D[x] = f while G) \<subseteq> {s. G s}"
proof(clarify)
fix a b
assume hip:"(a,b) \<in> D [ x ] = f while G" 
then obtain t::"real" and F::"real \<Rightarrow> real store" where "t\<ge>0 \<and> F t = b \<and> F 0 = a"
using guarDiffEqtn_def isFlow_def by auto
from this and hip have "G b" using guarDiffEqtn_def isFlow_def by auto 
thus "G (snd (a,b))" by simp
qed

lemma nullCompNotIfSubset:"(snd ` R) \<subseteq> {s. P s} \<Longrightarrow> R ; (rel_ad (p2r P)) = {}"
proof(auto)
fix x y z
assume "snd ` R \<subseteq> p2s P" and "(x, y) \<in> R"
hence pOfY:"y \<in> p2s P" by auto
assume "(y, z) \<in> p2r (- P)"
then have "z = y \<and> y \<notin> p2s P" by (simp add: p2r_def p2r_subid)
from this and pOfY show "False" by simp
qed

(* Sketch of this proof: [\<alpha>] \<phi> = \<not> <\<alpha>> \<not> \<phi> = (\<alpha> \<circ> \<phi>\<^sup>C)\<^sup>C = Univ \<Longleftrightarrow> (\<alpha> \<circ> \<phi>\<^sup>C) = \<emptyset> \<Longleftarrow> \<pi>\<^sub>2[\<alpha>] \<subseteq> \<phi> *)
theorem dWeakening: "p2r G \<subseteq> p2r P \<Longrightarrow> PRE C (D[x] = f while G) POST P"
proof(clarify)
fix a b::"real store"
fix G P::"real store pred"
assume guardImpliesPost: "p2r G \<subseteq> p2r P" and abDef: "(a,b) \<in> rdom (p2r C)"
have progrContainedInGuard: "snd ` (D[x] = f while G) \<subseteq> {s. G s}" 
by (simp add: dEvolutionImpliesGuard)
from this and guardImpliesPost have "snd ` (D[x] = f while G) \<subseteq> {s. P s}" using order_trans by auto
then have "(D[x] = f while G) ; (rel_ad (p2r P)) = {}" by (meson nullCompNotIfSubset)
thus "(a,b) \<in> wp (D [ x ] = f while G ) (p2r P)" by (metis abDef d_p2r p2r_subid 
rel_antidomain_kleene_algebra.addual.bbox_def rel_antidomain_kleene_algebra.am1 
rel_antidomain_kleene_algebra.fbox_one_1 relcomp_empty2 subsetCE) 
qed

(* Differential Cut. *)
lemma boxAlphaProp_IsProp: "wp R (p2r P) \<subseteq> Id"
by (simp add: rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def)

(* Should not add these "complement_rule's" to simp... *)
lemma complement_rule1: "(x,x) \<notin> rel_ad (p2r P) \<Longrightarrow> P x"
proof-
assume "(x,x) \<notin> rel_ad (p2r P)" then have "\<exists> y. (x,y) \<in> (p2r P)" by (simp add: rel_ad_def)
from this and p2r_subid have "(x,x) \<in> (p2r P)" by blast
thus "P x" by (simp add: p2r_def)
qed

lemma complement_rule2: "(x,x) \<in> rel_ad (p2r P) \<Longrightarrow> \<not> P x"
by (metis ComplD VC_KAD.p2r_neg_hom complement_rule1 empty_iff mem_Collect_eq p2s_neg_hom 
rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.am1 relcomp.relcompI)

lemma complement_rule3: "R \<subseteq> Id \<Longrightarrow> (x,x) \<notin> R \<Longrightarrow> (x,x) \<in> rel_ad R"
by (metis IdI Un_iff d_p2r rel_antidomain_kleene_algebra.addual.ars3 
rel_antidomain_kleene_algebra.addual.ars_r_def rpr)

lemma complement_rule4: "(x,x) \<in> R \<Longrightarrow> (x,x) \<notin> rel_ad R"
by (metis empty_iff rel_antidomain_kleene_algebra.addual.ars1 relcomp.relcompI)

thm wp_trafo
thm rel_ad_def

lemma guarDiffEqtn_def2: "(s1,s2) \<in> D [ x ] = f while G \<Longrightarrow> 
  \<exists> (t::real) (F::real \<Rightarrow> real store). t \<ge> 0 \<and> F t = s2 \<and> isFlow F x s1 f G"
proof-
assume "(s1, s2) \<in> D [ x ] = f while G" from this have 
"(s1, s2) \<in> {(s,(F::real \<Rightarrow> real store) t) |s t F. t \<ge> 0 \<and> (isFlow F x s f G)}"
using guarDiffEqtn_def by simp
then obtain s t F where "s = s1 \<and> t \<ge> 0 \<and> s2 = F t \<and> (isFlow F x s f G)" by blast
hence "t \<ge> 0 \<and> F t = s2 \<and> isFlow F x s1 f G" by blast
thus ?thesis by blast 
qed

theorem dCut: "(PRE P (D[x] = f while G) POST C) \<Longrightarrow> (PRE P (D[x] = f while (\<lambda> s. G s \<and> C s)) POST Q)
\<Longrightarrow> PRE P (D[x] = f while G) POST Q"
proof(clarify)
fix a b::"real store"
have "rdom \<lceil>P\<rceil> = p2r P" by simp 
assume pHenceWpCut:"rdom (p2r P) \<subseteq> wp (D [ x ] = f while G ) (p2r C)" and 
abDef:"(a,b) \<in> rdom (p2r P)"
from this have "a = b \<and> P a" by (metis Domain.DomainI contra_subsetD d_p2r 
impl_prop p2r_subid pair_in_Id_conv r2p_def rpr)
from this abDef and pHenceWpCut have "(a,a) \<in> wp (D [ x ] = f while G) (p2r C)" by blast
hence hip1:"\<forall> c. (a,c) \<in> (D [ x ] = f while G) \<longrightarrow> C c" by (metis Domain.DomainI r2p_def wp_trafo) 
assume pHenceBoxCq:"rdom (p2r P) \<subseteq> wp (D [ x ] = f while (\<lambda>s. G s \<and> C s) ) (p2r Q)"
from this and abDef have hip2:"\<forall> c. (a,c) \<in> (D [ x ] = f while (\<lambda>s. G s \<and> C s)) \<longrightarrow> Q c" 
by (metis (no_types) Domain.DomainI abDef contra_subsetD pHenceBoxCq r2p_def wp_trafo)
have "\<forall> c. (a,c) \<in> (D [ x ] = f while G) \<longrightarrow> Q c"
  proof(clarify)
  fix c 
  assume "(a, c) \<in> D [ x ] = f while G" from this obtain t::"real" and F::"real \<Rightarrow> real store" 
    where "t\<ge>0 \<and> F t = c \<and> isFlow F x a f G" 
    using guarDiffEqtn_def2 by blast 
  hence "\<forall> s. 0 \<le> s \<and> s \<le> t \<longrightarrow> (a, F s) \<in> D [ x ] = f while G" 
    oops
    oops

lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> s. 1) while (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
using dWeakening by simp 
      
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> s. 1) while (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
apply(clarify, simp add: p2r_def)
apply(simp add: rel_ad_def rel_antidomain_kleene_algebra.addual.ars_r_def)
apply(simp add: rel_antidomain_kleene_algebra.fbox_def)
apply(simp add: relcomp_def rel_ad_def guarDiffEqtn_def isFlow_def)
apply(auto)
done

declare [[show_types]]
declare [[show_sorts]]

end