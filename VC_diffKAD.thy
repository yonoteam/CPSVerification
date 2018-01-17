theory VC_diffKAD
imports
Main
"HOL.Transcendental"
"../afp-2017-10-18/thys/Algebraic_VCs/AVC_KAD/VC_KAD"

begin
(*  When people specify an initial value problem like:
       x' = f(t,x)    x(0) = x\<^sub>0 \<in> \<real>\<^sup>n
    They are assuming many things and abusing notation strongly. Formally, the following holds:
       f:\<real>\<^sup>n\<^sup>+\<^sup>1\<rightarrow>\<real>\<^sup>n (or f:\<real>\<rightarrow>\<real>\<^sup>n\<rightarrow>\<real>\<^sup>n) and x:\<real>\<rightarrow>\<real>\<^sup>n, hence x':\<real>\<rightarrow>\<real>\<^sup>n such that 
       x'=f\<circ>(id,x) (alternatively, x'= (\<lambda>s.f s (x s))) where
       (id,x):t\<mapsto>(t, \<pi>\<^sub>1(x(t)), \<pi>\<^sub>2(x(t)),\<dots>,\<pi>\<^sub>n(x(t))) and \<pi>\<^sub>i is the ith projection.
    In our implementation, we substitute every \<real>\<^sup>n with the type "real store" 
    (i.e. real \<Rightarrow> string \<Rightarrow> real). Moreover, we use "F" (instead of "x" above) as 
    the function that solves the system of differential equations. This is mainly
    because we denote syntactic variables with an "x".
*)

definition solvesIVP :: "(real \<Rightarrow> real store) \<Rightarrow> string \<Rightarrow> real store \<Rightarrow> 
(real \<Rightarrow> real store \<Rightarrow> real store) \<Rightarrow> (real store pred) \<Rightarrow> bool" where
"solvesIVP F var st expr P \<equiv> (F 0 = st) \<and> 
(\<forall> (s::real). s \<ge> 0 \<longrightarrow>
  (\<forall> (t::real). 0 < t \<and> t < s \<longrightarrow> ((\<lambda> y. F y var) has_real_derivative ((\<lambda>y. (expr y (F y)) var) t)) (at t)) \<and>
  (\<forall> t. 0 \<le> t \<and> t \<le> s \<longrightarrow> P (F t) \<and> (\<forall> y. y\<noteq>var \<longrightarrow> F t y = st y))  \<and>
  continuous (at_left 0) (\<lambda> y. F y var) \<and> continuous (at_right s) (\<lambda> y. F y var))"
(* originally, has_real_derivative originally was has_derivative and the function 
(\<lambda>y. (expr y (F y)) var) was not evaluated at t. *)

definition guarDiffEqtn :: "string \<Rightarrow> (real \<Rightarrow> real store \<Rightarrow> real store) \<Rightarrow> (real store pred) \<Rightarrow> 
real store rel" ("D [ _ ] = _ with _ " [70, 70, 70] 61) where
"D [var] = expr with restr = 
  {(st,(F::real \<Rightarrow> real store) t) |st t F. t \<ge> 0 \<and> (solvesIVP F var st expr restr)}"

(* dL CALCULUS. *)

(* This lemma is here just to make the reader familiarize with the notation to come. *)
lemma p2rIsCollect:"{s. P s} \<subseteq> {s. Q s} \<equiv> p2r P \<subseteq> p2r Q"
by (simp add: Collect_mono_iff)

(* Differential Weakening. *)
lemma dEvolutionImpliesGuard:"snd ` (D[x] = f with G) \<subseteq> {s. G s}"
proof(clarify)
fix a b
assume hip:"(a,b) \<in> D [ x ] = f with G" 
then obtain t::"real" and F::"real \<Rightarrow> real store" where "t\<ge>0 \<and> F t = b \<and> F 0 = a"
using guarDiffEqtn_def solvesIVP_def by auto
from this and hip have "G b" using guarDiffEqtn_def solvesIVP_def by auto 
thus "G (snd (a,b))" by simp
qed

lemma nullComposIfSubset:"(snd ` R) \<subseteq> {s. P s} \<Longrightarrow> R ; (rel_ad (p2r P)) = {}"
proof(auto)
fix x y z
assume "snd ` R \<subseteq> p2s P" and "(x, y) \<in> R"
hence pOfY:"y \<in> p2s P" by auto
assume "(y, z) \<in> p2r (- P)"
then have "z = y \<and> y \<notin> p2s P" by (simp add: p2r_def p2r_subid)
from this and pOfY show "False" by simp
qed

(* Sketch of this proof: [\<alpha>] \<phi> = \<not> <\<alpha>> \<not> \<phi> = (\<alpha> \<circ> \<phi>\<^sup>C)\<^sup>C = Univ \<Longleftrightarrow> (\<alpha> \<circ> \<phi>\<^sup>C) = \<emptyset> \<Longleftarrow> \<pi>\<^sub>2[\<alpha>] \<subseteq> \<phi> *)
theorem dWeakening: "p2r G \<subseteq> p2r P \<Longrightarrow> PRE C (D[x] = f with G) POST P"
proof(clarify)
fix a b::"real store"
assume guardImpliesPost: "p2r G \<subseteq> p2r P" and abHyp: "(a,b) \<in> rdom (p2r C)"
have progrContainedInGuard: "snd ` (D[x] = f with G) \<subseteq> {s. G s}" 
by (simp add: dEvolutionImpliesGuard)
from this and guardImpliesPost have "snd ` (D[x] = f with G) \<subseteq> {s. P s}" using order_trans by auto
then have "(D[x] = f with G) ; (rel_ad (p2r P)) = {}" by (meson nullComposIfSubset)
thus "(a,b) \<in> wp (D [ x ] = f with G ) (p2r P)" by (metis abHyp d_p2r p2r_subid 
rel_antidomain_kleene_algebra.addual.bbox_def rel_antidomain_kleene_algebra.am1 
rel_antidomain_kleene_algebra.fbox_one_1 relcomp_empty2 subsetCE) 
qed

(* Example of hybrid program verified with differential weakening. *)      
lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> t s var. s ''x'' + 1) with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
apply(clarify, simp add: p2r_def)
apply(simp add: rel_ad_def rel_antidomain_kleene_algebra.addual.ars_r_def)
apply(simp add: rel_antidomain_kleene_algebra.fbox_def)
apply(simp add: relcomp_def rel_ad_def guarDiffEqtn_def solvesIVP_def)
apply(auto)
done

lemma "PRE (\<lambda> s. s ''x'' > 0)  
      (D[''x''] = (\<lambda> t s var. s ''x'' + 1) with (\<lambda> s. s ''x'' > 0))
      POST (\<lambda> s. s ''x'' > 0)"
using dWeakening by simp 

(* Differential Cut. *)
lemma boxProgrPred_IsProp: "wp R (p2r P) \<subseteq> Id"
by (simp add: rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def)

lemma rdom_p2r_contents[simp]:"(a, b) \<in> rdom (p2r P) = ((a = b) \<and> P a)" 
proof-
have "(a, b) \<in> rdom (p2r P) = ((a = b) \<and> (a, a) \<in> rdom (p2r P))" using p2r_subid by fastforce 
also have "((a = b) \<and> (a, a) \<in> rdom (p2r P)) = ((a = b) \<and> (a, a) \<in> (p2r P))" by simp
also have "((a = b) \<and> (a, a) \<in> (p2r P)) = ((a = b) \<and> P a)" by (simp add: p2r_def) 
ultimately show ?thesis by simp
qed

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

lemma boxProgrPred_chrctrztn:"(x,x) \<in> wp R (p2r P) = (\<forall> y. (x,y) \<in> R \<longrightarrow> P y)"
by (metis boxProgrPred_IsProp complement_rule1 complement_rule2 complement_rule3 
complement_rule4 d_p2r wp_simp wp_trafo)

lemma boxProgrRel_chrctrztn:"pRel \<subseteq> Id \<Longrightarrow> (x,x) \<in> wp R pRel = (\<forall> y. (x,y) \<in> R \<longrightarrow> r2p pRel y)"
by (metis boxProgrPred_chrctrztn rpr)

lemma boxProgrRel_eRule1:"(x,y) \<in> wp R (p2r P) \<Longrightarrow> (\<forall> y. (x,y) \<in> R \<longrightarrow> P y)"
by (metis boxProgrPred_chrctrztn boxProgrPred_IsProp pair_in_Id_conv subsetCE)

lemma boxProgrRel_eRule2:"pRel \<subseteq> Id \<Longrightarrow> (x,y) \<in> wp R pRel \<Longrightarrow> (\<forall> y. (x,y) \<in> R \<longrightarrow> r2p pRel y)"
by (metis boxProgrRel_eRule1 rpr)

lemma guarDiffEqtn_def2: "(s1,s2) \<in> D [ x ] = f with G \<Longrightarrow> 
  \<exists> (t::real) (F::real \<Rightarrow> real store). t \<ge> 0 \<and> F t = s2 \<and> solvesIVP F x s1 f G"
proof-
assume "(s1, s2) \<in> D [ x ] = f with G" from this have 
"(s1, s2) \<in> {(s,(F::real \<Rightarrow> real store) t) |s t F. t \<ge> 0 \<and> (solvesIVP F x s f G)}"
using guarDiffEqtn_def by simp
then obtain s t F where "s = s1 \<and> t \<ge> 0 \<and> s2 = F t \<and> (solvesIVP F x s f G)" by blast
hence "t \<ge> 0 \<and> F t = s2 \<and> solvesIVP F x s1 f G" by blast
thus ?thesis by blast 
qed

lemma condAfterEvol_remainsAlongEvol: 
"(a, a) \<in> wp {(s, F t) |s t F. 0 \<le> t \<and> solvesIVP F x s f G} (p2r C) \<Longrightarrow> solvesIVP F x a f G \<Longrightarrow> 
solvesIVP F x a f (\<lambda>s. G s \<and> C s)"
proof-
assume "(a, a) \<in> wp {(s, F t) |s t F. 0 \<le> t \<and> solvesIVP F x s f G} (p2r C)" then have 
diffHyp:"\<forall> c. (a,c) \<in> {(s, F t) |s t F. 0 \<le> t \<and> solvesIVP F x s f G} \<longrightarrow> C c" using wp_trafo
by (metis (no_types, lifting) Domain.intros r2p_def)
assume flowHyp:"solvesIVP F x a f G"
show "solvesIVP F x a f (\<lambda>s. G s \<and> C s)"
  proof(simp add: solvesIVP_def, rule conjI)
  show "F 0 = a" using flowHyp solvesIVP_def by simp
  from flowHyp have "\<forall>s\<ge>0. (\<forall>t. 0 < t \<and> t < s \<longrightarrow> ((\<lambda>y. F y x) has_real_derivative ((\<lambda>y. (f y (F y)) x) t)) (at t)) \<and> 
  (\<forall>t. 0 \<le> t \<and> t \<le> s \<longrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> F t y = a y)) \<and> continuous (at_left 0) (\<lambda>y. F y x) \<and> 
  continuous (at_right s) (\<lambda>y. F y x)" by (simp add: solvesIVP_def)
  from this show "\<forall>xa\<ge>0. (\<forall>t. 0 < t \<and> t < xa \<longrightarrow> ((\<lambda>y. F y x) has_real_derivative ((\<lambda>y. (f y (F y)) x) t)) (at t)) \<and>
  (\<forall>t. 0 \<le> t \<and> t \<le> xa \<longrightarrow> G (F t) \<and> C (F t) \<and> (\<forall>y. y \<noteq> x \<longrightarrow> F t y = a y)) \<and>
  continuous (at_left 0) (\<lambda>y. F y x) \<and> continuous (at_right xa) (\<lambda>y. F y x)"
    proof(clarsimp)
    fix s t::"real" assume "0 \<le> t"
    hence "(a,F t) \<in> {(s, F t) |s t F. 0 \<le> t \<and> solvesIVP F x s f G}" using flowHyp by auto
    then show "G (F t) \<and> C (F t)" using \<open>0 \<le> t\<close> solvesIVP_def and diffHyp by auto 
    qed
  qed
qed

lemma boxDiffPred_impliesAllTimeInDiff:"(a,a) \<in> wp (D [ x ] = f with G) (p2r C) \<Longrightarrow>
\<forall> t F. t\<ge>0 \<and> solvesIVP F x a f G \<longrightarrow> (a,F t) \<in> (D [ x ] = f with (\<lambda>s. G s \<and> C s))"
apply(clarify, simp add: guarDiffEqtn_def, rule_tac x="t" in exI)
apply(rule_tac x="F" in exI, rule conjI, simp, rule conjI, simp)
apply(simp add: condAfterEvol_remainsAlongEvol)
done

theorem dCut: "(PRE P (D[x] = f with G) POST C) \<Longrightarrow> (PRE P (D[x] = f with (\<lambda> s. G s \<and> C s)) POST Q)
\<Longrightarrow> PRE P (D[x] = f with G) POST Q"
proof(clarify)
fix a b::"real store" 
assume pHenceWpCut:"rdom (p2r P) \<subseteq> wp (D [ x ] = f with G ) (p2r C)" 
assume abHyp:"(a,b) \<in> rdom (p2r P)"
from this have "a = b \<and> P a" by (metis rdom_p2r_contents)
from this abHyp and pHenceWpCut have hip1:"(a,a) \<in> wp (D [ x ] = f with G) (p2r C)" by blast 
assume pHenceBoxCq:"rdom (p2r P) \<subseteq> wp (D [ x ] = f with (\<lambda>s. G s \<and> C s) ) (p2r Q)"
from this and abHyp have hip2:"\<forall> c. (a,c) \<in> (D [ x ] = f with (\<lambda>s. G s \<and> C s)) \<longrightarrow> Q c"
by (metis (no_types, lifting) \<open>a = b \<and> P a\<close> boxProgrPred_chrctrztn set_mp)
have "\<forall> c. (a,c) \<in> (D [ x ] = f with G) \<longrightarrow> Q c"
  proof(clarify)
  fix c 
  assume "(a, c) \<in> D [ x ] = f with G" from this obtain t::"real" and F::"real \<Rightarrow> real store" 
  where Fdef:"t\<ge>0 \<and> F t = c \<and> solvesIVP F x a f G" using guarDiffEqtn_def2 by blast 
  then have "(a, F t) \<in> D [ x ] = f with (\<lambda>s. G s \<and> C s)" using boxDiffPred_impliesAllTimeInDiff
  using hip1 by blast
  from this Fdef and hip2 show "Q c" by simp
  qed
from this and \<open>a = b \<and> P a\<close> show "(a,b) \<in> wp (D [ x ] = f with G) (p2r Q)" 
by (simp add: boxProgrPred_chrctrztn)
qed 

(* Diffierential Invariant Rule. *)
(*datatype trms = Const real | Eq trms trms | Geq trms trms

datatype props = Const "real \<Rightarrow> real \<Rightarrow> bool" | Var "real \<Rightarrow> real \<Rightarrow> bool" | Neg boolex | And boolex boolex*)

term "\<lambda> s. s ''x'' > (0::real)"


(* deriv_Pred :: "real store pred \<Rightarrow> real store pred" *)
function deriv_Pred :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool)" where
"deriv_Pred (op \<and>) = (op \<and>)"|
"deriv_Pred (op \<or>) = (op \<and>)"
oops

theorem "\<forall> st. P st \<longrightarrow> G st \<longrightarrow> Q st \<Longrightarrow> PRE G (var ::= S) POST Q \<Longrightarrow> 
PRE P (D [var] = f with G) POST Q"
oops

lemma "PRE (\<lambda> s. s ''x'' >0 \<and> s ''v'' > 0)
      ((D[''x''] = (\<lambda> t s var. s ''v'') with (\<lambda> s. True)))
      POST (\<lambda> s. s ''x''> 0)"
      apply(rule_tac C = "\<lambda> s. s ''v'' \<ge> 0" in dCut)
      defer
      apply(rule_tac C = "\<lambda> s. s ''x'' > 0" in dCut)
      defer
      apply(rule dWeakening)
      apply(simp)
      oops

      term r
      
(* Solve-Differential-Equation Rule. *)
theorem solveDiff:"\<forall> st. solvesIVP (\<lambda> t. st(var := (x t st))) var st f G
\<Longrightarrow> \<forall> st. \<forall> X. solvesIVP X var st f G \<longrightarrow> (\<forall> t \<ge> 0. st(var := (x t st)) = X t)  \<Longrightarrow>
\<forall> st. P st \<longrightarrow> (\<forall> t \<ge> 0. (\<forall> rr. 0 \<le> rr \<and> rr \<le> t \<longrightarrow> G (st(var := (x rr st)))) \<longrightarrow> 
(r2p (wp (var ::= x t) (p2r Q)) st))
\<Longrightarrow> PRE P (D[var] = f with G) POST Q "
proof
fix pair
assume "pair \<in> rdom (p2r P)" from this obtain a::"real store" where
aHyp:"pair = (a,a) \<and> P a" by (metis IdE contra_subsetD d_p2r p2r_subid rdom_p2r_contents)
assume "\<forall> st. solvesIVP (\<lambda> t. st(var := (x t st))) var st f G"
from this have xIsSolution:"solvesIVP (\<lambda> t. a(var := (x t a))) var a f G" by simp
assume "\<forall> st. \<forall> X. solvesIVP X var st f G \<longrightarrow> (\<forall> t \<ge> 0. st(var := (x t st)) = X t)" 
from this have uniq:"\<forall> X. solvesIVP X var a f G \<longrightarrow> (\<forall> t \<ge> 0. a(var := (x t a))= X t)" 
using xIsSolution by metis
assume "\<forall> st. P st \<longrightarrow> (\<forall> t \<ge> 0. (\<forall> rr. 0 \<le> rr \<and> rr \<le> t \<longrightarrow> G (st(var := (x rr st)))) \<longrightarrow> 
r2p (wp (var ::= x t) (p2r Q)) st)"
from this and aHyp have "(\<forall>t\<ge>0. (\<forall>rr. 0 \<le> rr \<and> rr \<le> t \<longrightarrow> G (a(var := (x rr a)))) \<longrightarrow> 
r2p (wp (var ::= x t) (p2r Q)) a)" by simp
then have antiDerivHyp:"(\<forall>t\<ge>0. (\<forall>rr. 0 \<le> rr \<and> rr \<le> t \<longrightarrow> G (a(var := (x rr a)))) \<longrightarrow> 
(\<forall> c. (a,c) \<in> (var ::= x t) \<longrightarrow> Q c))" 
by (metis rdom_p2r_contents wp_simp boxProgrRel_eRule1) 
have "\<forall> c. (a,c) \<in> (D [ var ] = f with G) \<longrightarrow> Q c"
  proof(clarify)
  fix c 
  assume "(a, c) \<in> D [ var ] = f with G" from this obtain t::"real" and F::"real \<Rightarrow> real store" 
  where Fdef:"t\<ge>0 \<and> F t = c \<and> solvesIVP F var a f G" using guarDiffEqtn_def2 by blast 
  from this and uniq have eq2:"(\<lambda> rr. a(var := (x rr a))) t = F t" by blast
  from Fdef have "\<forall>s\<ge>0.(\<forall>t. 0 \<le> t \<and> t \<le> s \<longrightarrow> (\<forall>y::char list. y \<noteq> var \<longrightarrow> F t y = a y))"
  using solvesIVP_def by simp
  from this have "(\<forall>y::char list. y \<noteq> var \<longrightarrow> F t y = a y)" using Fdef by auto
  then have "\<forall> y. F t y = (a (var := x t a)) y" using eq2 by auto
  hence "F t = a (var := x t a)" by auto
  from this have "(a, F t) \<in> (var ::= x t)" using gets_def by blast 
  then show "Q c" using Fdef xIsSolution antiDerivHyp solvesIVP_def by auto 
  qed
from this have "(a,a) \<in>  wp (D [ var ] = f with G ) (p2r Q)" by (simp add: boxProgrPred_chrctrztn)
then show "pair \<in> wp (D [ var ] = f with G ) (p2r Q)" using aHyp by simp
qed

(* This definition is in the AFP entry on ODE's:
solves_ode :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool"
where "(X solves_ode F) DerivDom CodOfX \<longleftrightarrow> (X has_vderiv_on (\<lambda>t. F t (X t))) DerivDom \<and> 
                                             X: DerivDom \<rightarrow> CodOfX"
Hence, to use this theory/definition with our own predicate "isSolution", we should feed it with:
    - (\<lambda> y. x y var) as X.                   [ x :: real \<Rightarrow> (string \<Rightarrow> real) ]
    - (\<lambda> y. \<lambda> z. f y (x y) var) as F.        [ f :: real \<Rightarrow> (string \<Rightarrow> real) \<Rightarrow> (string \<Rightarrow> real)]

However, the way they proved the Picard-Lindelöf theorem, does not help us to show uniqueness of our
solutions, even if we constrain them to being Lipschitz continuous.  *)

(* Useful observations *)
thm boxProgrPred_chrctrztn
thm r2p_def
term "Set.Collect"
term "Domain R" 
thm rel_antidomain_kleene_algebra.fbox_def
thm rel_ad_def

lemma boxProgrPred_chrctrztn2:"x \<in> r2s (wp R P) = (\<forall>y. (x, y) \<in> R \<longrightarrow> (r2p P) y)"
apply(auto simp: r2p_def rel_antidomain_kleene_algebra.fbox_def rel_ad_def, blast)
by fastforce

lemma dotOpIsMult:"op \<cdot> (c::real) = (\<lambda> x. c \<cdot> x)"
by auto

lemma constantAdditive: "\<forall>x y. (\<lambda>x. c) (x + y) = (\<lambda>x. c) x + (\<lambda>x. c) y"
oops

lemma derivOfMult1:"((\<lambda> x. (c::real) \<cdot> x) has_derivative (\<lambda>x. c)) (at t)"
apply(simp add: has_derivative_def)
apply(simp add: bounded_linear_def)
apply(simp add: bounded_linear_axioms_def)
apply(simp add: linear_def)
apply(rule conjI)
thm additive_def
apply(simp add: additive_def)
apply(auto)
oops

lemma derivOfMult:"((op \<cdot> (c::real)) has_derivative (\<lambda>x. c)) (at t)"
apply(rule derivative_eq_intros)
apply(rule derivative_intros)  
nitpick
oops

theorem voltea:"(\<not> Q) \<longrightarrow> \<not> P \<Longrightarrow> P \<longrightarrow> Q"
by linarith

thm "DERIV_def" 
term "DERIV g (f x) :> E"
term "op \<cdot> (t::real)"
thm derivative_intros
thm derivative_eq_intros
thm continuous_intros

lemma "PRE (\<lambda> s. s ''station'' < s ''pos''  \<and> s ''vel'' > 0)  
      (
      (D[''pos''] = (\<lambda> t s var. s ''vel'') with (\<lambda> s. True))
      )
      POST (\<lambda> s. (s ''station'' < s ''pos''))"
      apply(rule_tac x = "(\<lambda> t. \<lambda> s. s ''vel'' \<cdot> t + s ''pos'')" in solveDiff)
      apply(simp add: solvesIVP_def, safe)[1]  (* Goal split in three. *)
      apply(rule derivative_eq_intros)          (* Goal split in three. *)
      apply(rule derivative_intros)+             (* Goal split in two. *)
      apply(simp)                               (* Goal gone. *)
      apply(rule continuous_intros)+         (* Goal split in two. *)
      defer
      apply(simp add: p2r_def r2p_def boxProgrPred_chrctrztn2 gets_def, clarify)
      apply(simp add: Domain_iff add_strict_increasing2) (* Goal gone. *) 
      (*apply(rule allI, rule allI, rule impI)
      apply(simp add: isSolution_def)
      proof(rule allI, clarify)
      fix X::"real \<Rightarrow> real store"
      fix t::"real"
      assume tDef:"t \<ge> 0"
      assume xIsSolution:"\<forall>s\<ge>0. (\<forall>t. 0 < t \<and> t < s \<longrightarrow> 
      ((\<lambda>y. X y ''pos'') has_real_derivative X t ''vel'') (at t)) \<and> 
      (\<forall>t. 0 \<le> t \<and> t \<le> s \<longrightarrow> (\<forall>y. y \<noteq> ''pos'' \<longrightarrow> X t y = X 0 y)) \<and> 
      continuous (at_left 0) (\<lambda>y. X y ''pos'') \<and> continuous (at_right s) (\<lambda>y. X y ''pos'')"
      then have "\<forall>t \<ge> 0. \<forall>y. y \<noteq> ''pos'' \<longrightarrow> X t y = X 0 y" by (meson order_refl) 
      from this and tDef have "\<forall>y. y \<noteq> ''pos'' \<longrightarrow> X t y = X 0 y" by blast
      also have ""
      hence "\<forall>y. y \<noteq> ''pos'' \<longrightarrow> (X 0)(''pos'' := X 0 ''vel'' \<cdot> t + X 0 ''pos'') = X t" 
      *)
      apply(rule allI, rule allI)
      apply(rule voltea)
      apply(simp add: solvesIVP_def, clarify)
      proof(rule, rule conjI, simp, rule impI)
      fix X::"real \<Rightarrow> real store"
      fix t::"real"
      assume tDef:"t\<ge>0" and "(X 0)(''pos'' := X 0 ''vel'' \<cdot> t + X 0 ''pos'') \<noteq> X t"
      from this obtain str::"char list" where 
      distinctStr:"((X 0)(''pos'' := X 0 ''vel'' \<cdot> t + X 0 ''pos'')) str \<noteq> X t str" by (meson ext)
      assume xContFromLeft:"continuous (at_left 0) (\<lambda>y. X y ''pos'')"
      let ?goal = "(\<exists>ta>0. ta < t \<and> \<not> ((\<lambda>y. X y ''pos'') has_real_derivative X ta ''vel'') (at ta)) 
      \<or> (\<exists>ta\<ge>0. ta \<le> t \<and> (\<exists>y. y \<noteq> ''pos'' \<and> X ta y \<noteq> X 0 y)) 
      \<or> \<not> continuous (at_right t) (\<lambda>y. X y ''pos'')"
      {assume strIsPos:"str = ''pos''"
        from this have "((X 0)(''pos'' := X 0 ''vel'' \<cdot> t + X 0 ''pos'')) str = 
        X 0 ''vel'' \<cdot> t + X 0 ''pos''" by simp
        hence "X t ''pos'' \<noteq> X 0 ''vel'' \<cdot> t + X 0 ''pos''" using distinctStr by (simp add: strIsPos)
        from this have "t > 0" using less_eq_real_def tDef by auto 
        then have ?goal sorry}
      moreover
      {assume strIsntPos:"str \<noteq> ''pos''"
        from this have "\<exists>rr\<ge>0. rr \<le> t \<and> (\<exists>y. y \<noteq> ''pos'' \<and> X rr y \<noteq> X 0 y)" 
        using distinctStr tDef by fastforce
        then have ?goal by simp}
      ultimately show ?goal by auto
      qed

(* Verification Examples. *)

declare [[show_types]]
declare [[show_sorts]]

lemma "rdom (p2r P) \<subseteq> wp X (wp Y (p2r Q)) \<Longrightarrow> rdom (p2r P) \<subseteq> wp (X; Y) (p2r Q)"
by simp

lemma "rdom (p2r (\<lambda> s. P s \<and> (s str = e s))) \<subseteq> (p2r (\<lambda> s. Q (s(str := e s)))) \<Longrightarrow> rdom (p2r P) \<subseteq> wp (str ::= (e::real store \<Rightarrow> real)) (p2r Q)"
apply(auto)
oops

lemma "rdom (p2r (\<lambda> s. P (s(str := e s)))) \<subseteq> (p2r (\<lambda> s. Q (s(str := e s)))) \<Longrightarrow> rdom (p2r P) \<subseteq> wp (str ::= (e::real store \<Rightarrow> real)) (p2r Q)"
apply(auto)
oops

lemma randomRule:"(p2r P) \<subseteq> (p2r (\<lambda> s. Q (s(str := e s)))) \<Longrightarrow> (p2r P) \<subseteq> wp (str ::= e) (p2r Q)"
apply(auto)
done

lemma convRandomRule: "(p2r P) \<subseteq> wp (str ::= e) (p2r Q) \<Longrightarrow> (p2r P) \<subseteq> (p2r (\<lambda> s. Q (s(str := e s))))"
by auto

lemma firstMastersVerification:
      "PRE (\<lambda> s. s ''station'' > s ''pos'' \<and> s ''vel'' > 0)  
      (
      (''acc'' ::= (\<lambda>s. - (s ''vel'')*(s ''vel'') / (2 * (s ''station'' - s ''pos''))));
      ((D[''pos''] = (\<lambda> t s var. s ''vel'') with (\<lambda> s. True))\<inter>(D[''vel''] = (\<lambda> t s var. s ''acc'') with (\<lambda> s. s ''vel'' \<ge> 0)) )
      )
      POST (\<lambda> s. (s ''station'' \<ge> s ''pos'') \<and> (s ''vel'' = 0 \<longleftrightarrow> s ''station'' = s ''pos''))"
      apply(simp)
      apply(erule convRandomRule)
      (* just add the "acc ::= blah, blah" to the preconditions and try to use your solveDiff rule.*)
      oops
      
(*proof(auto)
fix a b::"real store"
assume "(a, b) \<in> p2r (\<lambda>s. s ''pos'' < s ''station'' \<and> 0 < s ''vel'')"
from this have "a = b \<and> (a ''pos'' < a ''station'') \<and> (0 < a ''vel'')"
by (metis (no_types, lifting) d_p2r rdom_p2r_contents)
have "\<forall> c. (a,c) \<in> (''acc'' ::= (\<lambda>s. - (s ''vel'' \<cdot> s ''vel'' / (2 \<cdot> s ''station'' - 2 \<cdot> s ''pos''))))
\<longrightarrow> (r2p (wp ((D [ ''pos'' ] = (\<lambda>t s var. s ''vel'') with (\<lambda>s. True) ) \<inter> (D [ ''vel'' ] = (\<lambda>t s var. s ''acc'') with (\<lambda>s. 0 \<le> s ''vel'') ))
                        (p2r (\<lambda>s. s ''pos'' \<le> s ''station'' \<and> (s ''vel'' = 0) = (s ''station'' = s ''pos'')))) c)"
   proof(clarify)
   fix c
   assume "(a, c) \<in> ''acc'' ::= (\<lambda>s. - (s ''vel'' \<cdot> s ''vel'' / (2 \<cdot> s ''station'' - 2 \<cdot> s ''pos'')))"
   from this have "c = a(''acc'' := (- (a ''vel'' \<cdot> a ''vel'' / (2 \<cdot> a ''station'' - 2 \<cdot> a ''pos''))))" 
   by (simp add: gets_def)
oops*)

end