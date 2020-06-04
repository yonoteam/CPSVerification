(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

chapter \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory ARCH2020_examples
  imports "Hybrid_Systems_VCs.HS_VC_MKA_rel" "Matrices_for_ODEs.MTX_Flows"

begin


section \<open> Basic \<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")


subsection \<open> Basic assignment \<close> 

(* x>=0 -> [x:=x+1;]x>=1 *)
lemma "\<lceil>\<lambda>s. s$1 \<ge> (0::real)\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>"
  by simp


subsection \<open> Overwrite assignment on some branches \<close>

declare rel_aka.fbox_add2 [simp]

(* x>=0 -> [x:=x+1;][x:=x+1; ++ y:=x+1;]x>=1 *)
lemma "\<lceil>\<lambda>s. s$1 \<ge> (0::real)\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) 
  (wp ((1 ::= (\<lambda>s. s$1 +1)) \<union> (2 ::= (\<lambda>s. s$1 +1))) \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)"
  by simp


subsection \<open> Overwrite assignment in loop \<close>

context antidomain_kleene_algebra
begin

lemma fbox_seq_var: "p \<le> |x] p' \<Longrightarrow> p' \<le> |y] q \<Longrightarrow>  p \<le> |x \<cdot> y] q"

proof -
  assume h1: "p \<le> |x] p'" and h2: "p' \<le> |y] q"
  hence "|x] p' \<le> |x] |y] q"
    by (metis ads_d_def fbox_antitone_var fbox_dom fbox_iso)
  thus ?thesis
    by (metis dual_order.trans fbox_mult h1)
qed

lemma fbox_loopi_break: "d p \<le> |y] d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |y \<cdot> (loop x inv i)] q"
  by (rule fbox_seq_var, force) (rule fbox_loopi, auto) 

end

lemma wp_loopI_break: "\<lceil>P\<rceil> \<le> wp Y \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp X \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>  \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (Y ; (LOOP X INV I)) \<lceil>Q\<rceil>"
  by (subst p2r_simps(6)[symmetric], rule rel_aka.fbox_loopi_break, auto)

(* x>=0 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1)]x>=1 *)
lemma "\<lceil>\<lambda>s. s$1 \<ge> (0::real)\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) 
 (wp (LOOP (1 ::= (\<lambda>s. s$1 +1)) INV (\<lambda>s. s$1 \<ge> 1)) \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)"
  apply(subst rel_aka.fbox_mult[symmetric])
  by (rule wp_loopI_break, auto)


subsection \<open> Overwrite assignment in ODE \<close>

(* x>=0 -> [x:=x+1;][{x'=2}]x>=1 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s. s$1 \<ge> (0::real)\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) 
 (wp (x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then 2 else 0)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)" 
  apply(subst local_flow.fbox_g_ode_ivl[where \<phi>="\<lambda>t s. (\<chi> i. if i=1 then 2*t+s$1 else s$i)" and T=UNIV])
     apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff)
   apply(clarsimp, rule_tac x=1 in exI)+
  by (auto intro!: poly_derivatives)


subsection \<open> Overwrite with nondeterministic assignment \<close>

definition nondet_assign :: "'b \<Rightarrow> ('a^'b) rel" ("(2_ ::= ? )" [70] 61)
  where "(x ::= ?) = {(s,vec_upd s x k)|s k. True}"

lemma wp_nondet_assign[simp]: "wp (x ::= ?) \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<forall>k. P (\<chi> j. ((($) s)(x := k)) j)\<rceil>"
  unfolding wp_rel nondet_assign_def vec_upd_def apply(clarsimp, safe)
   apply(erule_tac x="vec_lambda ((($) s)(x := k))" in allE, clarsimp)
   apply(erule impE, rule_tac x=k in exI, simp)
   apply(subgoal_tac "vec_lambda ((($) s)(x := k)) = (\<chi> j. if j = x then k else s $ j)", simp)
   apply(simp add: vec_eq_iff)
  apply(erule_tac x=k in allE)
   apply(subgoal_tac "vec_lambda ((($) s)(x := k)) = (\<chi> j. if j = x then k else s $ j)", simp)
  by (simp add: vec_eq_iff)

(* x>=0 -> [x:=x+1;][x:=*; ?x>=1;]x>=1 *)
lemma "\<lceil>\<lambda>s. s$1 \<ge> (0::real)\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) (wp ((1 ::= ?);\<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>) \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)" 
  by (simp add: wp_rel, auto simp: p2r_def)


subsection \<open> Tests and universal quantification \<close>

(* x>=0 -> [x:=x+1;][?x>=2; x:=x-1; ++ ?\forall x (x>=1 -> y>=1); x:=y;]x>=1 *)
lemma "\<lceil>\<lambda>s::real^2. s$1 \<ge> 0\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) 
  (wp ((\<lceil>\<lambda>s. s$1 \<ge> 2\<rceil>;(1 ::= (\<lambda>s. s$1 - 1))) \<union> (\<lceil>\<lambda>s. \<forall>i. s$i \<ge> 1 \<longrightarrow> s$2 \<ge> 1\<rceil>;(1 ::= (\<lambda>s. s$2)))) 
  \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)" 
  by (simp add: wp_rel, auto simp: p2r_def assign_def vec_upd_def) 


subsection \<open> Overwrite assignment several times \<close>

lemma (in antidomain_kleene_algebra) choice_to_conj: 
  "d p \<le> |x + y]q \<longleftrightarrow> (d p \<le> |x]q) \<and> (d p \<le> |y]q)"
  apply (rule iffI, rule conjI)
  apply (metis fbox_antitone_var join.le_sup_iff join.sup.absorb_iff1 join.sup.cobounded1)
  apply (metis fbox_antitone_var join.le_sup_iff join.sup.absorb_iff1 join.sup.cobounded1)
  by (smt a_2_var a_6 a_d_add_closure a_mult_add ads_d_def as1 fbox_add2 fbox_def 
      join.le_sup_iff less_eq_def)

lemma wp_choice: "\<lceil>P\<rceil> \<le> wp (X \<union> Y) \<lceil>Q\<rceil> \<longleftrightarrow> \<lceil>P\<rceil> \<le> wp X \<lceil>Q\<rceil> \<and> \<lceil>P\<rceil> \<le> wp Y \<lceil>Q\<rceil>"
  apply(subgoal_tac "rel_aka.ads_d \<lceil>P\<rceil> \<subseteq> wp (X \<union> Y) \<lceil>Q\<rceil> \<longleftrightarrow> 
  (rel_aka.ads_d \<lceil>P\<rceil> \<subseteq> wp X \<lceil>Q\<rceil> \<and> rel_aka.ads_d \<lceil>P\<rceil> \<subseteq> wp Y \<lceil>Q\<rceil>)")
  by (simp, rule rel_aka.choice_to_conj)

lemma wp_change_loopi: "\<lceil>P\<rceil> \<subseteq> wp (LOOP X INV I) \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> wp (LOOP X INV G) \<lceil>Q\<rceil>"
  by (unfold rel_aka.loopi_def, simp)

(* x>=0 & y>=1 -> [x:=x+1;][{x:=x+1;}*@invariant(x>=1) ++ y:=x+1;][{y'=2}][x:=y;]x>=1 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1 \<ge> 0 \<and> s$2 \<ge> 1\<rceil> \<le> wp (1 ::= (\<lambda>s. s$1 +1)) 
    (wp ((LOOP (1 ::= (\<lambda>s. s$1 +1)) INV (\<lambda>s. s$1 \<ge> 1)) \<union> (2 ::= (\<lambda>s. s$1 + 1)))
    (wp (x\<acute>=(\<lambda>s. (\<chi> i. if i=2 then 2 else 0)) & G on {0..t} UNIV @ 0) (wp (1 ::= (\<lambda>s. s$2)) 
  \<lceil>\<lambda>s. s$1 \<ge> 1\<rceil>)))"
  apply(subst rel_aka.fbox_mult[symmetric])+
  apply(rule rel_aka.fbox_seq_var)+
     apply(subst wp_assign[where Q="\<lambda>s. 1 \<le> s$1 \<and> 1 \<le> s$2"], simp)
    apply(subst wp_choice, rule conjI)
  apply(rule_tac I="\<lambda>s. 1 \<le> s$1 \<and> 1 \<le> s$2" in wp_change_loopi)
    apply(rule_tac Q="\<lambda>s. 1 \<le> s$1 \<and> 1 \<le> s$2" in wp_loopI, simp_all)
   apply(subst local_flow.fbox_g_ode_ivl[where \<phi>="\<lambda>t s. (\<chi> i. if i=2 then 2*t+s$2 else s$i)" 
        and T=UNIV and Q="\<lambda>s. 1 \<le> s$1 \<and> 1 \<le> s$2"]; simp?)
   apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff)
  by (clarsimp, rule_tac x=1 in exI)+ (auto intro!: poly_derivatives vec_eq_iff)


subsection \<open> Potentially overwrite dynamics \<close>

(* x>0 & y>0 -> [{x'=5}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1 > 0 \<and> s$2 > 0\<rceil> \<le> 
   wp (x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then 5 else 0)) & G on {0..t} UNIV @ 0) 
  (wp ((LOOP (1 ::= (\<lambda>s. s$1 + 3)) INV (\<lambda>s. 0 < s$1)) \<union> (2 ::= (\<lambda>s. s$1))) 
  \<lceil>\<lambda>s. s$1 > 0 \<and> s$2 > 0\<rceil>)"
  apply(subst rel_aka.fbox_mult[symmetric])+
  apply(rule rel_aka.fbox_seq_var)+
   apply(subst local_flow.fbox_g_ode_ivl[where \<phi>="\<lambda>t s. (\<chi> i. if i=1 then 5*t+s$1 else s$i)"
        and T=UNIV and Q="\<lambda>s. s$1 > 0 \<and> s$2 > 0"]; simp?)
   apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
    apply(clarsimp, rule_tac x=1 in exI)+
    apply (force, force intro!: poly_derivatives)
  apply(subst wp_choice, rule conjI)
   apply(rule_tac I="\<lambda>s. s$1 > 0 \<and> s$2 > 0" in wp_change_loopi)
  by (rule wp_loopI, simp_all)


subsection \<open> Potentially overwrite exponential decay \<close>

abbreviation po_exp_dec_f :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=1 then -s$1 else 0)"

abbreviation po_exp_dec_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i=1 then s$1 * exp (- t) else s$i)"

lemma local_flow_exp_flow: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def)
     apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  apply(unfold UNIV_2, simp)
  apply (metis power2_commute real_sqrt_ge_abs1)
  by (auto intro!: poly_derivatives simp: forall_2 vec_eq_iff)

(* x>0 & y>0 -> [{x'=-x}][{x:=x+3;}*@invariant(x>0) ++ y:=x;](x>0&y>0) *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1 > 0 \<and> s$2 > 0\<rceil> \<le> wp (x\<acute>= f & G on {0..t} UNIV @ 0) 
  (wp ((LOOP (1 ::= (\<lambda>s. s$1 + 3)) INV (\<lambda>s. 0 < s$1)) \<union> (2 ::= (\<lambda>s. s$1))) 
  \<lceil>\<lambda>s. s$1 > 0 \<and> s$2 > 0\<rceil>)"
 apply(subst rel_aka.fbox_mult[symmetric])+
  apply(rule rel_aka.fbox_seq_var)+
   apply(subst local_flow.fbox_g_ode_ivl[OF local_flow_exp_flow, where Q="\<lambda>s. s$1 > 0 \<and> s$2 > 0"]; simp)
  apply(subst wp_choice, rule conjI)
   apply(rule_tac I="\<lambda>s. s$1 > 0 \<and> s$2 > 0" in wp_change_loopi)
  by (rule wp_loopI, auto)

no_notation po_exp_dec_f ("f")
        and po_exp_dec_flow ("\<phi>")


subsection \<open> Dynamics: Cascaded \<close>

(* x>0 -> [{x'=5};{x'=2};{x'=x}]x>0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 > 0\<rceil> \<le> 
  wp ((x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then 5 else 0)) & G on {0..t} UNIV @ 0);
      (x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then 2 else 0)) & G on {0..t} UNIV @ 0);
      (x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then s$1 else 0)) & G on {0..t} UNIV @ 0)) 
  \<lceil>\<lambda>s. s$1 > 0\<rceil>"
  apply(simp, subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. s$1 * exp t)"]; simp?)
   apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
    apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
    apply(force, force intro!: poly_derivatives)
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. 2*t+s$1)"]; simp?)
   apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
    apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
    apply(force, force intro!: poly_derivatives)
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. 5*t+s$1)"]; simp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
    apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  apply(force, force intro!: poly_derivatives)
  by auto (smt exp_gt_zero mult_minus_left real_mult_less_iff1)


subsection \<open> Dynamics: Single integrator time \<close>

(* x=0->[{x'=1}]x>=0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 = 0\<rceil> \<le> wp (x\<acute>=(\<lambda>s. (\<chi> i. 1)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. t+s$1)"]; simp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  by (auto intro!: poly_derivatives)


subsection \<open> Dynamics: Single integrator \<close>

(* x>=0 & y>=0 -> [{x'=y}]x>=0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1 \<ge> 0 \<and> s$2 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. if i = 1 then s$2 else 0)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and 
        \<phi>="\<lambda>t s. (\<chi> i. if i = 1 then s$2*t+s$1 else s$i)"]; simp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
    apply(simp add: dist_norm norm_vec_def L2_set_def)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  unfolding UNIV_2 by (auto intro!: poly_derivatives simp: forall_2 vec_eq_iff)


subsection \<open> Dynamics: Double integrator \<close>

(* x>=0 & y>=0 & z>=0 -> [{x'=y,y'=z}]x>=0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$1 \<ge> 0 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. if i = 1 then s$2 else (if i = 2 then s$3 else 0))) & G on {0..t} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and 
        \<phi>="\<lambda>t s. (\<chi> i. if i = 1 then s$3*t\<^sup>2/2 + s$2*t +s$1 else (if i = 2 then s$3*t+s$2 else s$i))"]; simp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  unfolding UNIV_3 by (auto intro!: poly_derivatives simp: forall_3 vec_eq_iff)


subsection \<open> Dynamics: Triple integrator \<close>

lemma new_diff_invs_leq:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> (\<forall>\<tau>\<in>T. \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> (\<forall>\<tau>\<in>T. \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on T"
  shows "diff_invariant (\<lambda>s. \<nu> s \<le> \<mu> s) f T S t\<^sub>0 G"
proof(simp_all add: diff_invariant_eq ivp_sols_def, safe)
  fix X t assume "t \<in> T " and guard: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  assume x_ivp: "D X = (\<lambda>x. f (X x)) on T" "\<nu> (X t\<^sub>0) \<le> \<mu> (X t\<^sub>0)" "X \<in> T \<rightarrow> S"
  {assume "t \<noteq> t\<^sub>0"
    hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> G (X \<tau>) \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
      "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
    using assms(3)[OF x_ivp(1)] assms(4)[OF x_ivp(1)] by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<mu>' (X t) - \<nu>' (X t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<t} \<subseteq> T" "{t\<^sub>0--t} \<subseteq> T"
    using \<open>t \<in> T\<close> Thyp \<open>t \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--t}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain r where "r \<in> {t\<^sub>0<--<t}" and
    "(\<mu> (X t) - \<nu> (X t)) - (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<mu>' (X r) -  \<nu>' (X r))) (t - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>t \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<mu> (X t) - \<nu> (X t) = (t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0))" 
    by force
  have "t > t\<^sub>0 \<Longrightarrow> r > t\<^sub>0 \<and> G (X r)" "\<not> t\<^sub>0 \<le> t \<Longrightarrow> r < t\<^sub>0" "r \<in> T"
    using \<open>r \<in> {t\<^sub>0<--<t}\<close> obs2 guard 
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  moreover have "r > t\<^sub>0 \<Longrightarrow> G (X r) \<Longrightarrow> (\<mu>' (X r) -  \<nu>' (X r)) \<ge> 0" "r < t\<^sub>0 \<Longrightarrow> (\<mu>' (X r) -  \<nu>' (X r)) \<le> 0"
    using primed(1,2)[OF \<open>r \<in> T\<close>] by auto
  ultimately have "(t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) \<ge> 0"
    apply(case_tac "t \<ge> t\<^sub>0")
    by (force, auto simp: split_mult_pos_le)
  hence "(t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) \<ge> 0" 
    using  x_ivp(2) by auto
  hence "\<nu> (X t) \<le> \<mu> (X t)" 
    using mvt by simp}
  thus "\<nu> (X t) \<le> \<mu> (X t)"
    using x_ivp by blast
qed

lemma new_diff_invs_le:
  fixes \<mu>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> (\<forall>\<tau>\<in>T. \<tau> > t\<^sub>0 \<longrightarrow> G (X \<tau>) \<longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>))"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> (\<forall>\<tau>\<in>T. \<tau> < t\<^sub>0 \<longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>))"
    and "\<And>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<Longrightarrow> D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on T"
  shows "diff_invariant (\<lambda>s. \<nu> s < \<mu> s) f T S t\<^sub>0 G"
proof(simp_all add: diff_invariant_eq ivp_sols_def, safe)
  fix X t assume "t \<in> T " and guard: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow>  G (X \<tau>)"
  assume x_ivp: "D X = (\<lambda>x. f (X x)) on T" "\<nu> (X t\<^sub>0) < \<mu> (X t\<^sub>0)" "X \<in> T \<rightarrow> S"
  {assume "t \<noteq> t\<^sub>0"
    hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> G (X \<tau>) \<Longrightarrow> \<mu>' (X \<tau>) \<ge> \<nu>' (X \<tau>)" 
      "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<mu>' (X \<tau>) \<le> \<nu>' (X \<tau>)"
    using assms(3)[OF x_ivp(1)] assms(4)[OF x_ivp(1)] by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<mu>' (X t) - \<nu>' (X t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<t} \<subseteq> T" "{t\<^sub>0--t} \<subseteq> T"
    using \<open>t \<in> T\<close> Thyp \<open>t \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<mu> (X \<tau>) - \<nu> (X \<tau>)) = (\<lambda>\<tau>. \<mu>' (X \<tau>) - \<nu>' (X \<tau>)) on {t\<^sub>0--t}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain r where "r \<in> {t\<^sub>0<--<t}" and
    "(\<mu> (X t) - \<nu> (X t)) - (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<mu>' (X r) -  \<nu>' (X r))) (t - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>t \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<mu> (X t) - \<nu> (X t) = (t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0))" 
    by force
  have "t > t\<^sub>0 \<Longrightarrow> r > t\<^sub>0 \<and> G (X r)" "\<not> t\<^sub>0 \<le> t \<Longrightarrow> r < t\<^sub>0" "r \<in> T"
    using \<open>r \<in> {t\<^sub>0<--<t}\<close> obs2 guard 
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  moreover have "r > t\<^sub>0 \<Longrightarrow> G (X r) \<Longrightarrow> (\<mu>' (X r) -  \<nu>' (X r)) \<ge> 0" "r < t\<^sub>0 \<Longrightarrow> (\<mu>' (X r) -  \<nu>' (X r)) \<le> 0"
    using primed(1,2)[OF \<open>r \<in> T\<close>] by auto
  ultimately have "(t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) \<ge> 0"
    apply(case_tac "t \<ge> t\<^sub>0")
    by (force, auto simp: split_mult_pos_le)
  hence "(t - t\<^sub>0) * (\<mu>' (X r) -  \<nu>' (X r)) + (\<mu> (X t\<^sub>0) - \<nu> (X t\<^sub>0)) > 0" 
    using  x_ivp(2) by auto
  hence "\<nu> (X t) < \<mu> (X t)" 
    using mvt by simp}
  thus "\<nu> (X t) < \<mu> (X t)"
    using x_ivp by blast
qed

abbreviation triple_int_f :: "real^4 \<Rightarrow> real^4" ("f")
  where "f s \<equiv> (\<chi> i. if i = 1 then s$2 else (if i = 2 then s$3 else (if i = 3 then s$4 else (s$4)\<^sup>2)))"

thm derivative_intros(60,61,193)

(* x>=0 & y>=0 & z>=0 & j>=0 -> [{x'=y,y'=z,z'=j,j'=j\<^sup>2}]x>=0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^4. s$1 \<ge> 0 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0 \<and> s$4 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>=f & G on {0..t} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(rule_tac C="\<lambda>s. s$4 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$4 \<ge> 0"])
   apply(rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$4)\<^sup>2" in diff_invariant_leq_rule; simp?)
   apply(force intro!: poly_derivatives simp: forall_4)
  apply(rule_tac C="\<lambda>s. s$3 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$3 \<ge> 0"])
   apply(rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$4)" in new_diff_invs_leq; simp?) 
   apply(force intro!: poly_derivatives simp: forall_4)
  apply(rule_tac C="\<lambda>s. s$2 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$2 \<ge> 0"])
   apply(rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$3)" in new_diff_invs_leq; simp?)
   apply(force intro!: poly_derivatives simp: forall_4)
  apply(rule_tac C="\<lambda>s. s$1 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1 \<ge> 0"])
   apply(rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$2)" in new_diff_invs_leq; simp?)
   apply(force intro!: poly_derivatives simp: forall_4)
  by (rule diff_weak_rule, simp)

no_notation triple_int_f ("f")


subsection \<open> Dynamics: Exponential decay (1) \<close>

(* x>0 -> [{x'=-x}]x>0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 > 0\<rceil> \<le> wp (x\<acute>=(\<lambda>s. (\<chi> i. - s$1)) & G) \<lceil>\<lambda>s. s$1 > 0\<rceil>"
  apply(subst local_flow.wp_g_ode[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. s$1 * exp (- t))"]; simp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  by (auto intro!: poly_derivatives)


subsection \<open> Dynamics: Exponential decay (2) \<close>

(* x>0 -> [{x'=-x+1}]x>0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 > 0\<rceil> \<le> wp (x\<acute>=(\<lambda>s. (\<chi> i. - s$1 + 1)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 > 0\<rceil>"
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. 1 - exp (- t) + s$1 * exp (- t))"]; clarsimp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
     apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  by (auto intro!: poly_derivatives simp: field_simps) (smt exp_gt_zero mult_pos_pos one_less_exp_iff)


subsection \<open> Dynamics: Exponential decay (3) \<close>

(* x>0 & y>0->[{x'=-y*x}]x>0 *)
lemma "0 \<le> t \<Longrightarrow> y > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 > 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. - y * s$1)) & G on UNIV UNIV @ 0) \<lceil>\<lambda>s. s$1 > 0\<rceil>"
  apply(subst local_flow.wp_g_ode[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. s$1 * (exp (-t * y)))"]; clarsimp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
   apply(clarsimp, rule_tac x=1 in exI)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x="y" in exI)
   apply (metis abs_mult abs_of_pos dist_commute dist_real_def less_eq_real_def vector_space_over_itself.scale_right_diff_distrib)
  by (auto intro!: poly_derivatives simp: field_simps)


subsection \<open> Dynamics: Exponential growth (1) \<close>

(* x>=0 -> [{x'=x}]x>=0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. s$1)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(subst local_flow.fbox_g_ode_ivl[where T=UNIV and \<phi>="\<lambda>t s. (\<chi> i. s$1 * exp t)"]; clarsimp?)
  apply(unfold_locales; (simp add: local_lipschitz_def lipschitz_on_def vec_eq_iff)?)
   apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  by (auto intro!: poly_derivatives)


subsection \<open> Dynamics: Exponential growth (2) \<close>

lemma in_ivp_sols_subset:
  "T' \<subseteq> T \<Longrightarrow> X \<in> Sols f T S 0 s \<Longrightarrow> X \<in> Sols f T' S 0 s "
  apply(rule ivp_solsI)
  using ivp_solsD(1,2) has_vderiv_on_subset apply blast+
  by (drule ivp_solsD(3)) auto

lemma vderiv_cnst_div_intro[poly_derivatives]:
  assumes "\<forall>t\<in>T. f t \<noteq> (0::real)" and "D f = f' on T" and "g = (\<lambda>t. - a * f' t / (f t)^2)"
  shows "D (\<lambda>t. a/(f t)) = g on T"
  apply(rule has_vderiv_on_compose_eq[where g=f and f="\<lambda>t. a/t" and f'="\<lambda>t. - a/t^2", OF _ assms(2)])
   unfolding has_vderiv_on_def has_vector_derivative_def assms apply clarsimp
  using assms(1) by (auto intro!: derivative_eq_intros simp: fun_eq_iff power2_eq_square)

(* x>=0 & y>=0 -> [{x'=y, y'=y\<^sup>2}]x>=0 *)
lemma "\<lceil>\<lambda>s::real^2. s$1 \<ge> 0 \<and> s$2 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. if i=1 then s$2 else (s$2)\<^sup>2)) & G on {0..} {s. s$2 < 0} @ 0) \<lceil>\<lambda>s. s$1 \<ge> 0\<rceil>"
  apply(rule_tac C="\<lambda>s. s$2 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$2 \<ge> 0"], rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$2)^2" in new_diff_invs_leq; (simp add: forall_2)?)
  apply(rule_tac C="\<lambda>s. s$1 \<ge> 0" in diff_cut_rule, simp_all)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1 \<ge> 0"])
   apply(rule wp_g_odei; simp?)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$2)" in new_diff_invs_leq; (simp add: forall_2)?)
  by (rule diff_weak_rule, simp)


subsection \<open> Dynamics: Exponential growth (4) \<close> (* sic *)

(* x>0 -> [{x'=x^x}]x>0 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 > 0\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. (s$1)\<^sup>2)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1 > 0\<rceil>"
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1 > 0"], rule wp_g_odei, simp_all)
  by (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$1)\<^sup>2" in diff_invariant_rules(3); simp?)


subsection \<open> Dynamics: Exponential growth (5) \<close>

(* x>=1 -> [{x'=x\<^sup>2+2*x^4}]x^3>=x\<^sup>2 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^1. s$1 \<ge> 1\<rceil> \<le> 
  wp (x\<acute>=(\<lambda>s. (\<chi> i. (s$1)\<^sup>2 + 2 \<cdot> (s$1)^4)) & G on {0..t} UNIV @ 0) \<lceil>\<lambda>s. s$1^3 \<ge>  (s$1)\<^sup>2\<rceil>"
  apply(rule_tac C="\<lambda>s. s$1 \<ge> 1" in diff_cut_rule; simp?)
   apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (s$1)\<^sup>2 + 2 \<cdot> s$1 ^ 4" in diff_invariant_rules(2); simp?)
  apply(force intro!: poly_derivatives)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1^3 \<ge>  (s$1)\<^sup>2 "], rule wp_g_odei, simp_all add: power_increasing)
  apply (rule_tac \<nu>'="\<lambda>s. 2 * s$1 * ((s$1)\<^sup>2 + 2 \<cdot> (s$1)^ 4)"
              and \<mu>'="\<lambda>s. 3 * (s$1)\<^sup>2 * ((s$1)\<^sup>2 + 2 \<cdot> (s$1)^4)" in new_diff_invs_leq; clarsimp?)
  apply(auto intro!: poly_derivatives simp: field_simps semiring_normalization_rules(27,28))
  apply(subgoal_tac "X \<tau> $ 1 \<ge> 1")
   apply(subgoal_tac "2 + 4 \<cdot> (X \<tau>)$1 ^ 2 \<le> 3 \<cdot> (X \<tau>)$1 + 6 \<cdot> (X \<tau>)$1 ^ 3")
  apply (smt One_nat_def numerals(1) one_le_power power.simps(2) power_0 power_add_numeral power_less_power_Suc power_one_right semiring_norm(2) semiring_norm(4) semiring_norm(5))
  apply (smt numeral_One one_le_power power_add_numeral power_commutes power_le_one power_less_power_Suc power_one_right semiring_norm(5))
  by simp


subsection \<open> Dynamics: Rotational dynamics (1) \<close>

(* x\<^sup>2+y\<^sup>2=1 -> [{x'=-y, y'=x}]x\<^sup>2+y\<^sup>2=1 *)
lemma "\<lceil>\<lambda>s::real^2. (s$1)\<^sup>2 + (s$2)\<^sup>2 = 1\<rceil> \<le> wp (x\<acute>= (\<lambda>s.(\<chi> i. if i = 1 then - s$2 else s$1)) & G) 
  \<lceil>\<lambda>s. (s$1)\<^sup>2 + (s$2)\<^sup>2 = 1\<rceil>"
  by (auto intro!: poly_derivatives diff_invariant_rules)


subsection \<open> Dynamics: Rotational dynamics (2) \<close>

abbreviation rot_dyn2_mtx :: "3 sq_mtx" ("A")
  where "A \<equiv> mtx  
   ([0,  -1, 0] # 
    [0,  0,  1] #
    [0, -1,  0] # [])"

abbreviation rot_dyn2_f :: "real^3 \<Rightarrow> real^3" ("f")
  where "f s \<equiv> (\<chi> i. if i = 1 then - s$2 else (if i = 2 then s$3 else - s$2))"

lemma rot_dyn2_f_linear: "f s = A *\<^sub>V s "
  apply(simp add: vec_eq_iff sq_mtx_vec_mult_eq)
  unfolding UNIV_3 using exhaust_3 by force

abbreviation rot_dyn2_flow :: "real \<Rightarrow> real^3 \<Rightarrow> real^3" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 1 then - s$3 + s$1 + s$3 * cos t - s$2 * sin t
  else (if i = 2 then s$3 * sin t + s$2 * cos t else s$3 * cos t - s$2 * sin t))"

lemma mtx_circ_flow_eq: "exp (t *\<^sub>R A) *\<^sub>V s = \<phi> t s"
  apply(rule local_flow.eq_solution[OF local_flow_sq_mtx_linear, symmetric])
    apply(rule ivp_solsI, simp_all add: sq_mtx_vec_mult_eq vec_eq_iff)
  unfolding UNIV_3 using exhaust_3
  by (force intro!: poly_derivatives simp: matrix_vector_mult_def)+

(* x\<^sup>2+y\<^sup>2=1 & e=x -> [{x'=-y, y'=e, e'=-y}](x\<^sup>2+y\<^sup>2=1 & e=x) *)
lemma "\<lceil>\<lambda>s::real^3. (s$1)\<^sup>2 + (s$2)\<^sup>2 = 1 \<and> s$3 = s$1\<rceil> \<le> wp (x\<acute>= f & G) 
  \<lceil>\<lambda>s. (s$1)\<^sup>2 + (s$2)\<^sup>2 = 1 \<and> s$3 = s$1\<rceil>"
  apply(subst rot_dyn2_f_linear, subst local_flow.wp_g_ode[OF local_flow_sq_mtx_linear])
  unfolding mtx_circ_flow_eq by auto

no_notation rot_dyn2_f ("f")
        and rot_dyn2_mtx ("A")
        and rot_dyn2_flow ("\<phi>")


subsection \<open> Dynamics: Rotational dynamics (3) \<close>

(* d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1 -> 
  [{x1'=d1, x2'=d2, d1'=-w*d2, d2'=w*d1}](d1\<^sup>2+d2\<^sup>2=w\<^sup>2*p\<^sup>2 & d1=-w*x2 & d2=w*x1)*)
lemma "\<lceil>\<lambda>s::real^4. (s$3)\<^sup>2 + (s$4)\<^sup>2 = w\<^sup>2 \<cdot> p\<^sup>2 \<and> s$3 = - w \<cdot> s$2 \<and> s$4 = w \<cdot> s$1\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then s$3 else (if i=2 then s$4 else (if i = 3 then - w * s$4 else w * s$3)))) & G) 
  \<lceil>\<lambda>s. (s$3)\<^sup>2 + (s$4)\<^sup>2 = w\<^sup>2*p\<^sup>2 \<and> s$3 = - w * s$2 \<and> s$4= w * s$1\<rceil>"
  by (auto intro!: diff_invariant_rules poly_derivatives)


subsection \<open> Dynamics: Spiral to equilibrium \<close>

(* w>=0 & x=0 & y=3 -> [{x'=y, y'=-w\<^sup>2*x-2*w*y}]w\<^sup>2*x\<^sup>2+y\<^sup>2<=9 *)
lemma "\<lceil>\<lambda>s::real^3. (s$3) \<ge> 0 \<and> s$1=0 \<and> s$2=3\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then s$2 else (if i=2 then - (s$3)\<^sup>2*(s$1) - 2*(s$3)*(s$2) else 0))) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. (s$3)\<^sup>2*(s$1)\<^sup>2 + (s$2)\<^sup>2 \<le> 9\<rceil>"
  apply(rule_tac C="\<lambda>s. s$3 \<ge> 0" in diff_cut_rule; simp?)
    apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$3 \<ge> 0"], rule wp_g_odei, simp_all)
  apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in diff_invariant_rules(2); (simp add: forall_3)?)
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. (s$3)\<^sup>2*(s$1)\<^sup>2 + (s$2)\<^sup>2 \<le> 9"], rule wp_g_odei, simp_all add: power_increasing)
  apply(rule_tac \<nu>'="\<lambda>s. 2 * (s$3)\<^sup>2 * (s$1) * (s$2) + 2 * (s$2) * (- (s$3)\<^sup>2*(s$1) - 2*(s$3)*(s$2))" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all)
  by (auto intro!: poly_derivatives simp: forall_3 field_simps) (simp add: mult.assoc[symmetric] power2_eq_square)


subsection \<open> Dynamics: Open cases \<close>

lemma wp_conj_inv: "\<lceil>I2\<rceil> \<le> wp R \<lceil>I2\<rceil> \<Longrightarrow> \<lceil>I1\<rceil> \<le> wp R \<lceil>I1\<rceil> \<Longrightarrow>  \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> wp R \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> "
  apply(subst p2r_simps(3)[symmetric])+
  apply(subgoal_tac "\<lceil>I1\<rceil> ; \<lceil>I2\<rceil> = rel_aka.ads_d \<lceil>I1\<rceil> ; rel_aka.ads_d \<lceil>I2\<rceil>")
  by (erule ssubst, rule rel_aka.mult_inv, simp_all)

lemma wp_disj_inv: "\<lceil>I2\<rceil> \<le> wp R \<lceil>I2\<rceil> \<Longrightarrow> \<lceil>I1\<rceil> \<le> wp R \<lceil>I1\<rceil> \<Longrightarrow>  \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> wp R \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> "
  apply(subst p2r_simps(4)[symmetric])+
  apply(subgoal_tac "\<lceil>I1\<rceil> \<union> \<lceil>I2\<rceil> = rel_aka.ads_d \<lceil>I1\<rceil> \<union> rel_aka.ads_d \<lceil>I2\<rceil>")
  by (erule ssubst, rule rel_aka.plus_inv, simp_all)

lemma has_vderiv_mono_test:
  assumes T_hyp: "is_interval T" 
    and d_hyp: "D f = f' on T"
    and xy_hyp: "x\<in>T" "y\<in>T" "x \<le> y" 
  shows "\<forall>x\<in>T. (0::real) \<le> f' x \<Longrightarrow> f x \<le> f y"
    and "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
proof-
  have "{x..y} \<subseteq> T"
    using T_hyp xy_hyp by (meson atLeastAtMost_iff mem_is_interval_1_I subsetI) 
  hence "D f = f' on {x..y}"
    using has_vderiv_on_subset[OF d_hyp(1)] by blast
  hence "(\<And>t. x \<le> t \<Longrightarrow> t \<le> y \<Longrightarrow> D f \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f' t) at t within {x..y})"
    unfolding has_vderiv_on_def has_vector_derivative_def by auto
  then obtain c where c_hyp: "c \<in> {x..y} \<and> f y - f x = (y - x) *\<^sub>R f' c"
    using mvt_very_simple[OF xy_hyp(3), of f "(\<lambda>t \<tau>. \<tau> *\<^sub>R f' t)"] by blast
  hence mvt_hyp: "f x = f y - f' c * (y - x)"
    by (simp add: mult.commute)
  also have "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> ... \<le> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by auto
  finally show "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> f x \<le> f y" .
  have "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f y - f' c * (y - x) \<ge> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by (auto simp: mult_le_0_iff)
  thus "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
    using mvt_hyp by auto
qed

lemma continuous_on_ge_ball_ge: 
  "continuous_on T f \<Longrightarrow> x \<in> T \<Longrightarrow> f x > (k::real) \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>y\<in>ball x \<epsilon> \<inter> T. f y > k"
  unfolding continuous_on_iff apply(erule_tac x=x in ballE; clarsimp?)
  apply(erule_tac x="f x - k" in allE, clarsimp simp: dist_norm)
  apply(rename_tac \<delta>, rule_tac x=\<delta> in exI, clarsimp)
  apply(erule_tac x=y in ballE; clarsimp?)
  by (subst (asm) abs_le_eq, simp_all add: dist_commute)

lemma current_vderiv_ge_always_ge:
  fixes c::real
  assumes init: "c < x t\<^sub>0" and ode: "D x = x' on {t\<^sub>0..}" 
    and dhyp: "x' = (\<lambda>t. g (x t))" "\<forall>x\<ge>c. g x \<ge> 0"
  shows "\<forall>t\<ge>t\<^sub>0. x t > c"
proof-
  have cont: "continuous_on {t\<^sub>0..} x"
    using vderiv_on_continuous_on[OF ode] .
  {assume "\<exists>t\<ge>t\<^sub>0. x t \<le> c"
    hence inf: "{t. t > t\<^sub>0 \<and> x t \<le> c} \<noteq> {}" "bdd_below {t. t > t\<^sub>0 \<and> x t \<le> c}"
      using init less_eq_real_def unfolding bdd_below_def by force (rule_tac x=t\<^sub>0 in exI, simp)
    define t\<^sub>1 where t1_hyp: "t\<^sub>1 = Inf {t. t > t\<^sub>0 \<and> x t \<le> c}"
    hence "t\<^sub>0 \<le> t\<^sub>1"  
      using le_cInf_iff[OF inf, of t\<^sub>0] by auto
    have "x t\<^sub>1 \<ge> c"
    proof-
      {assume "x t\<^sub>1 < c"
        hence obs: "x t\<^sub>1 \<le> c" "x t\<^sub>0 \<ge> c" "t\<^sub>1 \<noteq> t\<^sub>0"
          using init by auto
        hence "t\<^sub>1 > t\<^sub>0"
          using \<open>t\<^sub>0 \<le> t\<^sub>1\<close> by auto
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k \<le> t\<^sub>1 \<and> x k = c"
          using IVT2'[of "\<lambda>t. x t", OF obs(1,2) _ continuous_on_subset[OF cont]] by auto
        hence "t\<^sub>0 < k" "k < t\<^sub>1"
          using \<open>x t\<^sub>1 < c\<close> less_eq_real_def init by auto
        also have "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp calculation unfolding t1_hyp by auto
        ultimately have False
          by simp}
      thus "x t\<^sub>1 \<ge> c"
        by fastforce
    qed
    hence obs: "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
    proof-
      {assume "\<exists>t\<in>{t\<^sub>0..<t\<^sub>1}. x t \<le> c"
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k < t\<^sub>1 \<and> x k \<le> c"
          by auto
        hence "k > t\<^sub>0"
          using \<open>x t\<^sub>0 > c\<close> less_eq_real_def by auto
        hence "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp unfolding t1_hyp by auto
        hence "False"
          using k2_hyp by auto}
      thus "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
        by force
    qed
    hence "\<forall>t\<in>{t\<^sub>0..t\<^sub>1}. x' t \<ge> 0"
      using \<open>x t\<^sub>1 \<ge> c\<close> dhyp(2) less_eq_real_def 
      unfolding dhyp by (metis atLeastAtMost_iff atLeastLessThan_iff) 
    hence "x t\<^sub>0 \<le> x t\<^sub>1"
      apply(rule_tac f="\<lambda>t. x t" and T="{t\<^sub>0..t\<^sub>1}" in has_vderiv_mono_test(1); clarsimp)
      using has_vderiv_on_subset[OF ode] apply force
      using \<open>t\<^sub>0  \<le> t\<^sub>1\<close>  by (auto simp: less_eq_real_def)
    hence "c < x t\<^sub>1"
      using \<open>x t\<^sub>1 \<ge> c\<close> init by auto
    then obtain \<epsilon> where eps_hyp: "\<epsilon> > 0 \<and> (\<forall>t\<in>ball t\<^sub>1 \<epsilon> \<inter> {t\<^sub>0..}. c < x t)"
      using continuous_on_ge_ball_ge[of _ "\<lambda>t. x t", OF cont _ \<open>c < x t\<^sub>1\<close>] \<open>t\<^sub>0  \<le> t\<^sub>1\<close> by auto
    hence "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1+\<epsilon>}. c < x t"
      using obs \<open>t\<^sub>0 \<le> t\<^sub>1\<close> ball_eq_greaterThanLessThan by auto
    hence "\<forall>t\<in>{t. t > t\<^sub>0 \<and> x t \<le> c}. t\<^sub>1+\<epsilon> \<le> t"
      by (metis (mono_tags, lifting) atLeastLessThan_iff less_eq_real_def mem_Collect_eq not_le)
    hence "t\<^sub>1+\<epsilon> \<le> t\<^sub>1"
      using le_cInf_iff[OF inf] unfolding t1_hyp by simp
    hence False
      using eps_hyp by auto}
  thus "\<forall>t\<ge>t\<^sub>0. c < x t"
    by fastforce
qed

(* x^3>5 & y>2 -> [{x'=x^3+x^4, y'=5*y+y^2}](x^3>5 & y>2) *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1^3>5 \<and> s$2>2\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then s$1^3 + s$1^4 else 5 * s$2 + s$2^2)) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1^3>5 \<and> s$2>2\<rceil>"
  apply(rule wp_conj_inv, simp_all add: diff_invariant_eq ivp_sols_def forall_2; clarsimp)
   apply(frule_tac x="\<lambda>t. X t $ 2" in current_vderiv_ge_always_ge)
      apply(force, force, force simp: add_nonneg_pos, simp)
  apply(frule_tac x="\<lambda>t. X t $ 1 ^ 3" and g="\<lambda>t. 3 * t^2 + 3 * (root 3 t)^5" in current_vderiv_ge_always_ge)
     apply(rule poly_derivatives, simp, assumption, simp)
  using real_root_gt_zero[of 3] by (auto simp: field_simps odd_real_root_power_cancel add_nonneg_pos)


subsection \<open> Dynamics: Closed cases \<close>

(* x>=1 & y=10 & z=-2 -> [{x'=y, y'=z+y^2-y & y>=0}](x>=1 & y>=0) *)
lemma "z = - 2 \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$1 \<ge> 1 \<and> s$2 = 10\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then s$2 else z + (s$2)^2 - s$2)) & (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 \<ge> 1 \<and> s$2 \<ge> 0\<rceil>"
  apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$1 \<ge> 1 \<and> s$2 \<ge> 0"], rule wp_g_odei, simp_all)
  apply(rule diff_invariant_rules)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$2" in new_diff_invs_leq, simp_all add: diff_invariant_eq)
  by (force intro!: poly_derivatives)


subsection \<open> Dynamics: Conserved quantity \<close>

lemma dyn_cons_qty_arith: "(36::real) \<cdot> (x1\<^sup>2 \<cdot> (x1 \<cdot> x2 ^ 3)) - 
  (- (24 \<cdot> (x1\<^sup>2 \<cdot> x2) \<cdot> x1 ^ 3 \<cdot> (x2)\<^sup>2) - 12 \<cdot> (x1\<^sup>2 \<cdot> x2) \<cdot> x1 \<cdot> x2 ^ 4) - 
  36 \<cdot> (x1\<^sup>2 \<cdot> (x2 \<cdot> x1)) \<cdot> (x2)\<^sup>2 - 12 \<cdot> (x1\<^sup>2 \<cdot> (x1 \<cdot> x2 ^ 5)) = 24 \<cdot> (x1 ^ 5 \<cdot> x2 ^ 3)" 
  (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
proof-
  have eq1: "?t1 = ?t4"
    by (simp add: power2_eq_square power3_eq_cube)
  have eq2: "- (- ?t2 - ?t3) = (?t6 + ?t3)"
    by (auto simp: field_simps semiring_normalization_rules(27))
  have eq3: "?t3 = ?t5"
    by (auto simp: field_simps semiring_normalization_rules(27))
  show "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6"
    unfolding eq1 eq2 eq3 by (simp add: field_simps semiring_normalization_rules(27))
qed

(* x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c ->
    [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] 
   x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^2. (s$1)^4*(s$2)^2+(s$1)^2*(s$2)^4-3*(s$1)^2*(s$2)^2 + 1 \<le> c\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then 2*(s$1)^4*(s$2)+4*(s$1)^2*(s$2)^3-6*(s$1)^2*(s$2) 
    else -4*(s$1)^3*(s$2)^2-2*(s$1)*(s$2)^4+6*(s$1)*(s$2)^2)) & G on {0..t} UNIV @ 0) 
  \<lceil>\<lambda>s. (s$1)^4*(s$2)^2+(s$1)^2*(s$2)^4-3*(s$1)^2*(s$2)^2 + 1 \<le> c\<rceil>"
  thm diff_invariant_rules(2)
  apply(simp, rule_tac \<mu>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 0" in diff_invariant_rules(2); clarsimp simp: forall_2)
  apply(intro poly_derivatives; (assumption)?, (rule poly_derivatives)?)
  apply force+
  apply(clarsimp simp: algebra_simps(17,18,19,20) semiring_normalization_rules(27,28))
  by (auto simp: dyn_cons_qty_arith)


subsection \<open> Dynamics: Darboux equality \<close>

lemma mult_abs_right_mono: "a < b \<Longrightarrow> a * \<bar>c\<bar> \<le> b * \<bar>c\<bar>" for c::real
  by (simp add: mult_right_mono)

lemma local_lipschitz_first_order_linear:
  fixes c::"real \<Rightarrow> real"
  assumes "continuous_on T c"
  shows "local_lipschitz T UNIV (\<lambda>t. (*) (c t))"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix x t::real assume "t \<in> T"
  then obtain \<delta> where d_hyp: "\<delta> > 0 \<and> (\<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>)"
    using assms unfolding continuous_on_iff 
    apply(erule_tac x=t in ballE, erule_tac x="max 1 (\<bar>c t\<bar>)" in allE; clarsimp)
    by (metis dist_norm less_max_iff_disj real_norm_def zero_less_one)
  {fix \<tau> x\<^sub>1 x\<^sub>2 
    assume "\<tau> \<in> cball t (\<delta>/2) \<inter> T" "x\<^sub>1 \<in> cball x (\<delta>/2)" "x\<^sub>2 \<in> cball x (\<delta>/2)" 
    hence "\<bar>\<tau> - t\<bar> < \<delta>" "\<tau> \<in> T"
      by (auto simp: dist_norm, smt d_hyp)
    hence "\<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>"
      using d_hyp by auto
    hence "- (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) < c \<tau> \<and> c \<tau> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (auto simp: abs_le_eq)
    hence obs: "\<bar>c \<tau>\<bar> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (simp add: abs_le_eq)
    have "\<bar>c \<tau> \<cdot> x\<^sub>1 - c \<tau> \<cdot> x\<^sub>2\<bar> = \<bar>c \<tau>\<bar> \<cdot> \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      by (metis abs_mult left_diff_distrib mult.commute)
    also have "... \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) \<cdot> \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      using mult_abs_right_mono[OF obs] by blast
    finally have "\<bar>c \<tau> \<cdot> x\<^sub>1 - c \<tau> \<cdot> x\<^sub>2\<bar> \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) \<cdot> \<bar>x\<^sub>1 - x\<^sub>2\<bar>" .}
  hence "\<exists>L. \<forall>t\<in>cball t (\<delta>/2) \<inter> T. 0 \<le> L \<and>
    (\<forall>x\<^sub>1\<in>cball x (\<delta>/2). \<forall>x\<^sub>2\<in>cball x (\<delta>/2). \<bar>c t \<cdot> x\<^sub>1 - c t \<cdot> x\<^sub>2\<bar> \<le> L \<cdot> \<bar>x\<^sub>1 - x\<^sub>2\<bar>)"
    by (rule_tac x="max 1 \<bar>c t\<bar> + \<bar>c t\<bar>" in exI, clarsimp simp: dist_norm)
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. 0 \<le> L \<and> 
    (\<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>c t \<cdot> xa - c t \<cdot> y\<bar> \<le> L \<cdot> \<bar>xa - y\<bar>)"
    apply(rule_tac x="\<delta>/2" in exI) 
    using d_hyp by auto
qed

lemma picard_lindeloef_first_order_linear: "t\<^sub>0 \<in> T \<Longrightarrow> open T \<Longrightarrow> is_interval T \<Longrightarrow> 
  continuous_on T c \<Longrightarrow> picard_lindeloef (\<lambda>t x::real. c t * x) T UNIV t\<^sub>0"
  apply(unfold_locales; clarsimp?)
   apply(intro continuous_intros, assumption)
  by (rule local_lipschitz_first_order_linear)

(* x+z=0 -> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z *)
lemma "\<lceil>\<lambda>s::real^2. s$1 + s$2 = 0\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then A*(s$1)^2+B*(s$1) else A*(s$2)*(s$1)+B*(s$2))) & G on UNIV UNIV @ 0) 
  \<lceil>\<lambda>s. 0 = - s$1 - s$2\<rceil>"
proof-
  have key: "diff_invariant (\<lambda>s. s $ 1 + s $ 2 = 0)
     (\<lambda>s. \<chi> i. if i = 1 then A*(s$1)^2+B*(s$1) else A*(s$2)*(s$1)+B*(s$2)) UNIV UNIV 0 G"
  proof(clarsimp simp: diff_invariant_eq ivp_sols_def forall_2)
    fix X::"real\<Rightarrow>real^2" and t::real
    let "?c" = "(\<lambda>t.  X t $ 1 + X t $ 2)"
    assume init: "?c 0 = 0"
      and D1: "D (\<lambda>t. X t $ 1) = (\<lambda>t. A \<cdot> (X t $ 1)\<^sup>2 + B \<cdot> X t $ 1) on UNIV"
      and D2: "D (\<lambda>t. X t $ 2) = (\<lambda>t. A \<cdot> X t $ 2 \<cdot> X t $ 1 + B \<cdot> X t $ 2) on UNIV"
    hence "D ?c = (\<lambda>t. ?c t * (A \<cdot> (X t $ 1) + B)) on UNIV"
      by (auto intro!: poly_derivatives simp: field_simps power2_eq_square)
    hence "D ?c = (\<lambda>t. (A \<cdot> X t $ 1 + B) \<cdot> (X t $ 1 + X t $ 2)) on {0--t}"
      using has_vderiv_on_subset[OF _ subset_UNIV[of "{0--t}"]] by (simp add: mult.commute)
    moreover have "continuous_on UNIV (\<lambda>t. A \<cdot> (X t $ 1) + B)"
      apply(rule vderiv_on_continuous_on)
      using D1 by (auto intro!: poly_derivatives simp: field_simps power2_eq_square)
    moreover have "D (\<lambda>t. 0) = (\<lambda>t. (A \<cdot> X t $ 1 + B) \<cdot> 0) on {0--t}"
      by (auto intro!: poly_derivatives)
    moreover note picard_lindeloef.unique_solution[OF 
        picard_lindeloef_first_order_linear[OF _ _ _ calculation(2)] this _ _ _ calculation(1)]
    ultimately show "X t $ 1 + X t $ 2 = 0"
      using init by auto
  qed
  show ?thesis
    apply(subgoal_tac "(\<lambda>s. 0 = - s$1 - s$2) = (\<lambda>s. s$1 + s$2 = 0)", erule ssubst)
    using key by auto
qed


subsection \<open> Dynamics: Fractional Darboux equality \<close> (*N 30 *)

lemma vderiv_div_intro[poly_derivatives]:
  assumes "\<forall>t\<in>T. g t \<noteq> (0::real)" and "D f = f' on T"and "D g = g' on T" 
    and "h = (\<lambda>t. (f' t \<cdot> g t - f t \<cdot> (g' t)) / (g t)^2)"
  shows "D (\<lambda>t. (f t)/(g t)) = h on T"
  apply(subgoal_tac "(\<lambda>t. (f t)/(g t)) = (\<lambda>t. (f t) \<cdot> (1/(g t)))")
   apply(erule ssubst, rule poly_derivatives, rule assms(2))
    apply(rule poly_derivatives, rule assms(1), rule assms(3), force)
  using assms by (auto simp: field_simps semiring_normalization_rules(27))

(* x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0 *)
(* x' + z' = (A*y+B*x)/z^2 + (A*x+B)/z = (A*y+B*x+A*x*z+B*z)/z^2 = (x*(A*x+B)+z*(A*x+B))/z^2 *)
lemma "0 \<le> t \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$1 + s$3 = 0\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. if i=1 then (A*(s$2)+B*(s$1))/(s$3)\<^sup>2 else (if i = 3 then (A*(s$1)+B)/s$3 else 0))) & (\<lambda>s. (s$2) = (s$1)^2 \<and> (s$3)^2 > 0) on UNIV UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 + s$3 = 0\<rceil>"
  oops


subsection \<open> Dynamics: Darboux inequality \<close> (*N 31 *)

(* x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0 *)
lemma "\<lceil>\<lambda>s::real^3. s$1 + s$3 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then (s$1)^2 else (if i=3 then (s$3)*(s$1)+(s$2) else 0)) & (\<lambda>s. s$2 = (s$1)^2) on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 + s$3 \<ge> 0\<rceil>"
  oops


subsection \<open> Dynamics: Bifurcation \<close>

lemma picard_lindeloef_dyn_bif:
  "continuous_on T (g::real \<Rightarrow> real) \<Longrightarrow> t\<^sub>0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> picard_lindeloef (\<lambda>t \<tau>::real. r + \<tau>^2) T UNIV t\<^sub>0"
proof(unfold_locales; clarsimp simp: dist_norm local_lipschitz_def lipschitz_on_def)
  fix x t::real
  {fix x1 and x2
    assume "x1 \<in>cball x 1" and "x2 \<in>cball x 1"
    hence leq: "\<bar>x - x1\<bar> \<le> 1" "\<bar>x - x2\<bar> \<le> 1"
      by (auto simp: dist_norm)
    have "\<bar>x1 + x2\<bar> = \<bar>x1 - x + x2 - x + 2 * x\<bar>"
      by simp
    also have "... \<le> \<bar>x1 - x\<bar> + \<bar>x2 - x\<bar> + 2 * \<bar>x\<bar>"
      using abs_triangle_ineq by auto
    also have "... \<le> 2 * (1 + \<bar>x\<bar>)"
      using leq by auto
    finally have obs: "\<bar>x1 + x2\<bar> \<le> 2 * (1 + \<bar>x\<bar>)" .
    also have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> = \<bar>x1 + x2\<bar>*\<bar>x1 - x2\<bar>"
      by (metis abs_mult power2_eq_square square_diff_square_factored)
    ultimately have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> \<le> (2 * (1 + \<bar>x\<bar>)) * \<bar>x1 - x2\<bar>"
      by (metis abs_ge_zero mult_right_mono)}
  thus "\<exists>u>0. (\<exists>\<tau>. \<bar>t - \<tau>\<bar> \<le> u \<and> \<tau> \<in> T) \<longrightarrow> (\<exists>L\<ge>0. \<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L \<cdot> \<bar>xa - y\<bar>)"
    by (rule_tac x=1 in exI, clarsimp, rule_tac x="2 \<cdot> (1 + \<bar>x\<bar>)" in exI, auto)
qed

(* r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f) *)
lemma "r \<le> 0 \<Longrightarrow> \<exists>c. \<lceil>\<lambda>s::real^1. s$1 = c\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. (\<chi> i. r + (s$1)^2)) & G on UNIV UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 = c\<rceil>"
proof(rule_tac x="sqrt \<bar>r\<bar>" in exI, clarsimp simp: diff_invariant_eq ivp_sols_def)
  fix X::"real\<Rightarrow>real^1" and t::real
  assume init: "X 0 $ 1 = sqrt (- r)" and "r \<le> 0"
     and D1: "D (\<lambda>x. X x $ 1) = (\<lambda>x. r + (X x $ 1)\<^sup>2) on UNIV"
  hence "D (\<lambda>x. X x $ 1) = (\<lambda>x. r + (X x $ 1)\<^sup>2) on {0--t}"
    using has_vderiv_on_subset by blast
  moreover have "continuous_on UNIV (\<lambda>t. X t $ 1)"
    apply(rule vderiv_on_continuous_on)
    using D1 by assumption
  moreover have "D (\<lambda>t. sqrt (- r)) = (\<lambda>t. r + (sqrt (- r))\<^sup>2) on {0--t}"
    apply(subgoal_tac "(\<lambda>t. r + (sqrt (- r))\<^sup>2) = (\<lambda>t. 0)")
     apply(erule ssubst, rule poly_derivatives)
    using \<open>r \<le> 0\<close> by auto
  moreover note picard_lindeloef.unique_solution[OF 
      picard_lindeloef_dyn_bif[OF calculation(2)] calculation(1) init _, where Y="\<lambda>t. sqrt (- r)"]
  ultimately show "X t $ 1 = sqrt (- r)"
    using \<open>r \<le> 0\<close> by auto
qed


subsection \<open> Dynamics: Parametric switching between two different damped oscillators \<close> (*N 33 *)

lemma wp_test[simp]: "wp \<lceil>P\<rceil> \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<longrightarrow> Q s\<rceil>"
  by (subst wp_rel, simp add: p2r_def)

lemma exhaust_5:
  fixes x :: 5
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 5" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4" by arith
  then show ?case by auto
qed

lemma forall_5: "(\<forall>i::5. P i) = (P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5)"
  by (metis exhaust_5)

abbreviation switch_two_osc_f :: "real^5 \<Rightarrow> real^5" ("f")
  where "f s \<equiv> (\<chi> i. if i = 4 then s$5 else (if i = 5 then - (s$3^2) * s$4 - 2 * s$2 * s$3 * s$5 else 0))"

(*     w>=0 & d>=0
  & -2<=a&a<=2
  & b^2>=1/3
  & w^2*x^2+y^2 <= c
->
  [{
    {x'=y, y'=-w^2*x-2*d*w*y};
    {  { ?(x=y*a); w:=2*w; d:=d/2; c := c * ((2*w)^2+1^2) / (w^2+1^2); }
    ++ { ?(x=y*b); w:=w/2; d:=2*d; c := c * (w^2+1^2) / ((2*w^2)+1^2); }
    ++ { ?true; } }
   }*@invariant(w^2*x^2+y^2<=c&d>=0&w>=0)
  ] w^2*x^2+y^2 <= c *)

declare wp_diff_inv [simp del]

lemma "- 2 \<le> a  \<Longrightarrow> a \<le> 2 \<Longrightarrow> b^2 \<ge> 1/3 \<Longrightarrow> 
\<lceil>\<lambda>s. s$3 \<ge> 0 \<and> s$2 \<ge> 0 \<and> s$3^2 * s$4^2 + s$5^2 \<le> s$1\<rceil> \<le> wp
  (LOOP 
    ((x\<acute>= f & (\<lambda>s. True) on {0..} UNIV @ 0);
    ((\<lceil>\<lambda>s. s$4 = s$5*a\<rceil>; (3 ::= (\<lambda>s. 2 * s$3)); (2 ::= (\<lambda>s. s$2/2)); (1 ::= (\<lambda>s. s$1 * ((2 \<cdot> s$3)\<^sup>2 + 1)/(s$3^2 + 1)))) \<union>
    (\<lceil>\<lambda>s. s$4 = s$5*b\<rceil>; (3 ::= (\<lambda>s. s$3/2)); (2 ::= (\<lambda>s. 2 * s$2)); (1 ::= (\<lambda>s. s$1 * ((s$3)\<^sup>2 + 1)/(2 * (s$3^2) + 1)))) \<union>
    \<lceil>\<lambda>s. True\<rceil>)) 
  INV (\<lambda>s. s$3^2 * s$4^2 + s$5^2 \<le> s$1 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0))
  \<lceil>\<lambda>s. s$3^2 * s$4^2 + s$5^2 \<le> s$1\<rceil>"
  apply(rule_tac I="\<lambda>s. s$3^2 * s$4^2 + s$5^2 \<le> s$1 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0" in wp_change_loopi)
  apply(rule wp_loopI, simp_all add: wp_choice del: rel_aka.fbox_add2, intro conjI)
    apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$3^2 * s$4^2 + s$5^2 \<le> s$1 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0"])
    apply(rule wp_g_odei, simp)
     apply(rule_tac C="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0" in diff_cut_rule, simp_all)
      apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0"], rule wp_g_odei; simp add: wp_diff_inv)
      apply(rule diff_invariant_conj_rule)
       apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
     apply(simp add: wp_diff_inv, intro diff_invariant_conj_rule)
       apply(rule_tac \<nu>'="\<lambda>s. -4*(s$2)*(s$3)*(s$5)^2" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq; (clarsimp simp: forall_5)?)
       apply(auto intro!: poly_derivatives simp: field_simps power2_eq_square)[1]
      apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
  subgoal sorry
   apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$3^2 * s$4^2 + s$5^2 \<le> s$1 \<and> s$2 \<ge> 0 \<and> s$3 \<ge> 0"])
   apply(rule wp_g_odei, simp)
    apply(rule_tac C="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0" in diff_cut_rule, simp_all)
     apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0"], rule wp_g_odei, simp_all)
     apply(simp add: wp_diff_inv, rule diff_invariant_conj_rule)
      apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
    apply(simp add: wp_diff_inv, intro diff_invariant_conj_rule)
      apply(rule_tac \<nu>'="\<lambda>s. -4*(s$2)*(s$3)*(s$5)^2" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq; (clarsimp simp: forall_5)?)
      apply(auto intro!: poly_derivatives simp: field_simps power2_eq_square)[1]
     apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
  subgoal sorry
  apply(rule_tac C="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0" in diff_cut_rule, simp_all)
   apply(subst g_ode_inv_def[symmetric, where I="\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<ge> 0"], rule wp_g_odei, simp_all)
   apply(simp add: wp_diff_inv, rule diff_invariant_conj_rule)
    apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
  apply(simp add: wp_diff_inv, intro diff_invariant_conj_rule)
    apply(rule_tac \<nu>'="\<lambda>s. -4*(s$2)*(s$3)*(s$5)^2" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq; (clarsimp simp: forall_5)?)
    apply(auto intro!: poly_derivatives simp: field_simps power2_eq_square)[1]
   apply (rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 0" in new_diff_invs_leq, simp_all add: forall_5)+
  done

declare wp_diff_inv [simp]

no_notation switch_two_osc_f ("f")


subsection \<open> Dynamics: Nonlinear 1 \<close>

(* x^3 >= -1 -> [{x'=(x-3)^4+a & a>=0}] x^3>=-1 *)
lemma "\<lceil>\<lambda>s::real^1. s$1^3 \<ge> -1\<rceil> \<le> wp 
  (x\<acute>= (\<lambda>s. \<chi> i. (s$1 - 3)^4 + a) & (\<lambda>s. a \<ge> 0) on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1^3 \<ge> -1\<rceil>"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 3 * s$1^2 * ((s$1 - 3)^4 + a)" in new_diff_invs_leq)
  by (auto intro!: poly_derivatives simp: field_simps)


subsection \<open> Dynamics: Nonlinear 2 \<close>

(* x1+x2^2/2=a -> [{x1'=x1*x2,x2'=-x1}]x1+x2^2/2=a *)
lemma "\<lceil>\<lambda>s::real^2. s$1 + (s$2^2)/2 = a\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$1 * s$2 else - s$1) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1 + (s$2^2)/2 = a\<rceil>"
  by (auto intro!: diff_invariant_rules poly_derivatives)


subsection \<open> Dynamics: Nonlinear 4 \<close>

(* x1^2/2-x2^2/2>=a -> [{x1'=x2+x1*x2^2, x2'=-x1+x1^2*x2 & x1>=0 & x2>=0}]x1^2/2-x2^2/2>=a *)
lemma "\<lceil>\<lambda>s::real^2. (s$1)^2/2 - (s$2^2)/2 \<ge> a\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 + s$1 * (s$2^2) else - s$1 + s$1^2 * s$2) & (\<lambda>s. s$1 \<ge> 0 \<and> s$2 \<ge> 0) on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. (s$1)^2/2 - (s$2^2)/2 \<ge> a\<rceil>"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$1*(s$2 + s$1 * (s$2^2)) - s$2 * (- s$1 + s$1^2 * s$2)" in new_diff_invs_leq)
  by (auto intro!: poly_derivatives simp: field_simps power2_eq_square)


subsection \<open> Dynamics: Nonlinear 5 \<close>

(* -x1*x2>=a -> [{x1'=x1-x2+x1*x2, x2'=-x2-x2^2}]-x1*x2>=a *)
lemma "\<lceil>\<lambda>s::real^2. -(s$1) *(s$2) \<ge> a\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$1 - s$2 + s$1 * s$2 else - s$2 - s$2^2) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. -(s$1)*(s$2) \<ge> a\<rceil>"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. (- s$1 + s$2 - s$1 * s$2) * s$2 - s$1 * (- s$2 - s$2^2)" in new_diff_invs_leq)
  by (auto intro!: poly_derivatives simp: field_simps power2_eq_square)


subsection \<open> Dynamics: Riccati \<close>

(* 2*x^3 >= 1/4 -> [{x'=x^2+x^4}] 2*x^3>=1/4 *)
lemma "\<lceil>\<lambda>s::real^1. 2 * s$1^3 \<ge> 1/4\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. s$1^2 + s$1^4) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. 2 * s$1^3 \<ge> 1/4\<rceil>"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 24 * (s$1^2) * (s$1^2 + s$1^4)" in new_diff_invs_leq; clarsimp)
  by (auto intro!: poly_derivatives simp: field_simps power2_eq_square)


subsection \<open> Dynamics: Nonlinear differential cut \<close>

(* x^3 >= -1 & y^5 >= 0 -> [{x'=(x-3)^4+y^5, y'=y^2}] (x^3 >= -1 & y^5 >= 0) *)
lemma "\<lceil>\<lambda>s::real^2. s$1^3 \<ge> - 1 \<and> s$2^5 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then (s$1 - 3)^4 else s$2^2) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$1^3 \<ge> - 1 \<and> s$2^5 \<ge> 0\<rceil>"
  apply(simp, rule diff_invariant_rules)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 3 * s$1^2 * (s$1 - 3)^4" in new_diff_invs_leq)
   apply(simp_all add: forall_2, force intro!: poly_derivatives)
   apply(rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. s$2^2" in new_diff_invs_leq)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: forall_2)


subsection \<open> STTT Tutorial: Example 1 \<close>

context local_flow
begin

lemma eq_solution_subset: "0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> t \<in> T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> s \<in> S \<Longrightarrow> 
  X \<in> Sols (\<lambda>t. f) T' S 0 s \<Longrightarrow> X t = \<phi> t s"
  apply(subgoal_tac "{0--t} \<subseteq> T'")
   apply(rule eq_solution_ivl)
       apply(rule has_vderiv_on_subset[OF ivp_solsD(1)], force, simp)
      apply(erule ivp_solsD(2), drule ivp_solsD(3), force)
  by (auto simp: closed_segment_subset_interval)

lemma wp_g_ode_subset: "0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> wp (x\<acute>= f & G on T' S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>T'. (\<forall>\<tau>. \<tau> \<in> T' \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  unfolding wp_g_orbital apply(clarsimp, rule iffI, clarsimp)
   apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE, blast)
  using in_ivp_sols_subset in_ivp_sols apply blast
  apply(clarsimp, subgoal_tac "s \<in> S", simp)
   apply(subgoal_tac "\<forall>\<tau>. \<tau> \<in> T' \<and> \<tau> \<le> t \<longrightarrow> X \<tau> = \<phi> \<tau> s", force, clarsimp)
   apply(rule eq_solution_subset; assumption?)
  by (auto simp: ivp_sols_def)

end

(* v >= 0 & A > 0 -> [ { x' = v, v' = A } ] v >= 0 *)
lemma "A > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^2. s$2 \<ge> 0\<rceil> \<le> 
  wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else A) & G on {0..} UNIV @ 0) 
  \<lceil>\<lambda>s. s$2 \<ge> 0\<rceil>"
  apply(subst local_flow.wp_g_ode_subset[where T="UNIV" 
        and \<phi>="\<lambda>t s. \<chi> i::2. if i=1 then A * t^2/2 + s$2 * t + s$1 else A * t + s$2"])
      apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_2 using exhaust_2 by (auto intro!: poly_derivatives simp: vec_eq_iff)


subsection \<open> STTT Tutorial: Example 2 \<close>

(* v >= 0 & A > 0 & B > 0 -> 
  [
    { {a := A; ++ a := 0; ++ a := -B;};
      { x' = v, v' = a & v >= 0 }
    }*@invariant(v >= 0)
  ] v >= 0 *)

lemma local_flow_STTT_Ex2:
  "local_flow (\<lambda>s::real^3. \<chi> i. if i = 1 then s$2 else (if i=2 then s$3 else 0)) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then s$3 * t^2/2 + s$2 * t + s$1 else (if i=2 then s$3 * t + s$2 else s$i))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_3 by (auto intro!: poly_derivatives simp: forall_3 vec_eq_iff)

lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<ge> 0\<rceil> \<le> wp 
  (LOOP (
    (((3 ::= (\<lambda>s. A)) \<union> (3 ::= (\<lambda>s. 0)) \<union> (3 ::= (\<lambda>s. B)));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0))
  ) INV (\<lambda>s. s$2 \<ge> 0))
  \<lceil>\<lambda>s. s$2 \<ge> 0\<rceil>"
  apply(rule wp_loopI, simp_all add: wp_choice del: rel_aka.fbox_add2, intro conjI)
  by (simp_all add: local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2])


subsection \<open> STTT Tutorial: Example 3a \<close> (* 37 *)

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) < S
 -> [
      { {   ?x+v^2/(2*B) < S; a := A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        }

        {
           {x' = v, v' = a & v >= 0 & x+v^2/(2*B) <= S}
        ++ {x' = v, v' = a & v >= 0 & x+v^2/(2*B) >= S}
        }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)

lemma STTexample3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 \<cdot> B) \<le> S"
  shows "x2 \<cdot> t - B \<cdot> t\<^sup>2 / 2 + x1 + (x2 - B \<cdot> t)\<^sup>2 / (2 \<cdot> B) \<le> S" (is "?lhs \<le> S")
proof-
  have "?lhs = 2 * B * x2 \<cdot> t/(2*B) - B^2 \<cdot> t\<^sup>2 / (2*B) + (2 * B * x1)/(2*B) + (x2 - B \<cdot> t)\<^sup>2 / (2 \<cdot> B)"
    using \<open>0 < B\<close> by (auto simp: power2_eq_square)
  also have "(x2 - B \<cdot> t)\<^sup>2 / (2 \<cdot> B) = x2^2/(2*B) + B^2 * t^2/(2*B) - 2*x2*B*t/(2*B)"
    using \<open>0 < B\<close> by (auto simp: power2_diff field_simps)
  ultimately have "?lhs = x1 + x2\<^sup>2 / (2 \<cdot> B)"
    using \<open>0 < B\<close> by auto
  thus "?lhs \<le> S"
    using key by simp
qed

lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) < S\<rceil> \<le> wp 
  (LOOP (
    ((\<lceil>\<lambda>s. s$1 + s$2^2/(2*B) < S\<rceil>;(3 ::= (\<lambda>s. A))) \<union> (\<lceil>\<lambda>s. s$2 = 0\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> (3 ::= (\<lambda>s. - B)));
    ((x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S) on {0..} UNIV @ 0) \<union>
     (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<ge> S) on {0..} UNIV @ 0))
  ) INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S))
  \<lceil>\<lambda>s. s$1 \<le> S\<rceil>"
  apply(rule wp_loopI)
    apply(simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2] del: rel_aka.fbox_add2)
   apply safe
      apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
     apply(erule_tac x=0 in allE)
  by (auto simp: STTexample3a_arith)


subsection \<open> STTT Tutorial: Example 4a \<close>

(* v <= V & A > 0
 -> [
      { {
           ?v=V; a:=0;
        ++ ?v!=V; a:=A;
        }

        {x' = v, v' = a & v <= V}
      }*@invariant(v <= V)
    ] v <= V *)

lemma "A > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<le> V\<rceil> \<le> wp 
  (LOOP 
    (\<lceil>\<lambda>s. s$2 = V\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> (\<lceil>\<lambda>s. s$2 \<noteq> V\<rceil>;(3 ::= (\<lambda>s. A)));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<le> V))
  \<lceil>\<lambda>s. s$2 \<le> V\<rceil>"
  by (rule wp_loopI) (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2] 
      del: rel_aka.fbox_add2)
 

subsection \<open>STTT Tutorial: Example 4b\<close>

(* v <= V & A > 0
 -> [
      { a := A;

        {x' = v, v' = a & v <= V}
      }*@invariant(v <= V)
    ] v <= V *)
lemma "A > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<le> V\<rceil> \<le> wp 
  (LOOP 
    (3 ::= (\<lambda>s. A));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<le> V))
  \<lceil>\<lambda>s. s$2 \<le> V\<rceil>"
  by (rule wp_loopI) (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2])
 

subsection \<open>STTT Tutorial: Example 4c\<close>

(* v <= V & A > 0
 -> [
      { {
           ?v=V; a:=0;
        ++ ?v!=V; a:=A;
        }

        {  {x' = v, v' = a & v <= V}
        ++ {x' = v, v' = a & v >= V}}
      }*@invariant(v <= V)
    ] v <= V *)
lemma "A > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<le> V\<rceil> \<le> wp 
  (LOOP 
    (\<lceil>\<lambda>s. s$2 = V\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> (\<lceil>\<lambda>s. s$2 \<noteq> V\<rceil>;(3 ::= (\<lambda>s. A)));
    ((x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<le> V) on {0..} UNIV @ 0) \<union>
     (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> V) on {0..} UNIV @ 0))
  INV (\<lambda>s. s$2 \<le> V))
  \<lceil>\<lambda>s. s$2 \<le> V\<rceil>"
  apply (rule wp_loopI) 
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2] del: rel_aka.fbox_add2)
  by (clarsimp, erule_tac x=0 in allE, auto)


subsection \<open> STTT Tutorial: Example 5 \<close>

lemma STTexample5_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" 
    and key: "x1 + x2\<^sup>2 / (2 \<cdot> B) + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> x2) / B + (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "A \<cdot> t\<^sup>2 / 2 + x2 \<cdot> t + x1 + (A \<cdot> t + x2)\<^sup>2 / (2 \<cdot> B) \<le> S" (is "?k0 \<le> S")
proof-
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "A*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close>
    by (smt field_sum_of_halves mult_right_mono power_less_imp_less_base real_mult_le_cancel_iff2)
  hence "((A + B)/B) * (A*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 \<cdot> B) \<le>
    x1 + x2\<^sup>2 / (2 \<cdot> B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt real_mult_le_cancel_iff2 zero_compare_simps(9))
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

lemma local_flow_STTT_Ex5:
  "local_flow (\<lambda>s::real^4. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then s$3 * t^2/2 + s$2 * t + s$1 else (if i=2 then s$3 * t + s$2 else (if i=3 then s$3 else t+s$4)))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S; a := A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S\<rceil> \<le> wp 
  (LOOP 
    (
      (\<lceil>\<lambda>s. s$1 + s$2^2/(2*B) + (A/B + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S\<rceil>;(3 ::= (\<lambda>s. A))) \<union> 
      (\<lceil>\<lambda>s. s$2 = 0\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> 
      (3 ::= (\<lambda>s. - B))); 
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S))
  \<lceil>\<lambda>s. s$1 \<le> S\<rceil>"
  apply (rule wp_loopI) 
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex5] del: rel_aka.fbox_add2)
   apply safe
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
  by (auto simp: STTexample3a_arith STTexample5_arith)


subsection \<open> STTT Tutorial: Example 6 \<close>

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 \<cdot> B) + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> x2) / B + (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k \<cdot> \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k \<cdot> t\<^sup>2 / 2 + x2 \<cdot> t + x1 + (k \<cdot> t + x2)\<^sup>2 / (2 \<cdot> B) \<le> S" (is "?k0 \<le> S")
proof-
  have "0 \<le> k \<cdot> t + x2 + x2"
    using ghyp \<open>0 \<le> x2\<close> \<open>0 \<le> t\<close> by force
  hence "0 \<le> (k \<cdot> t + 2 * x2) * t/2"
    by (metis assms(5) divide_nonneg_pos is_num_normalize(1) mult_2 mult_sign_intros(1) rel_simps(51))
  hence f1: "0 \<le> k*t^2/2 + t*x2"
    by (auto simp: field_simps power2_eq_square)
  have f2: "0 \<le> (k + B) / B" "(k + B) / B \<le> (A + B) / B"
    using \<open>0 < A\<close> \<open>0 < B\<close> \<open>- B \<le> k\<close> \<open>k \<le> A\<close> divide_le_cancel by (auto, fastforce)
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "k*t^2/2 + t*x2 \<le> A*t^2/2 + t*x2"
    using \<open>k \<le> A\<close> by (auto simp: mult_right_mono)
  also have f3: "... \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close> \<open>t \<le> \<epsilon>\<close>
    by (smt field_sum_of_halves mult_right_mono power_less_imp_less_base real_mult_le_cancel_iff2)
  finally have "k*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2" .
  hence "((k + B)/B) * (k*t^2/2 + t*x2) \<le> ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)"
    using f1 f2 \<open>k \<le> A\<close> apply(rule_tac b="((A + B)/B) * (A*t^2/2 + t*x2)" in order.trans)
     apply (rule mult_mono', simp, simp, simp add: mult_right_mono, simp, simp)
    by (metis f3 add_sign_intros(4) assms(1,2) less_eq_real_def mult_zero_left 
        real_mult_le_cancel_iff2 zero_compare_simps(5))
  hence "((k + B)/B) * (k*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 \<cdot> B) \<le>
    x1 + x2\<^sup>2 / (2 \<cdot> B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt real_mult_le_cancel_iff2 zero_compare_simps(9))
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

(* v >= 0 & A > 0 & B > 0 & x+v^2/(2*B) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S; a :=*; ?-B <= a & a <= A;
         ++ ?v=0; a := 0;
         ++ a := -B;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*B) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S\<rceil> \<le> wp 
  (LOOP 
    (
      (\<lceil>\<lambda>s. s$1 + s$2^2/(2*B) + (A/B + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S\<rceil>;(3 ::= ?);\<lceil>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> A\<rceil>) \<union> 
      (\<lceil>\<lambda>s. s$2 = 0\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> 
      (3 ::= (\<lambda>s. - B))); 
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*B) \<le> S))
  \<lceil>\<lambda>s. s$1 \<le> S\<rceil>"
  apply (rule wp_loopI) 
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex5] del: rel_aka.fbox_add2)
   apply safe
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
  by (auto simp: STTexample3a_arith STTexample6_arith)


subsection \<open> STTT Tutorial: Example 7 \<close>

lemma STTexample7_arith1:
  assumes "(0::real) < A" "0 < b" "0 < \<epsilon>" "0 \<le> v" "0 \<le> t" "k \<le> A"
    and "x + v\<^sup>2 / (2 \<cdot> b) + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> v) / b + (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> v)) \<le> S" (is "?expr1 \<le> S")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k \<cdot> \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x + (k \<cdot> t + v)\<^sup>2 / (2 \<cdot> b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs1: "?lhs\<cdot>(2\<cdot>b) = k\<cdot>t\<^sup>2\<cdot>b + 2\<cdot>v\<cdot>t\<cdot>b + 2\<cdot>x\<cdot>b + (k\<cdot>t+v)\<^sup>2" (is "_ = ?expr2 k t")
    using \<open>0 < b\<close> by (simp add: field_simps)
  have "?expr2 A \<epsilon> = ?expr1\<cdot>(2\<cdot>b)"
    using \<open>0 < b\<close> by (simp add: field_simps power2_eq_square)
  also have "... \<le> S\<cdot>(2\<cdot>b)"
    using \<open>?expr1 \<le> S\<close> \<open>0 < b\<close> by (smt real_mult_less_iff1) 
  finally have obs2: "?expr2 A \<epsilon> \<le> S\<cdot>(2\<cdot>b)" .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "t\<^sup>2 \<le> \<epsilon>\<^sup>2" "k \<cdot> t + v \<le> A \<cdot> \<epsilon> + v"
    using \<open>k \<le> A\<close> \<open>0 < A\<close> power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2] 
    by auto (meson \<open>0 \<le> t\<close> less_eq_real_def mult_mono)
  hence "k \<cdot> t\<^sup>2 \<cdot> b \<le> A \<cdot> \<epsilon>\<^sup>2 \<cdot> b" "2 \<cdot> v \<cdot> t \<cdot> b \<le> 2 \<cdot> v \<cdot> \<epsilon> \<cdot> b"
    using \<open>t \<le> \<epsilon>\<close> \<open>0 < b\<close> \<open>k \<le> A\<close> \<open>0 \<le> v\<close> 
    by (auto simp: mult_left_mono) (meson \<open>0 < A\<close> less_eq_real_def mult_mono zero_compare_simps(12))
  hence "?expr2 k t \<le> ?expr2 A \<epsilon>"
    by (smt \<open>k \<cdot> t + v \<le> A \<cdot> \<epsilon> + v\<close> ends_in_segment(2) \<open>0 \<le> t\<close> guard power_mono)
  hence "?lhs\<cdot>(2\<cdot>b) \<le> S\<cdot>(2\<cdot>b)" 
    using obs1 obs2 by simp
  thus "?lhs \<le> S"
    using \<open>0 < b\<close> by (smt real_mult_less_iff1)
qed

lemma STTexample7_arith2:
  assumes "(0::real) < b" "0 \<le> v" "0 \<le> t" "k \<le> - b"
    and key: "x + v\<^sup>2 / (2 \<cdot> b) \<le> S" 
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k \<cdot> \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x + (k \<cdot> t + v)\<^sup>2 / (2 \<cdot> b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs: "1 + k/b \<le> 0" "k \<cdot> t + v \<ge> 0"
    using \<open>k \<le> - b\<close> \<open>0 < b\<close> guard \<open>0 \<le> t\<close> by (auto simp: mult_imp_div_pos_le real_add_le_0_iff)
  have "?lhs = (k \<cdot> t + v + v)\<cdot>t/2 \<cdot> (1 + k/b) + x + v\<^sup>2 / (2 \<cdot> b)"
    using \<open>0 < b\<close> by (auto simp: field_simps power2_eq_square)
  also have "... \<le> x + v\<^sup>2 / (2 \<cdot> b)"
    using obs \<open>0 \<le> t\<close> \<open>0 \<le> v\<close>
    by (smt mult_nonneg_nonneg zero_compare_simps(11) zero_compare_simps(6))
  also have "... \<le> S"
    using key .
  finally show ?thesis .
qed

(* v >= 0 & A > 0 & B >= b & b > 0 & x+v^2/(2*b) <= S & ep > 0
 -> [
      { {   ?x+v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) <= S; a :=*; ?-B <= a & a <= A;
         ++ ?v=0; a := 0;
         ++ a :=*; ?-B <=a & a <= -b;
        };

        c := 0;
        { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
      }*@invariant(v >= 0 & x+v^2/(2*b) <= S)
    ] x <= S *)
lemma "A > 0 \<Longrightarrow> B \<ge> b \<Longrightarrow> b > 0 \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*b) \<le> S\<rceil> \<le> wp 
  (LOOP 
    (
      (\<lceil>\<lambda>s. s$1 + s$2^2/(2*b) + (A/b + 1) * (A/2 * \<epsilon>^2 + \<epsilon> * s$2) \<le> S\<rceil>;(3 ::= ?);\<lceil>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> A\<rceil>) \<union> 
      (\<lceil>\<lambda>s. s$2 = 0\<rceil>;(3 ::= (\<lambda>s. 0))) \<union> 
      ((3 ::= ?);\<lceil>\<lambda>s. -B \<le> s$3 \<and> s$3 \<le> - b\<rceil>)
    );(4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$1 + s$2^2/(2*b) \<le> S))
  \<lceil>\<lambda>s. s$1 \<le> S\<rceil>"
  apply (rule wp_loopI) 
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex5] del: rel_aka.fbox_add2)
   apply(safe)
     apply (smt not_sum_power2_lt_zero zero_compare_simps(5))
    apply(force simp: STTexample7_arith1, force)
  using STTexample7_arith2[of b "_$2" _ _ "_$1" S] by blast


subsection \<open> STTT Tutorial: Example 9a \<close>

lemma STTexample9a_arith:
  "(10\<cdot>x-10\<cdot>r)\<cdot>v/4 + v\<^sup>2/2 + (x-r)\<cdot>(2\<cdot>r-2\<cdot>x-3\<cdot>v)/2 + v\<cdot>(2\<cdot>r-2\<cdot>x-3\<cdot>v)/2 \<le> (0::real)" (is "?t1 + ?t2 + ?t3 + ?t4 \<le> 0")
proof-
  have "?t1 = 5 * (x-r) * v/2"
    by auto
  moreover have "?t3 = -((x - r)^2) - 3 * v * (x-r)/2"
    by (auto simp: field_simps power2_diff power2_eq_square)
  moreover have "?t4 = - 2 * (x - r) * v/2 - 3 * v^2/2"
    by (auto simp: field_simps power2_diff power2_eq_square)
  ultimately have "?t1 + ?t3 + ?t4 = -((x - r)^2) - 3 * v^2/2"
    by (auto simp: field_simps)
  hence "?t1 + ?t2 + ?t3 + ?t4 = -((x - r)^2) - v^2"
    by auto
  also have "... \<le> 0"
    by auto
  finally show ?thesis .
qed

(* v >= 0 & c() > 0 & Kp() = 2 & Kd() = 3 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()
 -> [
      { x' = v, v' = -Kp()*(x-xr()) - Kd()*v }
    ] 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c() *)
lemma "c > 0 \<Longrightarrow> Kp = 2 \<Longrightarrow> Kd = 3 \<Longrightarrow> \<lceil>\<lambda>s::real^2. (5/4)*(s$1-xr)^2 + (s$1-xr)*(s$2)/2 + (s$2)^2/4 < c\<rceil> \<le> wp 
  (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else -Kp*(s$1-xr) - Kd*(s$2) ) & G on {0..} UNIV @ 0)
  \<lceil>\<lambda>s. (5/4)*(s$1-xr)^2 + (s$1-xr)*(s$2)/2 + (s$2)^2/4 < c\<rceil>"
  apply(simp, rule_tac \<mu>'="\<lambda>s. 0" and \<nu>'="\<lambda>s. 10*(s$1-xr)*(s$2)/4 + (s$2^2)/2 + 
    (s$1-xr)*(-Kp*(s$1-xr)-Kd*(s$2))/2 + (s$2)*(-Kp*(s$1-xr)-Kd*(s$2))/2" in new_diff_invs_le; 
      clarsimp simp: forall_2 STTexample9a_arith)
  apply(intro poly_derivatives; (rule poly_derivatives)?)
  by force+ (auto simp: field_simps power2_eq_square)


subsection \<open> STTT Tutorial: Example 9b \<close> (*N 50 *)

(* v >= 0 & xm <= x & x <= S & xr = (xm + S)/2 & Kp = 2 & Kd = 3
           & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2
 -> [ { {  xm := x;
           xr := (xm + S)/2;
           ?5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2;
        ++ ?true;
        };
        {{ x' = v, v' = -Kp*(x-xr) - Kd*v & v >= 0 }
          @invariant(
            xm<=x,
            5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2
         )
        }
      }*@invariant(v >= 0 & xm <= x & xr = (xm + S)/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S - xm)/2)^2)
    ] x <= S *)
lemma "c > 0 \<Longrightarrow> Kp = 2 \<Longrightarrow> Kd = 3 \<Longrightarrow> 
  \<lceil>\<lambda>s::real^4. s$2 \<ge> 0 \<and> s$3 \<le> s$1 \<and> s$1 \<le> S \<and> s$4 = (s$3 + S)/2 
  \<and> (5/4)*(s$1-s$4)^2 + (s$1-s$4)*(s$2)/2 + (s$2)^2/4 < ((S - s$3)/2)^2\<rceil> \<le> wp 
  (LOOP ((3 ::= (\<lambda>s. s$1));(4 ::= (\<lambda>s. (s$3 + S)/2));
    \<lceil>\<lambda>s. (5/4)*(s$1-s$4)^2 + (s$1-s$4)*(s$2)/2 + (s$2)^2/4 < ((S - s$3)/2)^2\<rceil> \<union> \<lceil>\<lambda>s. True\<rceil>);
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then -Kp*(s$1-s$3) - Kd*(s$2) else 0)) & 
      (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0 DINV (\<lambda>s. s$3 \<le> s$1 \<and> 
        (5/4)*(s$1-(s$3+S)/2)^2 + (s$1-(s$3+S)/2)*(s$2)/2 + s$2^2/4 < ((S - s$3)/2)^2))
  INV (\<lambda>s. s$2 \<ge> 0 \<and> s$3 \<le> s$1 \<and> s$4 = (s$3 + S)/2 \<and> 
    (5/4)*(s$1-s$4)^2 + (s$1-s$4)*(s$2)/2 + (s$2)^2/4 < ((S - s$3)/2)^2))
  \<lceil>\<lambda>s. s$1 \<le> S\<rceil>"
  oops

subsection \<open> STTT Tutorial: Example 10 \<close> (*N 51 *)

(*
 v >= 0 & A > 0 & B >= b & b > 0 & ep > 0 & lw > 0 & y = ly & r != 0 & dx^2 + dy^2 = 1
           & abs(y-ly) + v^2/(2*b) < lw
 -> [
      { {   ?abs(y-ly) + v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) < lw;
            a :=*; ?-B <= a & a <= A;
            w :=*; r :=*; ?r != 0 & w*r = v;
         ++ ?v=0; a := 0; w := 0;
         ++ a :=*; ?-B <=a & a <= -b;
        }

        c := 0;
        {
        { x' = v*dx, y' = v*dy, v' = a, dx' = -dy*w, dy' = dx*w, w'=a/r, c' = 1 & v >= 0 & c <= ep }
        @invariant(c>=0, dx^2+dy^2=1,
          (v'=a -> v=old(v)+a*c),
          (v'=a -> -c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)),
          (v'=0 -> v=old(v)),
          (v'=0 -> -c*v <= y - old(y) & y - old(y) <= c*v)
        )
        }
      }*@invariant(v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw)
    ] abs(y-ly) < lw *)

subsection \<open> LICS: Example 1 Continuous car accelerates forward \<close>

(*
   v>=0 & a>=0
 -> [
      {x'=v, v'=a & v>=0}
    ] v>=0 *)
lemma "\<lceil>\<lambda>s::real^3. s$2 \<ge> 0 \<and> s$3 \<ge> 0\<rceil> \<le> wp 
  (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0)
  \<lceil>\<lambda>s. s$2 \<ge> 0\<rceil>"
  by (simp_all add: local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2])
 

subsection \<open> LICS: Example 2 Single car drives forward \<close>

(* v>=0  & A>=0 & b>0
 -> [
      {
        {a:=A; ++ a:=-b;}
        {x'=v, v'=a & v>=0}
      }*@invariant(v>=0)
    ] v>=0 *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<ge> 0\<rceil> \<le> wp 
  (LOOP
    ((3 ::= (\<lambda>s. A)) \<union> (3 ::= (\<lambda>s. -b)));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<ge> 0))
  \<lceil>\<lambda>s. s$2 \<ge> 0\<rceil>"
  by (rule wp_loopI) (simp_all add: local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2])

subsection \<open> LICS: Example 3a event-triggered car drives forward \<close>

(*
( v >= 0
	 & A >= 0
	 & b > 0 )
->
  [
    {
      {  ?(m-x>=2); a := A;
      ++ a := -b;
      };
      {x' = v, v' = a & v >= 0}
    }*@invariant(v >= 0)
  ]v >= 0 *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^3. s$2 \<ge> 0\<rceil> \<le> wp 
  (LOOP
    ((\<lceil>\<lambda>s. m - s$1 \<ge> 2\<rceil>;(3 ::= (\<lambda>s. A))) \<union> (3 ::= (\<lambda>s. -b)));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else 0)) & (\<lambda>s. s$2 \<ge> 0) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2 \<ge> 0))
  \<lceil>\<lambda>s. s$2 \<ge> 0\<rceil>"
  by (rule wp_loopI) (simp_all add: local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex2])


subsection \<open> LICS: Example 4a safe stopping of time-triggered car \<close>

lemma LICSexample4a_arith:
  assumes "(0::real) \<le> A" "0 < b" "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x)" "0 \<le> t"
      and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> A \<cdot> \<tau> + v \<and> \<tau> \<le> \<epsilon>"
      and key: "v\<^sup>2 + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)) \<le> 2 \<cdot> b \<cdot> (m - x)" (is "?expr1 \<le> _")
    shows "(A \<cdot> t + v)\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - (A \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x))"
proof-
  have "t \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, auto)
  hence "A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v \<le> A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v"
    using \<open>0 \<le> A\<close> \<open>0 \<le> t\<close>
    by (smt mult_less_cancel_left_disj mult_right_mono power_less_imp_less_base) 
  hence "v\<^sup>2 + (A + b) \<cdot> (A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v) \<le> v\<^sup>2 + (A + b) \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)"
    using \<open>0 \<le> A\<close> \<open>0 < b\<close> by (smt mult_left_mono) 
  also have "... = ?expr1"
    by auto
  finally have "v\<^sup>2 + (A + b) \<cdot> (A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v) \<le> 2 \<cdot> b \<cdot> (m - x)"
    using key by auto
  thus ?thesis
    by (auto simp: field_simps power2_eq_square)
qed

(*v^2<=2*b*(m-x) & v>=0  & A>=0 & b>0
 -> [
      {
        {?(2*b*(m-x) >= v^2+(A+b)*(A*ep^2+2*ep*v)); a:=A; ++ a:=-b; }
        t := 0;
        {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
      }*@invariant(v^2<=2*b*(m-x))
    ] x <= m *)
lemma "A \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> \<lceil>\<lambda>s::real^4. s$2^2 \<le> 2*b*(m-s$1) \<and> s$2 \<ge> 0\<rceil> \<le> wp 
  (LOOP
    ((\<lceil>\<lambda>s. 2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>^2+2*\<epsilon>*(s$2))\<rceil>;(3 ::= (\<lambda>s. A))) \<union> (3 ::= (\<lambda>s. -b)));
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2^2 \<le> 2*b*(m-s$1)))
  \<lceil>\<lambda>s. s$1 \<le> m\<rceil>"
  apply (rule wp_loopI) 
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex5] del: rel_aka.fbox_add2)
   apply(safe, smt not_sum_power2_lt_zero zero_compare_simps(10))
  using LICSexample4a_arith[of A b "_$2" m "_$1" _ \<epsilon>] apply force
  by (auto simp: power2_diff power2_eq_square[symmetric] algebra_simps(18,19) 
      mult.assoc[symmetric] power_mult_distrib)


subsection \<open> LICS: Example 4b progress of time-triggered car \<close>  (*N 56 *)

notation rel_aka.fdia ("\<diamondsuit>")

lemma in_fdia_iff_wp: "(s,s) \<in> \<diamondsuit> R \<lceil>P\<rceil> \<longleftrightarrow> (s,s) \<in> rel_ad (wp R (rel_ad \<lceil>P\<rceil>))"
  unfolding rel_ad_def rel_aka.fdia_def rel_aka.fbox_def by auto

(* ep() > 0 & A() > 0 & b() > 0
->
  \forall p \exists m
  <
    {
        {?(2*b()*(m-x) >= v^2+(A()+b())*(A()*ep()^2+2*ep()*v)); a:=A(); ++ a:=-b(); }
        t := 0;
        {x'=v, v'=a, t'=1 & v>=0 & t<=ep()}
    }*
  > (x >= p) *)

lemma "\<epsilon> > (0::real) \<Longrightarrow> A > 0 \<Longrightarrow> b > 0 \<Longrightarrow> 
  \<forall>p. \<exists>m. (s,s) \<in> \<diamondsuit> (
    LOOP (\<lceil>\<lambda>s. 2*b*(m-x) \<ge> s$2^2+(A+b)*A*\<epsilon>^2+2*\<epsilon>\<cdot>v\<rceil>;(3 ::= (\<lambda>s. A)) \<union> (3 ::= (\<lambda>s. -b)));
      (4 ::= (\<lambda>s. 0));
      (x\<acute>= (\<lambda>s. f 1 (s$3) s) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
    INV (\<lambda>s. True)) \<lceil>\<lambda>s. s$1 \<ge> p\<rceil>"
  apply(subst in_fdia_iff_wp, simp)
  apply(clarsimp simp: rel_ad_def)
  apply(intro exI conjI allI)
  apply clarsimp
  oops


subsection \<open> LICS: Example 4c relative safety of time-triggered car \<close>

lemma in_wp_loopI: 
  "I x \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> wp R \<lceil>I\<rceil> \<Longrightarrow> y = x \<Longrightarrow> (x,y) \<in> wp (LOOP R INV I) \<lceil>Q\<rceil>"
  using wp_loopI[of I I Q R] apply simp
  apply(subgoal_tac "(x,x) \<in> \<lceil>I\<rceil>")
  by (simp add: subset_eq, simp add: p2r_def)

lemma (in local_flow) in_wp_g_ode_subset: "0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> 
  (s,s) \<in> wp (x\<acute>= f & G on T' S @ 0) \<lceil>Q\<rceil> \<longleftrightarrow>  (s \<in> S \<longrightarrow> (\<forall>t\<in>T'. (\<forall>\<tau>. \<tau> \<in> T' \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst wp_g_ode_subset, simp_all add: p2r_def)

abbreviation LICS_Ex4c_f :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f time acc s \<equiv> (\<chi> i. if i=1 then s$2 else (if i=2 then acc else if i=3 then 0 else time))"

lemma local_flow_LICS_Ex4c_1:
  "local_flow (f k a) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i=1 then a * t^2/2 + s$2 * t + s$1 else 
             (if i=2 then a * t + s$2               else 
             (if i=3 then s$3                       else 
                          k * t + s$4               )))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

lemma local_flow_LICS_Ex4c_2:
  "local_flow (\<lambda>s. f k (s$3) s) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i=1 then s$3 * t^2/2 + s$2 * t + s$1 else 
             (if i=2 then s$3 * t + s$2               else 
             (if i=3 then s$3                       else 
                          k * t + s$4               )))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_4 by (auto intro!: poly_derivatives simp: forall_4 vec_eq_iff)

lemma LICSexample4c_arith1:
  assumes "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x)" "0 \<le> t" "A \<ge> 0" "b > 0"
    and key: "v\<^sup>2 + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)) \<le> 2 \<cdot> b \<cdot> (m - x)"
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> (0::real) \<le> A \<cdot> \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "(A \<cdot> t + v)\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - (A \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x))" (is "_ \<le> ?rhs")
proof-
  have "t \<le> \<epsilon>" "0 \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, simp, erule_tac x=0 in allE, simp)
  hence obs1: "A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v \<le> A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v"
    using \<open>A \<ge> 0\<close> \<open>0 \<le> t\<close> \<open>t \<le> \<epsilon>\<close> by (smt mult_mono power_mono zero_compare_simps(12)) 
  have obs2:"?rhs + A * b * t^2 + 2 * b * v * t = 2 * b * (m - x)"
    by (simp add: field_simps)
  have "(A \<cdot> t + v)\<^sup>2 + A * b * t^2 + 2 * b * v * t = v\<^sup>2 + (A \<cdot> (A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v) + b \<cdot> (A \<cdot> t\<^sup>2 + 2 \<cdot> t \<cdot> v))"
    by (simp add: field_simps power2_eq_square)
  also have "... \<le> v\<^sup>2 + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v))"
    using obs1 \<open>A \<ge> 0\<close> \<open>b > 0\<close> by (smt mult_less_cancel_left) 
  also have "... \<le> 2 * b * (m - x)"
    using key .
  finally show ?thesis
    using obs2 by auto
qed

(* ( [{x' = v, v' = -b()}]x<=m()
   & v >= 0
	 & A() >= 0
	 & b() > 0 )
->
  [
    {
      {  ?(2*b()*(m()-x) >= v^2 + (A() + b())*(A()*ep()^2 + 2*ep()*v)); a := A();
      ++ a := -b();
      };
      t := 0;
      {x' = v, v' = a, t' = 1 & v >= 0 & t <= ep()}
    }*@invariant(v^2<=2*b()*(m()-x))
  ]x<=m() *)
lemma 
  assumes "A \<ge> 0" "b > 0" "s$2 \<ge> 0"
  shows "(s,s) \<in> wp (x\<acute>=(f 0 (-b)) & (\<lambda>s. True) on {0..} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<le> m\<rceil> \<Longrightarrow> 
  (s,s) \<in> wp 
  (LOOP
    ((\<lceil>\<lambda>s. 2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>^2+2*\<epsilon>*(s$2))\<rceil>;(3 ::= (\<lambda>s. A))) \<union> (3 ::= (\<lambda>s. -b)));
    (4 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s. f 1 (s$3) s) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. s$2^2 \<le> 2*b*(m-s$1))) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>"
  apply(subst (asm) local_flow.in_wp_g_ode_subset[OF local_flow_LICS_Ex4c_1], simp_all)
  apply(rule in_wp_loopI)
     apply(simp_all add: local_flow.wp_g_ode_subset[OF local_flow_LICS_Ex4c_2], safe)
     apply(erule_tac x="s$2/b" in ballE)
  using \<open>b > 0\<close> \<open>s$2 \<ge> 0\<close> apply(simp add: field_simps power2_eq_square, simp)
  apply (smt \<open>b > 0\<close> mult_sign_intros(6) sum_power2_ge_zero)
  using LICSexample4c_arith1[OF _ _ \<open>0 \<le> A\<close> \<open>0 < b\<close>] apply force
  by (auto simp: field_simps power2_eq_square)

no_notation LICS_Ex4c_f ("f")


subsection \<open> LICS: Example 5 Controllability Equivalence \<close>

lemma LICSexample5_arith1:
  assumes "(0::real) < b" "0 \<le> t"
    and key: "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x)"
  shows "v \<cdot> t - b \<cdot> t\<^sup>2 / 2 + x \<le> m"
proof-
  have "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x) + (b \<cdot> t - v)^2"
    using key by (simp add: add_increasing2) 
  hence "b^2 * t^2 - 2 * b * v * t \<ge> 2 * b * x - 2 * b * m"
    by (auto simp: field_simps power2_diff)
  hence "(b^2/b) * t^2 - 2 * (b/b) * v * t \<ge> 2 * (b/b) * x - 2 * (b/b) * m"
    using \<open>b > 0\<close> by (auto simp: field_simps)
  thus ?thesis
    using \<open>b > 0\<close> by (simp add: power2_eq_square)
qed

lemma LICSexample5_arith2:
  assumes "(0::real) < b" "0 \<le> v" "\<forall>t\<in>{0..}. v \<cdot> t - b \<cdot> t\<^sup>2 / 2 + x \<le> m"
  shows "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x)"
proof(cases "v = 0")
  case True
  have "m - x \<ge> 0"
    using assms by (erule_tac x=0 in ballE, auto)
  thus ?thesis 
    using assms True by auto
next
  case False
  hence obs: "v > 0 \<and> (\<exists>k. k > 0 \<and> v = b * k)"
    using assms(1,2) by (metis (no_types, hide_lams) divide_pos_pos divide_self_if 
        less_eq_real_def linorder_not_le mult_1_right mult_1s(1) times_divide_eq_left) 
  {fix t::real assume "t \<ge> 0"
    hence "v \<cdot> t - b \<cdot> t\<^sup>2 / 2 + x \<le> m"
      using assms by auto
    hence "- (b^2) * t^2 + 2 * b * v * t \<le> 2 * b * m - 2 * b * x"
      using \<open>b > 0\<close> apply(simp add: field_simps)
      by (metis (no_types, hide_lams) Groups.mult_ac(1) nat_distrib(2) power2_eq_square real_mult_le_cancel_iff2)
    hence "v^2 \<le> 2 * b * (m - x) + (b^2 * t^2 + v^2 - 2 * b * v * t)"
      by (simp add: field_simps)
    also have "... = 2 * b * (m - x) + (b * t - v)^2"
      by (simp add: power2_diff power_mult_distrib)
    finally have "v^2 \<le> 2 * b * (m - x) + (b * t - v)^2" .}
  hence "\<forall>t\<ge>0. v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x) + (b \<cdot> t - v)\<^sup>2"
    by blast
  then obtain k where "v\<^sup>2 \<le> 2 \<cdot> b \<cdot> (m - x) + (b \<cdot> k - v)\<^sup>2 \<and> k > 0 \<and> v = b * k"
    using obs by fastforce
  then show ?thesis 
    by auto
qed

(* v>=0 & b>0 -> ( v^2<=2*b*(m-x) <-> [{x'=v, v'=-b}]x<=m ) *)
lemma "b > 0 \<Longrightarrow> s$2 \<ge> 0 \<Longrightarrow> 
   (s,s) \<in> \<lceil>\<lambda>s::real^2. s$2^2 \<le> 2*b*(m-s$1)\<rceil> \<longleftrightarrow> (s,s) \<in> wp 
  (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else -b) & (\<lambda>s. True) on {0..} UNIV @ 0)
  \<lceil>\<lambda>s. s$1 \<le> m\<rceil>"
  apply(subst local_flow.wp_g_ode_subset[where T="UNIV" 
        and \<phi>="\<lambda>t s. \<chi> i::2. if i=1 then -b * t^2/2 + s$2 * t + s$1 else -b * t + s$2"])
      apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
     apply(clarsimp simp: dist_norm norm_vec_def L2_set_def, rule_tac x=1 in exI)+
  unfolding UNIV_2 apply clarsimp
  apply(force intro!: poly_derivatives)
  using exhaust_2 apply(force simp: vec_eq_iff)
  by (auto simp: p2r_def LICSexample5_arith1 LICSexample5_arith2)


subsection \<open> LICS: Example 6 MPC Acceleration Equivalence \<close>  (*N 59 *)

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
  A \<cdot> t \<cdot> \<tau> + v \<cdot> \<tau> - b \<cdot> \<tau>\<^sup>2 / 2 + (A \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) \<le> (m::real))"
  shows "v\<^sup>2 + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)) \<le> 2 \<cdot> b \<cdot> (m - x)"
proof-
  {fix \<tau>::real
    assume "\<tau> \<ge> 0"
    hence "A \<cdot> \<epsilon> \<cdot> \<tau> + v \<cdot> \<tau> - b \<cdot> \<tau>\<^sup>2 / 2 + (A \<cdot> \<epsilon>\<^sup>2 / 2 + v \<cdot> \<epsilon> + x) \<le> m"
      using guard \<open>0 \<le> \<epsilon>\<close> apply(erule_tac x=\<epsilon> in ballE)
      by (erule impE, auto simp: closed_segment_eq_real_ivl)
    hence "2 * (A \<cdot> \<epsilon> \<cdot> \<tau> + v \<cdot> \<tau> - b \<cdot> \<tau>\<^sup>2 / 2 + (A \<cdot> \<epsilon>\<^sup>2 / 2 + v \<cdot> \<epsilon> + x)) * b \<le> 2 * m * b"
      using \<open>0 < b\<close> by (meson less_eq_real_def mult_left_mono mult_right_mono rel_simps(51)) 
    hence "2 * A \<cdot> \<epsilon> \<cdot> \<tau> \<cdot> b + 2 * v \<cdot> \<tau> \<cdot> b - b^2 \<cdot> \<tau>\<^sup>2 + b * (A \<cdot> \<epsilon>\<^sup>2 + 2 * v \<cdot> \<epsilon>) \<le> 2 * b * (m - x)"
      using \<open>0 < b\<close> apply(simp add: algebra_simps(17,18,19,20) add.assoc[symmetric] 
          power2_eq_square[symmetric] mult.assoc[symmetric])
      by (simp add: mult.commute mult.left_commute power2_eq_square)}
  hence "\<forall>\<tau>\<ge>0. 2 * A \<cdot> \<epsilon> \<cdot> \<tau> \<cdot> b + 2 * v \<cdot> \<tau> \<cdot> b - b^2 \<cdot> \<tau>\<^sup>2 + b * (A \<cdot> \<epsilon>\<^sup>2 + 2 * v \<cdot> \<epsilon>) \<le> 2 * b * (m - x)"
    by blast
  moreover have "2 * A \<cdot> \<epsilon> \<cdot> ((A*\<epsilon> + v)/b) \<cdot> b + 2 * v \<cdot> ((A*\<epsilon> + v)/b) \<cdot> b - b^2 \<cdot> ((A*\<epsilon> + v)/b)\<^sup>2 =
    2 * A \<cdot> \<epsilon> \<cdot> (A*\<epsilon> + v) + 2 * v \<cdot> (A*\<epsilon> + v) - (A*\<epsilon> + v)\<^sup>2"
    using \<open>0 < b\<close> by (simp add: field_simps)
  moreover have "... = v\<^sup>2 + A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)"
    using \<open>0 < b\<close> by (simp add: field_simps power2_eq_square)
  moreover have "(A*\<epsilon> + v)/b \<ge> 0"
    using assms by auto
  ultimately have "v\<^sup>2 + A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b * (A \<cdot> \<epsilon>\<^sup>2 + 2 * v \<cdot> \<epsilon>) \<le> 2 * b * (m - x)"
    using assms by (erule_tac x="(A*\<epsilon> + v)/b" in allE, auto)
  thus ?thesis
    by argo
qed

lemma LICSexample6_arith2:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> t" "0 \<le> \<tau>" "t \<le> \<epsilon>"
    and "v\<^sup>2 + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v) + b \<cdot> (A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> \<epsilon> \<cdot> v)) \<le> 2 \<cdot> b \<cdot> (m - x)"
  shows "A \<cdot> \<epsilon> \<cdot> \<tau> + s $ 2 \<cdot> \<tau> - b \<cdot> \<tau>\<^sup>2 / 2 + (A \<cdot> \<epsilon>\<^sup>2 / 2 + s $ 2 \<cdot> \<epsilon> + s $ 1) \<le> m"
  sorry

lemma local_flow_LICS_Ex6:
  "local_flow (\<lambda>s::real^3. \<chi> i. if i=1 then s$2 else (if i=2 then k1 else k2)) UNIV UNIV
  (\<lambda>t s. \<chi> i. if i = 1 then k1 * t^2/2 + s$2 * t + s$1 else (if i=2 then k1 * t + s$2 else k2 * t + s$3))"
  apply(unfold_locales, simp_all add: local_lipschitz_def forall_2 lipschitz_on_def)
    apply(clarsimp, rule_tac x=1 in exI)+
  apply(clarsimp simp: dist_norm norm_vec_def L2_set_def)
  unfolding UNIV_3 by (auto intro!: poly_derivatives simp: forall_3 vec_eq_iff)

(* v>=0 & b>0 & A>=0 & ep>=0 -> (
    [t:=0; {x'=v, v'=A, t'=1 & t<=ep}][{x'=v, v'=-b}]x<=m
    <->
    2*b*(m-x) >= v^2 + (A + b)*(A*ep^2 + 2*ep*v)
   ) *)
lemma "s$2 \<ge> 0 \<Longrightarrow> b>0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> \<epsilon> \<ge> 0 \<Longrightarrow>  
(s,s) \<in> wp ((3 ::= (\<lambda>s. 0));
    (x\<acute>= (\<lambda>s::real^3. \<chi> i. if i=1 then s$2 else (if i=2 then A else 1)) & (\<lambda>s. s$3 \<le> \<epsilon>) on {0..} UNIV @ 0))
 (wp (x\<acute>= (\<lambda>s. \<chi> i. if i=1 then s$2 else (if i=2 then -b else 0)) & (\<lambda>s. True) on {0..} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>)
\<longleftrightarrow>
  (s,s) \<in> \<lceil>\<lambda>s. 2*b*(m-s$1) \<ge> s$2^2+(A+b)*(A*\<epsilon>^2+2*\<epsilon>*(s$2))\<rceil>"
  apply (simp add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_LICS_Ex6])
  apply(simp add: p2r_def, safe)
  apply(force simp: LICSexample6_arith1)
  apply(erule_tac x=t in allE; clarsimp)
  apply(rename_tac t \<tau>)
  apply(rule_tac b="A \<cdot> \<epsilon> \<cdot> \<tau> + s $ 2 \<cdot> \<tau> - b \<cdot> \<tau>\<^sup>2 / 2 + (A \<cdot> \<epsilon>\<^sup>2 / 2 + s $ 2 \<cdot> \<epsilon> + s $ 1)" in order.trans)
   apply (smt divide_le_cancel mult_left_mono mult_right_mono power2_less_imp_less)
  by (auto simp: LICSexample6_arith2)


subsection \<open> LICS: Example 7 Model-Predictive Control Design Car \<close>  (*N 60 *)

notation LICS_Ex4c_f ("f")

(* [{x'=v, v'=-b}](x<=m)
   & v >= 0
   & A >= 0
   & b > 0
->
  [
    {
    {{?([t:=0; {x'=v, v'=A, t'=1 & v >= 0 & t<=ep}] [{x'=v, v'=-b}](x<=m));
       a := A;}
    ++ a := -b;}
      t := 0;
      {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
    }*@invariant([{x'=v, v'=-b}](x<=m))
  ] (x <= m) *)
lemma "s$2 \<ge> 0 \<Longrightarrow> b>0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> 
  (s,s) \<in> (wp (x\<acute>=(f 0 (-b)) & (\<lambda>s. True) on {0..} UNIV @ 0)) \<lceil>\<lambda>s. s$1 \<le> m\<rceil> \<Longrightarrow>  
(s,s) \<in> wp (
  LOOP 
    ((\<lceil>\<lambda>s. (s,s) \<in> wp ((3 ::= (\<lambda>s. 0));(x\<acute>= (f 1 A) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)) 
    (wp (x\<acute>= (f 0 (-b)) & (\<lambda>s. True) on {0..} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>)\<rceil>;(3 ::= (\<lambda>s. A))) \<union> (3 ::= (\<lambda>s. -b)));
  (4 ::= (\<lambda>s. 0)); (x\<acute>= (\<lambda>s. f 1 (s$3) s) & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)
  INV (\<lambda>s. (s,s) \<in> wp (x\<acute>=(f 0 (-b)) & (\<lambda>s. True) on {0..} UNIV @ 0) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>)) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>"
  oops

no_notation LICS_Ex4c_f ("f")


section \<open>Advanced\<close>


subsection \<open> ETCS: Essentials \<close>

locale ETCS =
  fixes \<epsilon> b A m::real
(* Real ep; /* Control cycle duration upper bound */
   Real b;  /* Braking force */
   Real A;  /* Maximum acceleration */
   Real m;  /* End of movement authority (train must not drive past m) *)
begin

(* Real stopDist(Real v) = v^2/(2*b) *)
abbreviation "stopDist v \<equiv> v^2/(2*b)"

(* Real accCompensation(Real v) = (((A/b) + 1)*((A/2)*ep^2 + ep*v)) *)
abbreviation "accCompensation v \<equiv> ((A/b) + 1) \<cdot> ((A/2)\<cdot>\<epsilon>^2 + \<epsilon>\<cdot>v)"

(* Real SB(Real v) = stopDist(v) + accCompensation(v) *)
abbreviation "SB v \<equiv> stopDist v + accCompensation v"

(* initial(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) & b>0 & A>=0 & ep>=0) *)
abbreviation "initial m' z v \<equiv> (v \<ge> 0 \<and> (m' - z) \<ge> stopDist v)" (* Initial states *)

(* Bool safe(Real m, Real z, Real v, Real d) <-> (z >= m -> v <= d) *)
abbreviation "safe m' z v \<delta> \<equiv> z \<ge> m' \<longrightarrow> v \<le> \<delta>" 

(* Bool loopInv(Real m, Real z, Real v) <-> (v >= 0 & m-z >= stopDist(v) *)
abbreviation "loopInv m' z v \<equiv> v \<ge> 0 \<and> m' - z \<ge> stopDist v" (* always maintain sufficient stopping distance *)

(*HP ctrl ::= {?m - z <= SB(v); a := -b; ++ ?m - z >= SB(v); a :=  A; *)
abbreviation "ctrl \<equiv> \<lceil>\<lambda>s::real^4. m - s$1 \<le> SB (s$2)\<rceil>;(3 ::= (\<lambda>s. -b)) \<union> 
 \<lceil>\<lambda>s. m - s$1 \<ge> SB (s$2)\<rceil>;(3 ::= (\<lambda>s. A))" (* train controller *)

(* HP drive ::= {t := 0;{z'=v, v'=a, t'=1  & v >= 0 & t <= ep} *)
abbreviation "drive \<equiv> (4 ::= (\<lambda>s. 0));
  (x\<acute>= (\<lambda>s::real^4. \<chi> i. if i=1 then s$2 else (if i=2 then s$3 else (if i=3 then 0 else 1))) 
  & (\<lambda>s. s$2 \<ge> 0 \<and> s$4 \<le> \<epsilon>) on {0..} UNIV @ 0)"

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> t"
    and "v\<^sup>2 / (2 \<cdot> b) + (A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> v)/ b + (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> v)) \<le> m - x" (is "?expr1 \<le> m - x")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "(A \<cdot> t + v)\<^sup>2/(2 \<cdot> b) \<le> m - (A \<cdot> t\<^sup>2/2 + v \<cdot> t + x)" (is "?lhs \<le> ?rhs")
proof-
  have "2\<cdot>b\<cdot>(v\<^sup>2/(2\<cdot>b) + (A\<cdot>(A\<cdot>\<epsilon>\<^sup>2/2+\<epsilon>\<cdot>v)/b + (A\<cdot>\<epsilon>\<^sup>2/2+\<epsilon>\<cdot>v))) \<le> 2\<cdot>b\<cdot>(m-x)" (is "?expr2 \<le> 2\<cdot>b\<cdot>(m-x)")
    using \<open>0 < b\<close> mult_left_mono[OF \<open>?expr1 \<le> m - x\<close>, of "2 \<cdot> b"] by auto
  also have "?expr2 = v\<^sup>2 +  2 \<cdot> A \<cdot> (A \<cdot> \<epsilon>\<^sup>2 / 2 + \<epsilon> \<cdot> v) + b \<cdot> A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> b \<cdot> \<epsilon> \<cdot> v"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  also have "... = v\<^sup>2 +  A^2 \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> A \<cdot> \<epsilon> \<cdot> v + b \<cdot> A \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> b \<cdot> \<epsilon> \<cdot> v"
    by (auto simp: field_simps power2_eq_square)
  finally have obs: "v\<^sup>2 +  A\<^sup>2\<cdot>\<epsilon>\<^sup>2 + 2\<cdot>A\<cdot>\<epsilon>\<cdot>v + b\<cdot>A\<cdot>\<epsilon>\<^sup>2 + 2\<cdot>b\<cdot>\<epsilon>\<cdot>v \<le> 2\<cdot>b\<cdot>(m-x)" (is "?expr3 \<epsilon> \<le> 2\<cdot>b\<cdot>(m-x)") .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "v\<^sup>2 + A\<^sup>2 \<cdot> t\<^sup>2 + b \<cdot> A \<cdot> t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 \<cdot> \<epsilon>\<^sup>2 + b \<cdot> A \<cdot> \<epsilon>\<^sup>2"
    using power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2]
    by (smt assms(1,2) mult_less_cancel_left zero_compare_simps(4) zero_le_power) 
  hence "v\<^sup>2 + A\<^sup>2 \<cdot> t\<^sup>2 + 2 \<cdot> A \<cdot> t \<cdot> v + b \<cdot> A \<cdot> t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 \<cdot> \<epsilon>\<^sup>2 + 2 \<cdot> A \<cdot> \<epsilon> \<cdot> v + b \<cdot> A \<cdot> \<epsilon>\<^sup>2"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> by (smt mult_left_mono mult_right_mono) 
  hence "?expr3 t \<le> 2 \<cdot> b \<cdot> (m - x)"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> obs by (smt mult_right_mono real_mult_le_cancel_iff2) 
  hence "A\<^sup>2 \<cdot> t\<^sup>2 + v\<^sup>2 + 2 \<cdot> A \<cdot> t \<cdot> v \<le> 2 \<cdot> b \<cdot> m - b \<cdot> A \<cdot> t\<^sup>2 - 2 \<cdot> b \<cdot> t \<cdot> v - 2 \<cdot> b \<cdot> x"
    by (simp add: right_diff_distrib)
  hence "(A \<cdot> t + v)\<^sup>2 \<le> 2 \<cdot> b \<cdot> m - b \<cdot> A \<cdot> t\<^sup>2 - 2 \<cdot> b \<cdot> t \<cdot> v - 2 \<cdot> b \<cdot> x"
    unfolding cross3_simps(29)[of A t 2] power2_sum[of "A\<cdot>t" v] by (simp add: mult.assoc)
  hence "?lhs \<le> (2 \<cdot> b \<cdot> m - b \<cdot> A \<cdot> t\<^sup>2 - 2 \<cdot> b \<cdot> t \<cdot> v - 2 \<cdot> b \<cdot> x)/(2 \<cdot> b)" (is "_ \<le> ?expr4")
    using \<open>0 < b\<close> divide_right_mono by fastforce
  also have "?expr4 = ?rhs"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  finally show "?lhs \<le> ?rhs" .
qed

(* Safety specification of the form: initial -> [{ctrl;plant}*]safe *)
lemma "b > 0 \<Longrightarrow> A \<ge> 0 \<Longrightarrow> \<epsilon> \<ge> 0 \<Longrightarrow> 
  \<lceil>\<lambda>s. initial m (s$1) (s$2)\<rceil> \<le> wp (LOOP ctrl;drive INV (\<lambda>s. loopInv m (s$1) (s$2))) \<lceil>\<lambda>s. s$1 \<le> m\<rceil>"
  apply (rule wp_loopI)
    apply (simp_all add: wp_choice local_flow.wp_g_ode_subset[OF local_flow_STTT_Ex5] del: rel_aka.fbox_add2, safe)
    apply (smt divide_le_cancel divide_minus_left not_sum_power2_lt_zero)
   apply(auto simp: field_simps power2_eq_square)[1]
  using ETCS_arith1 by force

end

end