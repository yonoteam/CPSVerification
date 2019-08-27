theory kat2rel
  imports
  "../hs_prelims_dyn_sys"
  "../../afpModified/VC_KAT"

begin


chapter\<open> Hybrid System Verification with relations \<close>

\<comment> \<open>We start by deleting some conflicting notation.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Relation.Domain ("r2s")
        and VC_KAT.gets ("_ ::= _" [70, 65] 61)
        and tau ("\<tau>")
        and if_then_else_sugar  ("IF _ THEN _ ELSE _ FI" [64,64,64] 63)

notation Id ("skip")
     and if_then_else_sugar ("IF _ THEN _ ELSE _" [64,64,64] 63)

section\<open> Verification of regular programs \<close>

text\<open> Below we explore the behavior of the forward box operator from the antidomain kleene algebra
with the lifting ($\lceil-\rceil$*) operator from predicates to relations @{thm p2r_def[no_vars]} 
and its dropping counterpart @{thm r2p_def[no_vars]}. \<close>

thm sH_H

lemma sH_weaken_pre: "rel_kat.H \<lceil>P2\<rceil> R \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P1\<rceil> \<subseteq> \<lceil>P2\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P1\<rceil> R \<lceil>Q\<rceil>"
  unfolding sH_H by auto

text\<open> Next, we introduce assignments and compute their Hoare triple. \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a \<equiv> (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma sH_assign_iff [simp]: "rel_kat.H \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding sH_H vec_upd_def assign_def by (auto simp: fun_upd_def)

text\<open> Next, the Hoare rule of the composition:\<close>

lemma sH_relcomp: "rel_kat.H \<lceil>P\<rceil> X \<lceil>R\<rceil> \<Longrightarrow> rel_kat.H \<lceil>R\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil>"
  using rel_kat.H_seq_swap by force

text\<open> There is also already an implementation of the conditional operator 
@{thm ifthenelse_def[no_vars]} and its Hoare triple rule: @{thm sH_cond[no_vars]}. \<close>

text\<open> Finally, we add a Hoare triple rule for a simple finite iteration. \<close>

context kat
begin

lemma H_star_induct: "H (t i) x i \<Longrightarrow> H (t i) (x\<^sup>\<star>) i"
  unfolding H_def by (simp add: local.star_sim2)

lemma H_stari: 
  assumes "t p \<le> t i" and "H (t i) x i" and "t i \<le> t q"
  shows "H (t p) (x\<^sup>\<star>) q"
proof-
  have "H (t i) (x\<^sup>\<star>) i"
    using assms(2) H_star_induct by blast
  hence "H (t p) (x\<^sup>\<star>) i"
    apply(simp add: H_def) 
    using assms(1) local.phl_cons1 by blast 
  thus ?thesis 
    unfolding H_def using assms(3) local.phl_cons2 by blast 
qed

definition loopi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma sH_loopi: "t p \<le> t i \<Longrightarrow> H (t i) x i \<Longrightarrow> t i \<le> t q \<Longrightarrow> H (t p) (loop x inv i) q"
  unfolding loopi_def using H_stari by blast

end

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP R INV I \<equiv> rel_kat.loopi R \<lceil>I\<rceil>"

lemma sH_loopI: "\<lceil>P\<rceil> \<subseteq> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>I\<rceil> R \<lceil>I\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (LOOP R INV I) \<lceil>Q\<rceil>"
  using rel_kat.sH_loopi[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" R "\<lceil>Q\<rceil>"] by auto


section\<open> Verification of hybrid programs \<close>

subsection \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> 'b rel" ("EVOL")
  where "EVOL \<phi> G T = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G T}"

lemma sH_g_dyn[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "rel_kat.H \<lceil>P\<rceil> (EVOL \<phi> G T) \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding sH_H g_evol_def g_orbit_eq by auto

subsection \<open>Verification by providing solutions\<close>

definition g_ode :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

lemma sH_g_orbital: 
  "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  (\<forall>s. P s \<longrightarrow> (\<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)))"
  unfolding g_orbital_eq g_ode_def image_le_pred sH_H by auto

context local_flow
begin

lemma sH_g_orbit: "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s \<in> S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding sH_g_orbital apply(clarsimp, safe)
   apply(erule_tac x=s in allE, simp, erule_tac x="\<lambda>t. \<phi> t s" in ballE)
  using in_ivp_sols apply(force, force)
  apply(erule_tac x=s in ballE, simp)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s")
   apply(simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma sH_orbit: 
  "rel_kat.H \<lceil>P\<rceil> ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = (\<forall>s \<in> S. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  using sH_g_orbit unfolding orbit_def g_ode_def by auto

end


subsection\<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma sH_g_orbital_guard: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>R\<rceil>" 
  using assms unfolding g_orbital_eq sH_H ivp_sols_def g_ode_def by auto

lemma sH_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "rel_kat.H \<lceil>I\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in rel_kat.H_cons_1, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in rel_kat.H_cons_2, simp)
  using assms(2) by simp

lemma sH_diff_inv[simp]: "rel_kat.H \<lceil>I\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq sH_H g_orbital_eq image_le_pred g_ode_def by auto

lemma sH_g_odei: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> rel_kat.H \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  rel_kat.H \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def apply(rule_tac q'="\<lceil>\<lambda>s. I s \<and> G s\<rceil>" in rel_kat.H_cons_2, simp)
  apply(subst sH_g_orbital_guard[symmetric], force)
  by (rule_tac I="I" in sH_g_orbital_inv, simp_all)

subsection\<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c))"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  apply(subst local_flow.sH_g_orbit[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.sH_g_orbit, auto)

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms unfolding g_orbital_eq sH_H ivp_sols_def g_ode_def by auto

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C:"rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & (\<lambda> s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst sH_H, simp add: g_orbital_eq p2r_def image_le_pred g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) sH_H, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) sH_H) (auto simp: g_ode_def)
qed

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

end