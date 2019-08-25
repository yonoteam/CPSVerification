theory cat2rel
  imports
  "../hs_prelims_dyn_sys"
  "../../afpModified/VC_KAD"

begin


chapter\<open> Hybrid System Verification with relations \<close>

\<comment> \<open>We start by deleting some conflicting notation.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Relation.Domain ("r2s")
        and VC_KAD.gets ("_ ::= _" [70, 65] 61)
        and cond_sugar ("IF _ THEN _ ELSE _ FI" [64,64,64] 63)

notation Id ("skip")
     and cond_sugar ("IF _ THEN _ ELSE _" [64,64,64] 63)


section\<open> Verification of regular programs \<close>

text \<open>Properties of the forward box operator. \<close>

lemma wp_rel: "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
  have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
    by (simp add: wp_trafo pointfree_idE)
  thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
    by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

lemma p2r_r2p_wp: "\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  apply(subst d_p2r[symmetric])
  using wp_simp[symmetric, of R P] by blast

lemma p2r_r2p_simps: 
  "\<lfloor>\<lceil>P \<sqinter> Q\<rceil>\<rfloor> = (\<lambda> s. \<lfloor>\<lceil>P\<rceil>\<rfloor> s \<and> \<lfloor>\<lceil>Q\<rceil>\<rfloor> s)"
  "\<lfloor>\<lceil>P \<squnion> Q\<rceil>\<rfloor> = (\<lambda> s. \<lfloor>\<lceil>P\<rceil>\<rfloor> s \<or> \<lfloor>\<lceil>Q\<rceil>\<rfloor> s)"
  "\<lfloor>\<lceil>P\<rceil>\<rfloor> = P"
  unfolding p2r_def r2p_def by (auto simp: fun_eq_iff)

text\<open> Next, we introduce assignments and their @{text "wp"}. \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a \<equiv> (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma wp_assign [simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)\<rceil>"
  unfolding wp_rel vec_upd_def assign_def by (auto simp: fun_upd_def)

lemma assignD: "((s,s') \<in> (x ::= e)) = (s'$ x = e s \<and> (\<forall>y. y \<noteq> x \<longrightarrow> s' $ y = s $ y))"
  unfolding vec_upd_def assign_def by (simp, subst vec_eq_iff) auto
 

text\<open> The @{text "wp"} of the composition was already obtained in KAD.Antidomain\_Semiring:
@{thm fbox_mult[no_vars]}. \<close>

text\<open> There is also already an implementation of the conditional operator @{thm cond_def[no_vars]} 
and its @{text "wp"}: @{thm fbox_cond[no_vars]}. \<close>

text\<open> We also deal with finite iteration. \<close>

context antidomain_kleene_algebra
begin

lemma plus_inv: "i \<le> |x] i \<Longrightarrow> j \<le> |x] j \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  by (metis ads_d_def dka.dsr5 fbox_simp fbox_subdist join.sup_mono order_trans)

lemma mult_inv: "d i \<le> |x] d i \<Longrightarrow> d j \<le> |x] d j \<Longrightarrow> (d i \<cdot> d j) \<le> |x] (d i \<cdot> d j)"
  using local.fbox_demodalisation3 local.fbox_frame local.fbox_simp by auto

lemma fbox_stari: 
  assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
  shows "d p \<le> |x\<^sup>\<star>] q"
   by (meson assms local.dual_order.trans fbox_iso fbox_star_induct_var)

definition loopi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma fbox_loopi: "d p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |loop x inv i] q"
  unfolding loopi_def using fbox_stari by blast

end

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP R INV I \<equiv> rel_antidomain_kleene_algebra.loopi R \<lceil>I\<rceil>"

lemma wp_loopI: "\<lceil>P\<rceil> \<subseteq> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> wp R \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> wp (LOOP R INV I) \<lceil>Q\<rceil>"
  using rel_antidomain_kleene_algebra.fbox_loopi[of "\<lceil>P\<rceil>"] by auto


section\<open> Verification of hybrid programs \<close>


subsection \<open>Verification by providing evolution\<close>

definition g_evol :: "(real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a rel" ("EVOL")
  where "EVOL \<phi> G T = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G T}"

lemma wp_g_dyn[simp]: "wp (EVOL \<phi> G T) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding wp_rel g_evol_def g_orbit_eq by auto


subsection \<open>Verification by providing solutions\<close>

definition g_ode :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

lemma wp_g_orbital: "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>X\<in>Sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq wp_rel ivp_sols_def image_le_pred g_ode_def by auto

context local_flow
begin

lemma wp_g_ode: "wp (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  unfolding wp_g_orbital apply(clarsimp, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE)
  using in_ivp_sols apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma wp_orbit: "wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s))\<rceil>"
  unfolding orbit_def wp_g_ode g_ode_def[symmetric] by auto

end


subsection\<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma wp_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>H\<rceil>"
  unfolding wp_g_orbital using assms by auto

lemma wp_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule order.trans)
  using assms(2) apply(rule order.trans)
  apply(rule rel_antidomain_kleene_algebra.fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv[simp]: "(\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_orbital image_le_pred by(auto simp: p2r_def)

lemma wp_g_odei: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def apply(rule_tac b="wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" in order.trans)
   apply(rule_tac I="I" in wp_g_orbital_inv, simp_all)
  apply(subst wp_g_orbital_guard, simp)
  by (rule rel_antidomain_kleene_algebra.fbox_iso, simp)


subsection\<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_ode[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_ode, auto)

lemma diff_weak_axiom: "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_orbital image_def by force

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: g_orbital_eq g_ode_def)

lemma wp_g_evol_IdD:
  assumes "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
    and "\<forall>\<tau>\<in>(down T t). (s, x \<tau>) \<in> (x\<acute>= f & G on T S @ t\<^sub>0)"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> g_orbital f G T S t\<^sub>0 s" 
    using assms(2) unfolding g_ode_def by blast
  also have "\<forall>y. y \<in> (g_orbital f G T S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_rel g_ode_def by(auto simp: p2r_def)
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule subset_antisym)
  show "(x\<acute>=f & G on T S @ t\<^sub>0) \<subseteq> (x\<acute>=f & \<lambda>s. G s \<and> C s on T S @ t\<^sub>0)"
  proof(clarsimp simp: g_ode_def)
    fix s and s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"(\<P> X (down T \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using wp_g_evol_IdD[OF assms(3)] unfolding g_ode_def by blast
    thus "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce
  qed
next show "(x\<acute>=f & \<lambda>s. G s \<and> C s on T S @ t\<^sub>0) \<subseteq> (x\<acute>=f & G on T S @ t\<^sub>0)"  
    by (auto simp: g_orbital_eq g_ode_def)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def image_le_pred g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_rel, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_rel) (auto simp: g_ode_def)
qed

text\<open>The rules of dL\<close>

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = \<lceil>\<lambda>x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  by (subst diff_solve_axiom[of UNIV]) auto

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) unfolding image_le_pred by simp

lemma DW: "wp (x\<acute>= f & G) \<lceil>Q\<rceil> = wp (x\<acute>= f & G) \<lceil>\<lambda>s. G s \<longrightarrow> Q s\<rceil>"
  by (rule diff_weak_axiom)
  
lemma dW: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  by (rule diff_weak_rule)

lemma DC:
  assumes "wp (x\<acute>= f & G) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>= f & G) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  apply (rule diff_cut_axiom) 
  using assms by auto

lemma dC:
  assumes "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>C\<rceil>"
    and "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f UNIV UNIV 0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  apply(rule wp_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding wp_diff_inv using assms(2) .

end