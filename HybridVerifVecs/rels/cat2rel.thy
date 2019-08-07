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

section\<open> Verification of regular programs \<close>

text\<open> Below we explore the behavior of the forward box operator from the antidomain kleene algebra
with the lifting ($\lceil-\rceil$*) operator from predicates to relations @{thm p2r_def[no_vars]} 
and its dropping counterpart @{thm r2p_def[no_vars]}. \<close>

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

text\<open> Next, we introduce assignments and compute their @{text "wp"}. \<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd x i a \<equiv> vec_lambda ((vec_nth x)(i := a))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma wp_assign [simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (vec_upd s x (e s))\<rceil>"
  by(auto simp: rel_antidomain_kleene_algebra.fbox_def rel_ad_def p2r_def)

lemma wp_assign_var [simp]: "\<lfloor>wp (x ::= e) \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. Q (vec_upd s x (e s)))"
  by(subst wp_assign, simp add: pointfree_idE)

text\<open> The @{text "wp"} of the composition was already obtained in KAD.Antidomain\_Semiring:
@{thm fbox_mult[no_vars]}. \<close>

text\<open> There is also already an implementation of the conditional operator @{thm cond_def[no_vars]} 
and its @{text "wp"}: @{thm fbox_cond[no_vars]}. \<close>

text\<open> Finally, we add a wp-rule for a simple finite iteration. \<close>

lemma (in antidomain_kleene_algebra) fbox_starI: 
  assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
  shows "d p \<le> |x\<^sup>\<star>] q"
proof-
  have "d i \<le> |x] (d i)"
    using \<open>d i \<le> |x] i\<close> local.fbox_simp by auto
  hence "|1] p \<le> |x\<^sup>\<star>] i" 
    using \<open>d p \<le> d i\<close> by (metis (no_types) dual_order.trans 
        fbox_one fbox_simp fbox_star_induct_var)
  thus ?thesis 
    using \<open>d i \<le> d q\<close> by (metis (full_types) fbox_mult 
        fbox_one fbox_seq_var fbox_simp)
qed

lemma rel_ad_mka_starI:
  assumes "P \<subseteq> I" and "I \<subseteq> wp R I" and "I \<subseteq> Q"
  shows "P \<subseteq> wp (R\<^sup>*) Q"
proof-
  have "wp R I \<subseteq> Id"
    by (simp add: rel_antidomain_kleene_algebra.a_subid rel_antidomain_kleene_algebra.fbox_def)
  hence "P \<subseteq> Id" 
    using assms(1,2) by blast
  hence "rdom P = P" 
    by (metis d_p2r p2r_surj)
  also have "rdom P \<subseteq> wp (R\<^sup>*) Q"
    by (metis \<open>wp R I \<subseteq> Id\<close> assms d_p2r p2r_surj rel_antidomain_kleene_algebra.dka.dom_iso 
        rel_antidomain_kleene_algebra.fbox_starI)
  ultimately show ?thesis 
    by blast
qed


section\<open> Verification of hybrid programs \<close>

abbreviation g_evolution ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>=f & G on T S @ t\<^sub>0) \<equiv> {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0)"

subsection \<open>Verification by providing solutions\<close>

lemma wp_g_evolution: "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>= 
  \<lceil>\<lambda> s. \<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq wp_rel ivp_sols_def image_le_pred by auto

context local_flow
begin

lemma wp_orbit: 
  assumes "S = UNIV"
  shows "wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
  unfolding wp_rel apply(simp, safe)
  using orbit_eq unfolding assms by(auto simp: wp_rel)

lemma wp_g_orbit: 
  assumes "S = UNIV"
  shows "wp (x\<acute>=f & G on T S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  using g_orbital_collapses unfolding assms by (auto simp: wp_rel)

end

subsection\<open> Verification with differential invariants \<close>

lemma wp_g_evolution_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>H\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding wp_g_evolution using assms by auto

lemma wp_g_evolution_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule order.trans)
  using assms(2) apply(rule order.trans)
  apply(rule rel_antidomain_kleene_algebra.fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv: "(\<lceil>I\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_evolution image_le_pred by(auto simp: p2r_def)

context local_flow
begin

lemma wp_diff_inv_eq:
  assumes "S = UNIV"
  shows "(\<lceil>I\<rceil> = wp (x\<acute>=f & (\<lambda>s. True) on T S @ 0) \<lceil>I\<rceil>) = diff_invariant I f T S 0 (\<lambda>s. True)"
  unfolding diff_invariant_eq[OF assms] wp_g_orbit[OF assms] image_le_pred 
  using in_ivp_sols ivp(2) init_time unfolding assms by auto

lemma wp_orbit_inv_eq:
  assumes "S = UNIV"
  shows "(\<lceil>I\<rceil> = wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>I\<rceil>) = (\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s))"
  unfolding orbit_def wp_diff_inv_eq[OF assms] diff_invariant_eq[OF assms] 
  using in_ivp_sols ivp(2) init_time unfolding assms by auto

end


subsection\<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_orbit[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_orbit, auto)

lemma diff_weak_axiom: "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_evolution image_def by force

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: g_orbital_eq)

lemma wp_g_orbit_IdD:
  assumes "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
    and "\<forall>\<tau>\<in>(down T t). (s, x \<tau>) \<in> (x\<acute>=f & G on T S @ t\<^sub>0)"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> g_orbital f G T S t\<^sub>0 s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f G T S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_rel by(auto simp: p2r_def)
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, clarsimp, rule subset_antisym, safe)
  {fix s and s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"(\<P> X (down T \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using wp_g_orbit_IdD[OF assms(3)] by blast
    hence "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce}
  thus "\<And>s s'. s' \<in> g_orbital f G T S t\<^sub>0 s \<Longrightarrow> s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    by blast
next show "\<And>s s'. s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s \<Longrightarrow> s' \<in> g_orbital f G T S t\<^sub>0 s"  
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def image_le_pred, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_rel, auto)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_rel) auto
qed

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = \<lceil>\<lambda>x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  by (subst diff_solve_axiom[of UNIV]) auto

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) unfolding image_le_pred by simp

lemma DW: "wp (x\<acute>=f & G) \<lceil>Q\<rceil> = wp (x\<acute>=f & G) \<lceil>\<lambda>s. G s \<longrightarrow> Q s\<rceil>"
  by (rule diff_weak_axiom)
  
lemma dW: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  by (rule diff_weak_rule)

lemma DC:
  assumes "wp (x\<acute>=f & G) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>=f & G) \<lceil>Q\<rceil> = wp (x\<acute>=f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  apply (rule diff_cut_axiom) 
  using assms by auto

lemma dC:
  assumes "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>C\<rceil>"
    and "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f UNIV UNIV 0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule wp_g_evolution_inv[OF assms(1) _ assms(3)])
  unfolding wp_diff_inv using assms(2) .

end