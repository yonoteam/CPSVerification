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

section\<open> Verification of regular programs \<close>

text\<open> Below we explore the behavior of the forward box operator from the antidomain kleene algebra
with the lifting ($\lceil-\rceil$*) operator from predicates to relations @{thm p2r_def[no_vars]} 
and its dropping counterpart @{thm r2p_def[no_vars]}. \<close>

thm sH_H

lemma sH_weaken_pre: "rel_kat.H \<lceil>P2\<rceil> R \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P1\<rceil> \<subseteq> \<lceil>P2\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P1\<rceil> R \<lceil>Q\<rceil>"
  unfolding sH_H by auto

text\<open> Next, we introduce assignments and compute their Hoare triple. \<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd x i a \<equiv> vec_lambda ((vec_nth x)(i := a))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma sH_assign_iff [simp]: "rel_kat.H \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (vec_upd s x (e s)))"
  unfolding sH_H by simp

text\<open> Next, the Hoare rule of the composition:\<close>

lemma sH_relcomp: "rel_kat.H \<lceil>P\<rceil> X \<lceil>R\<rceil> \<Longrightarrow> rel_kat.H \<lceil>R\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil>"
  using rel_kat.H_seq_swap by force

text\<open> There is also already an implementation of the conditional operator 
@{thm ifthenelse_def[no_vars]} and its Hoare triple rule: @{thm sH_cond[no_vars]}. \<close>

text\<open> Finally, we add a Hoare triple rule for a simple finite iteration. \<close>

lemma (in kat) H_star_self: "H (t i) x i \<Longrightarrow> H (t i) (x\<^sup>\<star>) i"
  unfolding H_def by (simp add: local.star_sim2)

lemma (in kat) H_star: 
  assumes "t p \<le> t i" and "H (t i) x i" and "t i \<le> t q"
  shows "H (t p) (x\<^sup>\<star>) q"
proof-
  have "H (t i) (x\<^sup>\<star>) i"
    using assms(2) H_star_self by blast
  hence "H (t p) (x\<^sup>\<star>) i"
    apply(simp add: H_def) 
    using assms(1) local.phl_cons1 by blast 
  thus ?thesis 
    unfolding H_def using assms(3) local.phl_cons2 by blast 
qed

lemma sH_star:
  assumes "\<lceil>P\<rceil> \<subseteq> \<lceil>I\<rceil>" and "rel_kat.H \<lceil>I\<rceil> R \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (R\<^sup>*) \<lceil>Q\<rceil>"
  using rel_kat.H_star[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" R "\<lceil>Q\<rceil>"] assms by auto

section\<open> Verification of hybrid programs \<close>

abbreviation g_evolution ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>=f & G on T S @ t\<^sub>0) \<equiv> {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0)"

subsection \<open>Verification by providing solutions\<close>

lemma sH_g_evolution: 
  assumes "\<forall>s. P s \<longrightarrow> (\<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<P> X (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (X t))"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms unfolding g_orbital_eq(1) sH_H by auto

context local_flow
begin

lemma sH_orbit: 
  assumes "S = UNIV" and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s))"
  shows "rel_kat.H \<lceil>P\<rceil> ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil>"
  using orbit_eq assms(2) unfolding assms(1) sH_H by auto

lemma sH_g_orbit: 
  assumes "S = UNIV" and "\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ 0) \<lceil>Q\<rceil>"
  using g_orbital_collapses assms(2) unfolding assms(1) by (auto simp: sH_H)

end


subsection\<open> Verification with differential invariants \<close>

lemma sH_g_evolution_guard: 
  assumes "R = (\<lambda>s. G s \<and> Q s)" and "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>" 
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>R\<rceil>"
  using assms unfolding g_orbital_eq sH_H ivp_sols_def by auto

lemma sH_g_evolution_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "rel_kat.H \<lceil>I\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in rel_kat.H_cons_1, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in rel_kat.H_cons_2, simp)
  using assms(2) by simp

lemma sH_diff_inv: "rel_kat.H \<lceil>I\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq sH_H g_orbital_eq by auto

context local_flow
begin

lemma wp_diff_inv_eq:
  assumes "S = UNIV"
  shows "(rel_kat.H  \<lceil>I\<rceil> (x\<acute>=f & (\<lambda>s. True) on T S @ 0) \<lceil>I\<rceil>) = diff_invariant I f T S 0 (\<lambda>s. True)"
  unfolding diff_invariant_eq[OF assms] sH_H using g_orbital_collapses unfolding assms 
  by clarsimp force

lemma wp_orbit_inv_eq:
  assumes "S = UNIV"
  shows "(rel_kat.H  \<lceil>I\<rceil>  ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>I\<rceil>) = (\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s))"
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
  using assms unfolding g_orbital_eq sH_H ivp_sols_def by auto

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C:"rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & (\<lambda> s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst sH_H, simp add: g_orbital_eq p2r_def image_le_pred, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) sH_H, auto)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) sH_H) auto
qed

end