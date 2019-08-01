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
  \<lceil>\<lambda> s. \<forall>x\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (G \<rhd> x (down T t)) \<longrightarrow> Q (x t)\<rceil>"
  unfolding g_orbital_eq wp_rel ivp_sols_def by auto

lemma wp_guard_eq: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>R\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding wp_g_evolution using assms by auto

context local_flow
begin

lemma wp_orbit: 
  assumes "S = UNIV"
  shows "wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
  using orbit_eq unfolding assms by(auto simp: wp_rel)

lemma wp_g_orbit: 
  assumes "S = UNIV"
  shows "wp (x\<acute>=f & G on T S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (G \<rhd> (\<lambda>t. \<phi> t s) (down T t)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  using g_orbit_eq unfolding assms by (auto simp: wp_rel)

lemma invariant_set_eq_dl_invariant:
  assumes "S = UNIV"
  shows "(\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s)) = (\<lceil>I\<rceil> = wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>I\<rceil>)"
  unfolding wp_orbit[OF assms] apply simp
  using ivp(2) unfolding assms apply simp
  using init_time by auto

end

text\<open> The previous theorem allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (G \<rhd> (\<lambda>\<tau>. \<phi> \<tau> s) (down T t)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_orbit, auto)

lemma line_is_local_flow: 
  "0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> local_flow (\<lambda> s. c) T UNIV (\<lambda> t s. s + t *\<^sub>R c)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
   apply(rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)
  apply(rule_tac f'1="\<lambda> s. 0" and g'1="\<lambda> s. c" in derivative_intros(191))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma line_DS: fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> x. \<forall>t\<in>T. (G \<rhd> (\<lambda>\<tau>. x + \<tau> *\<^sub>R c) (down T t)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_orbit[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto
  

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>

lemma DW: "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  by (auto intro: g_orbitalD simp: wp_rel)

lemma dWeakening: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: g_orbital_eq)

subsubsection\<open> Differential Cut \<close>

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

lemma DC:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, clarsimp, rule subset_antisym, safe)
  {fix s and s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and x where x_ivp: "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
      "x \<in> T \<rightarrow> S" and guard_x:"G \<rhd> x (down T \<tau>)" and "s' = x \<tau>" "\<tau> \<in> T"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by clarsimp metis
    hence "\<forall>t\<in>(down T \<tau>).\<forall>\<tau>\<in>(down T t). G (x \<tau>)"
      by (simp add: closed_segment_eq_real_ivl)
    also have "\<forall>\<tau>\<in>(down T \<tau>). \<tau> \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). x t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by meson
    hence "C \<rhd> x (down T \<tau>)" 
      using wp_g_orbit_IdD[OF assms(3)] by blast
    hence "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>s' = x \<tau>\<close> by fastforce}
  thus "\<And>s s'. s' \<in> g_orbital f G T S t\<^sub>0 s \<Longrightarrow> s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    by blast
next show "\<And>s s'. s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s \<Longrightarrow> s' \<in> g_orbital f G T S t\<^sub>0 s" 
    by (auto simp: g_orbital_def)
qed

lemma dCut:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "P (x t\<^sub>0)" and "\<tau> \<in> T"
    and x_solves:"D x = (\<lambda>t. f (x t)) on T" "x \<in> T \<rightarrow> S" 
    and guard_x:"\<forall>t. t \<in> T \<and> t \<le> \<tau> \<longrightarrow> G (x t)"
  hence "\<forall>r\<in>(down T \<tau>). x r \<in> (g_orbital f G T S t\<^sub>0) (x t\<^sub>0)"
    by (auto intro!: g_orbitalI x_solves \<open>\<tau> \<in> T\<close>)
  hence "\<forall>t\<in>(down T \<tau>). C (x t)" 
    using wp_C \<open>P (x t\<^sub>0)\<close> by (subst (asm) wp_rel, auto)
  hence "x \<tau> \<in> (g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0) (x t\<^sub>0)"
    apply(simp) apply(rule g_orbitalI)
    using guard_x by (auto intro!: x_solves \<open>\<tau> \<in> T\<close>)
  thus "Q (x \<tau>)"
    using \<open>P (x t\<^sub>0)\<close> wp_Q by (subst (asm) wp_rel) auto
qed

subsubsection\<open> Differential Invariant \<close>

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T S from t\<^sub>0" and "I\<^sub>S = (\<lambda>s. s\<in>S \<and> I s)"
  shows "\<lceil>I\<^sub>S\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<^sub>S\<rceil>"
  using assms(1) unfolding diff_invariant_def wp_g_evolution 
  by(auto simp: p2r_def assms(2)  ivp_sols_def)

lemma dInvariant_converse:
  assumes "\<lceil>\<lambda>s. s\<in>S \<and> I s\<rceil> \<le> wp (x\<acute>=f & (\<lambda>s. True) on T S @ t\<^sub>0) \<lceil>\<lambda>s. s\<in>S \<and> I s\<rceil>"
  shows "I is_diff_invariant_of f along T S from t\<^sub>0"
  using assms unfolding invariant_to_set wp_rel by(auto simp: p2r_def)

lemma dI:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  apply(rule_tac C="I" in dCut[OF Thyp])
  using order.trans[OF assms(3,4)] apply assumption
  apply(rule dWeakening)
  using assms by auto

end