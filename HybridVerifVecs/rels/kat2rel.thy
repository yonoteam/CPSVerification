theory kat2rel
  imports
  "../hs_prelims_matrices"
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

text\<open> Next, we introduce assignments and compute their Hoare triple. \<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd x i a \<equiv> vec_lambda ((vec_nth x)(i := a))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma sH_assign_iff [simp]: "rel_kat.H \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (vec_upd s x (e s)))"
  unfolding sH_H by simp

(*lemma wp_assign_var [simp]: "\<lfloor>wp (x ::= e) \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. Q (vec_upd s x (e s)))"
  by(subst wp_assign, simp add: pointfree_idE)*)

text\<open> Next, the Hoare triple of the composition:\<close>

lemma sH_relcomp: "rel_kat.H \<lceil>P\<rceil> X \<lceil>R\<rceil> \<Longrightarrow> rel_kat.H \<lceil>R\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil>"
  using rel_kat.H_seq_swap by force

(* "|x \<cdot> y] q = |x] |y] q" *)

lemma "rel_kat.H \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil> = rel_kat.H \<lceil>P\<rceil> (X) {(s,s') |s s'. (s,s') \<in> Y \<longrightarrow> Q s' }"
  unfolding rel_kat.H_def apply(auto simp: subset_eq p2r_def Int_def)
  oops

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

subsection\<open> Verification by providing solutions \<close>

abbreviation guards :: "('a \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real set) \<Rightarrow> bool" ("_ \<rhd> _ _" [70, 65] 61) 
  where "G \<rhd> x T \<equiv> \<forall> r \<in> T. G (x r)"

definition "ivp_sols f T t\<^sub>0 s = {x |x. (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> t\<^sub>0 \<in> T}"

lemma ivp_solsI: 
  assumes "D x = (f \<circ> x) on T" "x t\<^sub>0 = s" "t\<^sub>0 \<in> T"
  shows "x \<in> ivp_sols f T t\<^sub>0 s"
  using assms unfolding ivp_sols_def by blast

lemma ivp_solsD:
  assumes "x \<in> ivp_sols f T t\<^sub>0 s"
  shows "D x = (f \<circ> x) on T"
    and "x t\<^sub>0 = s" and "t\<^sub>0 \<in> T"
  using assms unfolding ivp_sols_def by auto

definition "g_orbital f T t\<^sub>0 G s = \<Union> {{x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0..t} }|x. x \<in> ivp_sols f T t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f T t\<^sub>0 G s = 
  {x t |t x. t \<in> T \<and> (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> t\<^sub>0 \<in> T \<and> G \<rhd> x {t\<^sub>0..t}}"
  unfolding g_orbital_def ivp_sols_def by auto

lemma "g_orbital f T t\<^sub>0 G s = (\<Union> x \<in> ivp_sols f T t\<^sub>0 s. {x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0..t}})"
  unfolding g_orbital_def ivp_sols_def by auto

lemma g_orbitalI:
  assumes "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
    and "t\<^sub>0 \<in> T" "\<tau> \<in> T" and "G \<rhd> x {t\<^sub>0..\<tau>}"
  shows "x \<tau> \<in> g_orbital f T t\<^sub>0 G s"
  using assms unfolding g_orbital_def ivp_sols_def by blast

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f T t\<^sub>0 G s"
  obtains x and t where "x \<in> ivp_sols f T t\<^sub>0 s" 
  and "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
  and "x t = s'" and "t\<^sub>0 \<in> T" "t \<in> T" and "G \<rhd> x {t\<^sub>0..t}"
  using assms unfolding g_orbital_def ivp_sols_def by blast

abbreviation g_evol :: "(('a::banach) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow>'a pred \<Rightarrow> 'a rel" ("(1[x\<acute>=_]_ & _)") 
  where "[x\<acute>=f]T & G \<equiv> {(s,s'). s' \<in> g_orbital f T 0 G s}"

lemmas g_evol_def = g_orbital_eq[where t\<^sub>0=0]

context local_flow
begin

lemma in_ivp_sols: "(\<lambda>t. \<phi> t s) \<in> ivp_sols f T 0 s"
  by(auto intro: ivp_solsI simp: ivp init_time)

definition "orbit s = g_orbital f T 0 (\<lambda>s. True) s"

lemma orbit_eq[simp]: "orbit s = {\<phi> t s| t. t \<in> T}"
  unfolding orbit_def g_evol_def 
  by(auto intro: usolves_ivp intro!: ivp simp: init_time)

lemma g_orbital_collapses: 
  shows "g_orbital f T 0 G s = {\<phi> t s | t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0..t}}" (is "_ = ?gorbit")
proof(rule subset_antisym, simp_all only: subset_eq)
  {fix s' assume "s' \<in> g_orbital f T 0 G s"
    then obtain x and t where x_ivp:"D x = (\<lambda>t. f (x t)) on T" 
      "x 0 = s" and "x t = s'" and "t \<in> T" and guard:"G \<rhd> x {0..t}"
      unfolding g_orbital_eq by auto
    hence obs:"\<forall>\<tau>\<in>{0..t}. x \<tau> = \<phi> \<tau> s"
      using usolves_ivp[OF x_ivp]
      by (meson atLeastAtMost_iff init_time interval mem_is_interval_1_I) 
    hence "G \<rhd> (\<lambda>r. \<phi> r s) {0..t}"
      using guard by simp
    also have "\<phi> t s = x t"
      using usolves_ivp x_ivp \<open>t \<in> T\<close> by simp
    ultimately have "s' \<in> ?gorbit"
      using \<open>x t = s'\<close> \<open>t \<in> T\<close> by auto}
  thus "\<forall>s'\<in>g_orbital f T 0 G s. s' \<in> ?gorbit"
    by blast
next
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) {0..t}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> g_orbital f T 0 G s"
      by(auto intro: g_orbitalI simp: ivp init_time)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> g_orbital f T 0 G s"
    by blast
qed

lemma g_evol_collapses: "([x\<acute>=f]T & G) = {(s, \<phi> t s) | t s. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0..t}}"
  unfolding g_orbital_collapses by auto

lemma sH_orbit: 
  shows "rel_kat.H \<lceil>P\<rceil> {(s,s') | s s'. s' \<in> orbit s} \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  unfolding sH_H orbit_eq by auto

lemma sH_g_orbit: "rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = 
  (\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> Q (\<phi> t s)))"
  unfolding g_evol_collapses sH_H by auto

end

lemma (in local_flow) ivp_sols_collapse: "ivp_sols f T 0 s = {(\<lambda>t. \<phi> t s)}"
  apply(auto simp: ivp_sols_def ivp init_time fun_eq_iff)
  apply(rule unique_solution, simp_all add: ivp)
  oops

text\<open> The previous theorem allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f T L \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> Q (\<phi> t s))"
  shows "rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.sH_g_orbit, auto)

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>

lemma dWeakening: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]{0..\<tau>} & G) \<lceil>Q\<rceil>"
  using assms apply(subst sH_H)
  by(auto simp: g_evol_def)

subsubsection\<open> Differential Cut \<close>

theorem dCut:
  assumes wp_C:"rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]{0..\<tau>} & G) \<lceil>C\<rceil>"
    and wp_Q:"rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]{0..\<tau>} & (\<lambda> s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]{0..\<tau>} & G) \<lceil>Q\<rceil>"
proof(subst sH_H, simp add: g_orbital_eq p2r_def, clarsimp)
  fix \<tau>'::real and x::"real \<Rightarrow> 'a" 
  assume guard_x:"(\<forall> r \<in> {0..\<tau>'}. G (x r))" and "0 \<le> \<tau>'" and "\<tau>' \<le> \<tau>"
    and x_solves:"D x = (\<lambda>t. f (x t)) on {0..\<tau>}" and "P (x 0)"
  hence "\<forall>r\<in>{0..\<tau>'}.\<forall>\<tau>\<in>{0..r}. G (x \<tau>)"
    by auto
  hence "\<forall>r\<in>{0..\<tau>'}. x r \<in> g_orbital f {0..\<tau>} 0 G (x 0)"
    using g_orbitalI x_solves \<open>0 \<le> \<tau>'\<close> \<open>\<tau>' \<le> \<tau>\<close> by fastforce 
  hence "\<forall>r\<in>{0..\<tau>'}. C (x r)" 
    using wp_C \<open>P (x 0)\<close> by(subst (asm) sH_H, auto)
  hence "x \<tau>' \<in> g_orbital f {0..\<tau>} 0 (\<lambda>s. G s \<and> C s) (x 0)"
    using g_orbitalI x_solves guard_x \<open>0 \<le> \<tau>'\<close> \<open>\<tau>' \<le> \<tau>\<close> by fastforce
  from this \<open>P (x 0)\<close> and wp_Q show "Q (x \<tau>')"
    by(subst (asm) sH_H, auto)
qed

subsubsection\<open> Differential Invariant \<close>

definition diff_invariant :: "'a pred \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> bool" 
  ("(_)/ is'_diff'_invariant'_of (_)/ along (_)" [70,65]61) 
  where "I is_diff_invariant_of f along T \<equiv> 
  (\<forall>s. I s \<longrightarrow> (\<forall> x. x \<in> ivp_sols f T 0 s \<longrightarrow> (\<forall> t \<in> T. I (x t))))"

lemma invariant_to_set:
  shows "(I is_diff_invariant_of f along T) \<longleftrightarrow> (\<forall>s. I s \<longrightarrow> (g_orbital f T 0 (\<lambda>s. True) s) \<subseteq> {s. I s})"
  unfolding diff_invariant_def ivp_sols_def g_orbital_eq apply safe
   apply(erule_tac x="xa 0" in allE)
   apply(drule mp, simp_all)
  apply(erule_tac x="xa 0" in allE)
  apply(drule mp, simp_all add: subset_eq)
  apply(erule_tac x="xa t" in allE)
  by(drule mp, auto)

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T"
  shows "rel_kat.H \<lceil>I\<rceil> ([x\<acute>=f]T & G) \<lceil>I\<rceil>"
  using assms unfolding diff_invariant_def 
  by(auto simp: sH_H g_evol_def ivp_sols_def)

lemma dI:
  assumes "I is_diff_invariant_of f along {0..\<tau>}"
    and "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.H \<lceil>P\<rceil> ([x\<acute>=f]{0..\<tau>} & G) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac C="I" in dCut)
   apply(drule_tac G="G" in dInvariant)
  using assms(2) apply (simp add: sH_cons_1) 
  apply(rule dWeakening)
  using assms by auto

text\<open> Finally, we obtain some conditions to prove specific instances of differential invariants. \<close>

named_theorems diff_invariant_rules "compilation of rules for differential invariants."

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..\<tau>}) \<longrightarrow> 
  (\<forall>\<tau>\<in>{0..\<tau>}. (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = ((*\<^sub>R) 0) on {0..\<tau>}))"
  shows "(\<lambda>s. \<theta> s = \<nu> s) is_diff_invariant_of f along {0..\<tau>}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau>' assume tHyp:"0 \<le> \<tau>'" "\<tau>' \<le> \<tau>" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..\<tau>}" "\<theta> (x 0) = \<nu> (x 0)" 
  hence "\<forall> t \<in> {0..\<tau>'}. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R 0) at t within {0..\<tau>'}" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>t\<in>{0..\<tau>'}. \<theta> (x \<tau>') - \<nu> (x \<tau>') - (\<theta> (x 0) - \<nu> (x 0)) = (\<tau>' - 0) \<cdot> 0" 
    by (rule_tac mvt_very_simple) (auto simp: tHyp)
  thus "\<theta> (x \<tau>') = \<nu> (x \<tau>')" by (simp add: x_ivp(2))
qed

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..\<tau>}) \<longrightarrow> (\<forall>\<tau>\<in>{0..\<tau>}. \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>) \<and> 
  (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>r. \<theta>' (x r) - \<nu>' (x r)) on {0..\<tau>}))"
  shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_diff_invariant_of f along {0..\<tau>}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau>' assume tHyp:"0 \<le> \<tau>'" "\<tau>' \<le> \<tau>" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..\<tau>}" "\<nu> (x 0) \<le> \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0..\<tau>'}. (D (\<lambda>\<tau>'. \<theta> (x \<tau>') - \<nu> (x \<tau>')) \<mapsto> (\<lambda>\<tau>'. \<tau>' *\<^sub>R (\<theta>' (x r) - \<nu>' (x r))) 
  at r within {0..\<tau>'}) \<and> \<nu>' (x r) \<le> \<theta>' (x r)" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>r\<in>{0..\<tau>'}. (\<theta> (x \<tau>') - \<nu> (x \<tau>')) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>'. \<tau>' *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau>' - 0)" 
    by(rule_tac mvt_very_simple) (auto simp: tHyp)
  then obtain r where "r \<in> {0..\<tau>'}" 
    and "\<theta> (x \<tau>') - \<nu> (x \<tau>') = (\<tau>' - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... \<ge> 0" 
    using tHyp(1) x_ivp(2) primed calculation(1) by auto 
  ultimately show "\<nu> (x \<tau>') \<le> \<theta> (x \<tau>')" 
    by simp
qed

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (D x = (\<lambda>\<tau>'. f (x \<tau>')) on {0..\<tau>}) \<longrightarrow> (\<forall>\<tau>'\<in>{0..\<tau>}. \<theta>' (x \<tau>') \<ge> \<nu>' (x \<tau>') \<and> 
  (D (\<lambda>\<tau>'. \<theta> (x \<tau>') - \<nu> (x \<tau>')) = (\<lambda>r. \<theta>' (x r) - \<nu>' (x r)) on {0..\<tau>'}))"
  shows "(\<lambda>s. \<nu> s < \<theta> s) is_diff_invariant_of f along {0..\<tau>}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau>' assume tHyp:"0 \<le> \<tau>'" "\<tau>' \<le> \<tau>"
    and x_ivp:"D x = (\<lambda>\<tau>'. f (x \<tau>')) on {0..\<tau>}" "\<nu> (x 0) < \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0..\<tau>'}. ((\<lambda>\<tau>'. \<theta> (x \<tau>') - \<nu> (x \<tau>')) has_derivative 
(\<lambda>\<tau>'. \<tau>' *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {0..\<tau>'}) \<and> \<theta>' (x r) \<ge> \<nu>' (x r)" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>r\<in>{0..\<tau>'}. (\<theta> (x \<tau>') - \<nu> (x \<tau>')) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>'. \<tau>' *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau>' - 0)" 
    by(rule_tac mvt_very_simple) (auto simp: tHyp)
  then obtain r where "r \<in> {0..\<tau>'}" and 
    "\<theta> (x \<tau>') - \<nu> (x \<tau>') = (\<tau>' - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... > 0" 
    using tHyp(1) x_ivp(2) primed by (metis (no_types,hide_lams) Groups.add_ac(2) add_sign_intros(1) 
        calculation(1) diff_gt_0_iff_gt ge_iff_diff_ge_0 less_eq_real_def zero_le_scaleR_iff) 
  ultimately show "\<nu> (x \<tau>') < \<theta> (x \<tau>')" 
    by simp
qed

lemma [diff_invariant_rules]:
  assumes "I\<^sub>1 is_diff_invariant_of f along {0..\<tau>}"
      and "I\<^sub>2 is_diff_invariant_of f along {0..\<tau>}"
    shows "(\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) is_diff_invariant_of f along {0..\<tau>}"
  using assms unfolding diff_invariant_def by auto

lemma [diff_invariant_rules]:
  assumes "I\<^sub>1 is_diff_invariant_of f along {0..\<tau>}" 
      and "I\<^sub>2 is_diff_invariant_of f along {0..\<tau>}"
  shows "(\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) is_diff_invariant_of f along {0..\<tau>}"
  using assms unfolding diff_invariant_def by auto

end