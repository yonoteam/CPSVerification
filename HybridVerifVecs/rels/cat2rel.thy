theory cat2rel
  imports
  "../hs_prelims_matrices"
  "../../afpModified/VC_KAD"

begin

chapter\<open> Hybrid System Verification with relations \<close>

\<comment> \<open>We start by deleting some conflicting notation.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Relation.Domain ("r2s")

section\<open> Verification of regular programs \<close>

text\<open> Below we explore the behavior of the forward box operator from the antidomain kleene algebra
with the lifting ($\lceil-\rceil$*) operator from predicates to relations @{thm p2r_def[no_vars]} 
and its dropping counterpart @{thm r2p_def[no_vars]}. \<close>

lemma p2r_IdD:"\<lceil>P\<rceil> = Id \<Longrightarrow> P s"
  by (metis (full_types) UNIV_I impl_prop p2r_subid top_empty_eq)

lemma wp_rel:"wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
  have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
    by (simp add: wp_trafo pointfree_idE)
  thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
    by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

corollary wp_relD:"(x,x) \<in> wp R \<lceil>P\<rceil> \<Longrightarrow> \<forall> y. (x,y) \<in> R \<longrightarrow> P y"
proof-
  assume "(x,x) \<in> wp R \<lceil>P\<rceil>"
  hence "(x,x) \<in> \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" using wp_rel by auto
  thus "\<forall> y. (x,y) \<in> R \<longrightarrow> P y" by (simp add: p2r_def)
qed

lemma p2r_r2p_wp_sym:"wp R P = \<lceil>\<lfloor>wp R P\<rfloor>\<rceil>"
  using d_p2r wp_simp by blast

lemma p2r_r2p_wp:"\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  by(rule sym, subst p2r_r2p_wp_sym, simp)

text\<open> Next, we introduce assignments and compute their @{text "wp"}. \<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) where 
"x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2[_ ::== _])" [70, 65] 61) where 
"[x ::== expr]\<equiv> {(s, s[x :== expr s])| s. True}" 

lemma wp_assign [simp]: "wp ([x ::== expr]) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s[x :== expr s])\<rceil>"
  by(auto simp: rel_antidomain_kleene_algebra.fbox_def rel_ad_def p2r_def)

lemma wp_assign_var [simp]: "\<lfloor>wp ([x ::== expr]) \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. Q (s[x :== expr s]))"
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
from \<open>d i \<le> |x] i\<close> have "d i \<le> |x] (d i)"
  using local.fbox_simp by auto 
hence "|1] p \<le> |x\<^sup>\<star>] i" using \<open>d p \<le> d i\<close> by (metis (no_types) 
  local.dual_order.trans local.fbox_one local.fbox_simp local.fbox_star_induct_var)
thus ?thesis using \<open>d i \<le> d q\<close> by (metis (full_types)
  local.fbox_mult local.fbox_one local.fbox_seq_var local.fbox_simp)
qed

lemma rel_ad_mka_starI:
assumes "P \<subseteq> I" and "I \<subseteq> wp R I" and "I \<subseteq> Q"
shows "P \<subseteq> wp (R\<^sup>*) Q"
proof-
  have "wp R I \<subseteq> Id"
    by (simp add: rel_antidomain_kleene_algebra.a_subid rel_antidomain_kleene_algebra.fbox_def)
  hence "P \<subseteq> Id" using assms(1,2) by blast
  from this have "rdom P = P" by (metis d_p2r p2r_surj)
  also have "rdom P \<subseteq> wp (R\<^sup>*) Q"
    by (metis \<open>wp R I \<subseteq> Id\<close> assms d_p2r p2r_surj 
        rel_antidomain_kleene_algebra.dka.dom_iso rel_antidomain_kleene_algebra.fbox_starI)
  ultimately show ?thesis by blast
qed


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

lemma "(t::real) \<in> {0--t}"
  by (rule ends_in_segment(2))

lemma "(t::real) \<in> {0..t}"
  apply auto
  oops

definition "g_orbital f T t\<^sub>0 G s = \<Union> {{x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0--t} }|x. x \<in> ivp_sols f T t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f T t\<^sub>0 G s = 
  {x t |t x. t \<in> T \<and> (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> t\<^sub>0 \<in> T \<and> G \<rhd> x {t\<^sub>0--t}}"
  unfolding g_orbital_def ivp_sols_def by auto

lemma "g_orbital f T t\<^sub>0 G s = (\<Union> x \<in> ivp_sols f T t\<^sub>0 s. {x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0--t}})"
  unfolding g_orbital_def ivp_sols_def by auto

lemma g_orbitalI:
  assumes "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
    and "t\<^sub>0 \<in> T" "t \<in> T" and "G \<rhd> x {t\<^sub>0--t}"
  shows "x t \<in> g_orbital f T t\<^sub>0 G s"
  using assms unfolding g_orbital_def ivp_sols_def by blast

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f T t\<^sub>0 G s"
  obtains x and t where "x \<in> ivp_sols f T t\<^sub>0 s" 
  and "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
  and "x t = s'" and "t\<^sub>0 \<in> T" "t \<in> T" and "G \<rhd> x {t\<^sub>0--t}"
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
  shows "g_orbital f T 0 G s = {\<phi> t s | t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0--t}}" (is "_ = ?gorbit")
proof(rule subset_antisym, simp_all only: subset_eq)
  {fix s' assume "s' \<in> g_orbital f T 0 G s"
    then obtain x and t where x_ivp:"D x = (f \<circ> x) on T" 
      "x 0 = s" and "x t = s'" and "t \<in> T" and guard:"G \<rhd> x {0--t}"
      unfolding g_orbital_eq by blast
    hence obs:"\<forall>\<tau>\<in>{0--t}. x \<tau> = \<phi> \<tau> s"
      using usolves_ivp[of x s] closed_segment_subset_domainI init_time comp_def
      by (metis (mono_tags, lifting) has_vderiv_eq)
    hence "G \<rhd> (\<lambda>r. \<phi> r s) {0--t}"
      using guard by simp
    hence "s' \<in> ?gorbit"
      using \<open>x t = s'\<close> \<open>t \<in> T\<close> obs by blast}
  thus "\<forall>s'\<in>g_orbital f T 0 G s. s' \<in> ?gorbit"
    by blast
next
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) {0--t}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> g_orbital f T 0 G s"
      by(auto intro: g_orbitalI simp: ivp init_time)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> g_orbital f T 0 G s"
    by blast
qed

lemma g_evol_collapses:
  shows "([x\<acute>=f]T & G) = {(s, \<phi> t s) | t s. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0--t}}"
  unfolding g_orbital_collapses by auto

lemma wp_orbit: "wp ({(s,s') | s s'. s' \<in> orbit s}) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
  unfolding orbit_eq wp_rel by auto

lemma wp_g_orbit: "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) {0--t}) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding g_evol_collapses wp_rel by auto

end

lemma (in global_flow) ivp_sols_collapse[simp]: "ivp_sols f UNIV 0 s = {(\<lambda>t. \<phi> t s)}"
  by(auto intro: usolves_ivp simp: ivp_sols_def ivp)

text\<open> The previous theorem allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f T L \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  using assms apply(subst local_flow.wp_g_orbit, auto)
  by (simp add: Starlike.closed_segment_eq_real_ivl)

lemma line_DS: "0 \<le> t \<Longrightarrow> wp ([x\<acute>=\<lambda>s. c]{0..t} & G) \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (G \<rhd> (\<lambda>r. x + r *\<^sub>R c) {0..\<tau>}) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_orbit[of "\<lambda>s. c" _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  by(auto simp: line_is_local_flow closed_segment_eq_real_ivl)
  

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>

lemma DW: "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = wp ([x\<acute>=f]T & G) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  apply(subst wp_rel)+
  by(auto simp: g_orbital_eq)

lemma dWeakening: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  using assms apply(subst wp_rel)
  by(auto simp: g_orbital_eq)

subsubsection\<open> Differential Cut \<close>

lemma wp_g_orbit_IdD:
  assumes "wp ([x\<acute>=f]T & G) \<lceil>C\<rceil> = Id" and "\<forall> r\<in>{0--t}. (s, x r) \<in> ([x\<acute>=f]T & G)"
  shows "\<forall>r\<in>{0--t}. C (x r)"
proof
  fix r assume "r \<in> {0--t}"
  then have "x r \<in> g_orbital f T 0 G s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f T 0 G s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_rel by(auto simp: p2r_def)
  ultimately show "C (x r)" by blast
qed

theorem DC:
  assumes "interval T" and "wp ([x\<acute>=f]T & G) \<lceil>C\<rceil> = Id"
  shows "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = wp ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule subset_antisym, safe)
  {fix s and s' assume "s' \<in> g_orbital f T 0 G s"
    then obtain t::real and x where x_ivp: "D x = (f \<circ> x) on T" "x 0 = s"
      and guard_x:"G \<rhd> x {0--t}" and "s' = x t" and "0 \<in> T" "t \<in> T"
      using g_orbitalD[of s' "f" T 0 G s] by (metis (full_types))
    from guard_x have "\<forall>r\<in>{0--t}.\<forall> \<tau>\<in>{0--r}. G (x \<tau>)"
      by (metis contra_subsetD ends_in_segment(1) subset_segment(1))
    also have "\<forall>\<tau>\<in>{0--t}. \<tau> \<in> T"
      using interval.closed_segment_subset_domain[OF assms(1) \<open>0 \<in> T\<close> \<open>t \<in> T\<close>] by blast
    ultimately have "\<forall>\<tau>\<in>{0--t}. x \<tau> \<in> g_orbital f T 0 G s"
      using g_orbitalI[OF x_ivp \<open>0 \<in> T\<close>] by blast
    hence "\<forall>\<tau>\<in>{0--t}. (s, x \<tau>) \<in> [x\<acute>=f]T & G"
      unfolding wp_rel by(auto simp: p2r_def)
    hence "C \<rhd> x {0--t}" 
      using wp_g_orbit_IdD[OF assms(2)] by blast
    hence "s' \<in> g_orbital f T 0 (\<lambda>s. G s \<and> C s) s"
      using g_orbitalI[OF x_ivp \<open>0 \<in> T\<close> \<open>t \<in> T\<close>] guard_x \<open>s' = x t\<close> by fastforce}
  thus "\<And>s s'. s' \<in> g_orbital f T 0 G s \<Longrightarrow> s' \<in> g_orbital f T 0 (\<lambda>s. G s \<and> C s) s"
    by blast
next show "\<And>s s'. s' \<in> g_orbital f T 0 (\<lambda>s. G s \<and> C s) s \<Longrightarrow> s' \<in> g_orbital f T 0 G s" 
    by (auto simp: g_evol_def)
qed

theorem dCut:
  assumes wp_C:"\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & G) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<subseteq> wp ([x\<acute>=f]{0..t} & (\<lambda> s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<subseteq> wp ([x\<acute>=f]{0..t} & G) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "P (x 0)" and "0 \<le> \<tau>" and "\<tau> \<le> t"
    and x_solves:"D x = (\<lambda>t. f (x t)) on {0..t}" and guard_x:"(\<forall> r \<in> {0--\<tau>}. G (x r))"
  hence "\<forall>r\<in>{0--\<tau>}.\<forall>\<tau>\<in>{0--r}. G (x \<tau>)"
    using closed_segment_closed_segment_subset by blast
  hence "\<forall>r\<in>{0--\<tau>}. x r \<in> g_orbital f {0..t} 0 G (x 0)"
    using g_orbitalI x_solves \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce 
  hence "\<forall>r\<in>{0--\<tau>}. C (x r)" 
    using wp_C \<open>P (x 0)\<close> by(subst (asm) wp_rel, auto)
  hence "x \<tau> \<in> g_orbital f {0..t} 0 (\<lambda>s. G s \<and> C s) (x 0)"
    using g_orbitalI x_solves guard_x \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> by fastforce
  from this \<open>P (x 0)\<close> and wp_Q show "Q (x \<tau>)"
    by(subst (asm) wp_rel, auto simp: closed_segment_eq_real_ivl)
qed

subsubsection\<open> Differential Invariant \<close>

lemma DI_sufficiency:
  assumes "\<forall>s. \<exists>x. x \<in> ivp_sols f T 0 s"
  shows "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> \<le> wp \<lceil>G\<rceil> \<lceil>Q\<rceil>"
  apply(subst wp_rel, subst wp_rel, simp add: p2r_def, clarsimp)
  using assms apply(simp add: g_evol_def ivp_sols_def)
  apply(erule_tac x="s" in allE)+
  apply(erule exE, erule impE)
  by(rule_tac x="0" in exI, rule_tac x=x in exI, auto)

lemma (in local_flow) DI_necessity: (* Not true... check Bohrer formalisation *)
  shows "wp \<lceil>G\<rceil> \<lceil>Q\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  unfolding wp_g_orbit apply(subst wp_rel, simp add: p2r_def, clarsimp)
   apply(erule_tac x="0" in ballE)
    apply(simp_all add: ivp)
  oops

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
  shows "\<lceil>I\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>I\<rceil>"
  using assms unfolding diff_invariant_def 
  by(auto simp: wp_rel g_evol_def ivp_sols_def)

lemma dI:
  assumes "I is_diff_invariant_of f along {0..t}"
    and "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & G) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac C="I" in dCut)
   apply(drule_tac G="G" in dInvariant)
  using assms(2) dual_order.trans apply blast
  apply(rule dWeakening)
  using assms by auto

text\<open> Finally, we obtain some conditions to prove specific instances of differential invariants. \<close>

named_theorems ode_invariant_rules "compilation of rules for differential invariants."

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> (\<forall> \<tau> \<in> {0..t}. \<forall> r \<in> {0--\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>) ) has_derivative (\<lambda>\<tau>.  \<tau> *\<^sub>R 0)) (at r within {0--\<tau>}))"
shows "(\<lambda>s. \<theta> s = \<nu> s) is_diff_invariant_of f along {0..t}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<theta> (x 0) = \<nu> (x 0)" 
  hence "\<forall> r \<in> {0--\<tau>}. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R 0) at r within {0--\<tau>}" 
    using assms by auto
  hence "\<exists>r\<in>{0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x 0) - \<nu> (x 0)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) (\<tau> - 0)" 
    by(rule_tac closed_segment_mvt, auto simp: tHyp) 
  thus "\<theta> (x \<tau>) = \<nu> (x \<tau>)" by (simp add: x_ivp(2))
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> (\<forall> \<tau> \<in> {0..t}. \<forall> r \<in> {0--\<tau>}. \<theta>' (x r) \<ge> \<nu>' (x r)
\<and> (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) - \<nu>' (x r))) at r within {0--\<tau>}))"
shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_diff_invariant_of f along {0..t}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<nu> (x 0) \<le> \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0--\<tau>}. (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) - \<nu>' (x r))) 
  at r within {0--\<tau>}) \<and> \<nu>' (x r) \<le> \<theta>' (x r)" 
    using assms by auto
  hence "\<exists>r\<in>{0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - 0)" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>0 \<le> \<tau>\<close>)
  then obtain r where "r \<in> {0--\<tau>}" 
    and "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... \<ge> 0" 
    using tHyp(1) x_ivp(2) primed by (simp add: calculation(1))  
  ultimately show "\<nu> (x \<tau>) \<le> \<theta> (x \<tau>)" 
    by simp
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> (\<forall> \<tau> \<in> {0..t}. \<forall> r \<in> {0--\<tau>}. \<theta>' (x r) \<ge> \<nu>' (x r)
\<and> (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) - \<nu>' (x r))) at r within {0--\<tau>}))"
shows "(\<lambda>s. \<nu> s < \<theta> s) is_diff_invariant_of f along {0..t}"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t"
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<nu> (x 0) < \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0--\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative 
(\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {0--\<tau>}) \<and> \<theta>' (x r) \<ge> \<nu>' (x r)" 
    using assms by auto
  hence "\<exists>r\<in>{0--\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - 0)" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>0 \<le> \<tau>\<close>)
  then obtain r where "r \<in> {0--\<tau>}" and 
    "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... > 0" 
    using tHyp(1) x_ivp(2) primed by (metis (no_types,hide_lams) Groups.add_ac(2) add_sign_intros(1) 
        calculation(1) diff_gt_0_iff_gt ge_iff_diff_ge_0 less_eq_real_def zero_le_scaleR_iff) 
  ultimately show "\<nu> (x \<tau>) < \<theta> (x \<tau>)" 
    by simp
qed

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "I1 is_diff_invariant_of f along {0..t}" 
    and "I2 is_diff_invariant_of f along {0..t}"
shows "(\<lambda>s. I1 s \<and> I2 s) is_diff_invariant_of f along {0..t}"
  using assms unfolding diff_invariant_def by auto

lemma [ode_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "I1 is_diff_invariant_of f along {0..t}" 
    and "I2 is_diff_invariant_of f along {0..t}"
shows "(\<lambda>s. I1 s \<or> I2 s) is_diff_invariant_of f along {0..t}"
  using assms unfolding diff_invariant_def by auto

end