theory cat2funcset
  imports "../hs_prelims_dyn_sys" "Transformer_Semantics.Kleisli_Quantale"
                        
begin


chapter \<open>Hybrid System Verification\<close>

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation bres (infixr "\<rightarrow>" 60)

no_notation dagger ("_\<^sup>\<dagger>" [101] 100)

no_notation "Relation.relcomp" (infixl ";" 75) 

no_notation kcomp (infixl "\<circ>\<^sub>K" 75)

notation kcomp (infixl ";" 75)

notation kstar ("loop")

section \<open>Verification of regular programs\<close>

text \<open>First we add lemmas for computation of weakest liberal preconditions (wlps).\<close>

lemma "fb\<^sub>\<F> F S = {s. F s \<subseteq> S}"
  unfolding ffb_def map_dual_def klift_def kop_def dual_set_def
  by(auto simp: Compl_eq_Diff_UNIV fun_eq_iff f2r_def converse_def r2f_def)

lemma ffb_eq: "fb\<^sub>\<F> F S = {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> S}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

lemma ffb_eta[simp]: "fb\<^sub>\<F> \<eta> S = S"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

lemma ffb_iso: "P \<le> Q \<Longrightarrow> fb\<^sub>\<F> F P \<le> fb\<^sub>\<F> F Q"
  unfolding ffb_eq by auto

lemma ffb_eq_univD: "fb\<^sub>\<F> F P = UNIV \<Longrightarrow> (\<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P)"
proof
  fix y assume "fb\<^sub>\<F> F P = UNIV"
  hence "UNIV = {s. \<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P}" 
    by(subst ffb_eq[symmetric], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P)}" 
    by auto
  then show "s2p (F s) y \<longrightarrow> y \<in> P" 
    by auto
qed

lemma ffb_invariants: 
  assumes "{s. I s} \<le> fb\<^sub>\<F> F {s. I s}" and "{s. J s} \<le> fb\<^sub>\<F> F {s. J s}"
  shows "{s. I s \<and> J s} \<le> fb\<^sub>\<F> F {s. I s \<and> J s}"
    and "{s. I s \<or> J s} \<le> fb\<^sub>\<F> F {s. I s \<or> J s}"
  using assms unfolding ffb_eq by auto

text \<open>Next, we introduce assignments and their wlps.\<close>

definition vec_upd :: "('a^'n) \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'a^'n"
  where "vec_upd s i a \<equiv> \<chi> j. ((($) s)(i := a)) j"

definition assign :: "'n \<Rightarrow> ('a^'n \<Rightarrow> 'a) \<Rightarrow> ('a^'n) \<Rightarrow> ('a^'n) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> (\<lambda>s. {vec_upd s x (e s)})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> (x ::= e) Q = {s. (\<chi> j. ((($) s)(x := (e s))) j) \<in> Q}"
  unfolding vec_upd_def assign_def by (subst ffb_eq) simp

text \<open>The wlp of a (kleisli) composition is just the composition of the wlps.\<close>

lemma ffb_kcomp: "fb\<^sub>\<F> (G ; F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by(auto simp: kcomp_def)

lemma ffb_kcomp_ge:
  assumes "P \<le> fb\<^sub>\<F> F R" "R \<le> fb\<^sub>\<F> G Q"
  shows "P \<le> fb\<^sub>\<F> (F ; G) Q"
  apply(subst ffb_kcomp) 
  by (rule order.trans[OF assms(1)]) (rule ffb_iso[OF assms(2)])

text \<open>We also have an implementation of the conditional operator and its wlp.\<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where 
  "IF P THEN X ELSE Y \<equiv> (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else:
  "fb\<^sub>\<F> (IF T THEN X ELSE Y) Q = {s. T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q} \<inter> {s. \<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q}"
  unfolding ffb_eq ifthenelse_def by auto

lemma ffb_if_then_else_ge:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y) Q"
  using assms apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

lemma ffb_if_then_elseI:
  assumes "T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q"
    and "\<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q"
  shows "s \<in> fb\<^sub>\<F> (IF T THEN X ELSE Y) Q"
  using assms apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

text \<open>The final wlp we add is that of the finite iteration.\<close>

lemma kstar_inv: "I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  by(auto simp: kcomp_prop) 

lemma ffb_star_induct_self: "I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (loop F) I"
  unfolding kstar_def ffb_eq apply clarsimp
  using kstar_inv by blast

lemma ffb_kstarI:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (loop F) Q"
proof-
  have "I \<subseteq> fb\<^sub>\<F> (loop F) I"
    using assms(2) ffb_star_induct_self by blast
  hence "P \<le> fb\<^sub>\<F> (loop F) I"
    using assms(1) by auto
  also have "fb\<^sub>\<F> (loop F) I \<le> fb\<^sub>\<F> (loop F) Q"
    by (rule ffb_iso[OF assms(3)])
  finally show ?thesis .
qed


section \<open>Verification of hybrid programs\<close>

notation g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) s \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0) s"


subsection \<open>Verification by providing solutions\<close>

lemma ffb_g_orbital_eq: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = 
  {s. \<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<P> X (down T t) \<subseteq> {s. G s}) \<longrightarrow> \<P> X (down T t) \<subseteq> Q}"
  unfolding ffb_eq g_orbital_eq image_le_pred subset_eq apply(clarsimp, safe)
   apply(erule_tac x="X xa" in allE, erule impE, force, simp)
  by (erule_tac x=X in ballE, simp_all) (* for paper... *)

lemma ffb_g_orbital: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = 
  {s. \<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> (X t) \<in> Q}"
  unfolding ffb_eq g_orbital_eq by auto

context local_flow
begin

lemma ffb_g_orbit: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}" (is "_ = ?wlp")
  unfolding ffb_g_orbital apply(safe, clarsimp)
    apply(erule_tac x="\<lambda>t. \<phi> t x" in ballE)
  using in_ivp_sols apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> x", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma ffb_orbit: "fb\<^sub>\<F> \<gamma>\<^sup>\<phi> Q = {s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. \<phi> t s \<in> Q)}"
  unfolding orbit_def ffb_g_orbit by simp

end


subsection\<open> Verification with differential invariants \<close>

lemma ffb_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. H s} = fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. Q s}"
  unfolding ffb_g_orbital using assms by auto

lemma ffb_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
  using assms(1) apply(rule order.trans)
  using assms(2) apply(rule order.trans)
  by (rule ffb_iso[OF assms(3)])

lemma "diff_invariant I f T S t\<^sub>0 G = (((g_orbital f G T S t\<^sub>0)\<^sup>\<dagger>) {s. I s} \<subseteq> {s. I s})"
  unfolding klift_def diff_invariant_def by simp

lemma bdf_diff_inv: (* for paper... *)
  "diff_invariant I f T S t\<^sub>0 G = (bd\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. I s} \<le> {s. I s})"
  unfolding ffb_fbd_galois_var by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma ffb_diff_inv: 
  "({s. I s} \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. I s}) = diff_invariant I f T S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma diff_inv_guard_ignore: (* for paper... *)
  assumes "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. True) on T S @ t\<^sub>0) {s. I s}"
  shows "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. I s}"
  using assms unfolding ffb_diff_inv diff_invariant_eq image_le_pred by auto

context local_flow (* for paper... *)
begin

lemma ffb_diff_inv_eq: "diff_invariant I f T S 0 (\<lambda>s. True) = 
  ({s. s \<in> S \<longrightarrow> I s} = fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. True) on T S @ 0) {s. s \<in> S \<longrightarrow> I s})"
  unfolding ffb_diff_inv[symmetric] ffb_g_orbital 
  using init_time apply(auto simp: subset_eq ivp_sols_def)
  apply(subst ivp(2)[symmetric], simp)
  apply(erule_tac x="\<lambda>t. \<phi> t x" in allE)
  using in_domain has_vderiv_on_domain ivp(2) init_time by force

lemma diff_inv_eq_inv_set:
  "diff_invariant I f T S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end


subsection\<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL).\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) Q = 
  {s. \<forall>t\<in>T. (\<P> (\<lambda>\<tau>. s + \<tau> *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> (s + t *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. c" _ _ "(\<lambda>t s. s + t *\<^sub>R c)"])
  using line_is_local_flow assms unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T UNIV @ 0) Q"
  using assms by(subst local_flow.ffb_g_orbit) auto

lemma diff_weak_axiom: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. G s \<longrightarrow> s \<in> Q}"
  unfolding ffb_g_orbital image_def by force
  
lemma diff_weak_rule: "{s. G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
  by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq ffb_eq)

lemma ffb_g_orbital_eq_univD:
  assumes "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. C s} = UNIV" 
    and "\<forall>\<tau>\<in>(down T t). x \<tau> \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s \<longrightarrow> C y" 
    using assms(1) ffb_eq_univD by fastforce
  ultimately show "C (x \<tau>)" by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"\<P> X (down T \<tau>) \<subseteq> {s. G s}"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s]  by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using assms by (meson ffb_eq_univD mem_Collect_eq)
    hence "s' \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce}
  thus "(x\<acute>=f & G on T S @ t\<^sub>0) s \<subseteq> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
    by blast
next show "\<And>s. (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s \<subseteq> (x\<acute>=f & G on T S @ t\<^sub>0) s" 
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and ffb_C: "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. C s}"
    and ffb_Q: "P \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
proof(subst ffb_eq, subst g_orbital_eq, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "s \<in> P" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<P> X (down T t) \<subseteq> {s. G s}"
  have "\<forall>r\<in>(down T t). X r \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using ffb_C \<open>s \<in> P\<close> by (subst (asm) ffb_eq, auto)
  hence "X t \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "(X t) \<in> Q"
    using \<open>s \<in> P\<close> ffb_Q by (subst (asm) ffb_eq) auto
qed

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G) Q"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) unfolding image_le_pred by simp

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G) Q = {x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> (x + t *\<^sub>R c) \<in> Q}"
  by (subst diff_solve_axiom[of UNIV]) auto

lemma DW: "fb\<^sub>\<F> (x\<acute>=f & G) Q = fb\<^sub>\<F> (x\<acute>=f & G) {s. G s \<longrightarrow> s \<in> Q}"
  by (rule diff_weak_axiom)
  
lemma dW: "{s. G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>=f & G) Q"
  by (rule diff_weak_rule)

lemma DC:
  assumes "fb\<^sub>\<F> (x\<acute>=f & G) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>=f & G) Q = fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s)) Q"
  by (rule diff_cut_axiom) (auto simp: assms)

lemma dC:
  assumes "P \<le> fb\<^sub>\<F> (x\<acute>=f & G) {s. C s}"
    and "P \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s)) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G) Q"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "P \<le> {s. I s}" and "diff_invariant I f UNIV UNIV 0 G" and "{s. I s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G) Q"
  apply(rule ffb_g_orbital_inv[OF assms(1) _ assms(3)])
  using ffb_diff_inv[symmetric] assms(2) by force

end