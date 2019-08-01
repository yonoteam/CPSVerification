theory cat2funcset
  imports "../hs_prelims_dyn_sys" "Transformer_Semantics.Kleisli_Quantale"
                        
begin

chapter \<open>Hybrid System Verification\<close>

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
type_synonym 'a pred = "'a \<Rightarrow> bool"
no_notation bres (infixr "\<rightarrow>" 60)

section \<open>Verification of regular programs\<close>

text \<open>First we add lemmas for computation of weakest liberal preconditions (wlps).\<close>

lemma "fb\<^sub>\<F> F S = {s. F s \<subseteq> S}"
  unfolding ffb_def map_dual_def klift_def kop_def dual_set_def
  by(auto simp: Compl_eq_Diff_UNIV fun_eq_iff f2r_def converse_def r2f_def)

lemma ffb_eta[simp]: "fb\<^sub>\<F> \<eta> X = X"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

lemma ffb_eq: "fb\<^sub>\<F> F X = {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> X}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

lemma ffb_mono_ge:
  assumes "P \<le> fb\<^sub>\<F> F R" and "R \<le> Q"
  shows "P \<le> fb\<^sub>\<F> F Q"
  using assms unfolding ffb_eq by auto

lemma ffb_eq_univD: "fb\<^sub>\<F> F P = UNIV \<Longrightarrow> (\<forall>y. y \<in> (F x) \<longrightarrow> y \<in> P)"
proof
  fix y assume "fb\<^sub>\<F> F P = UNIV"
  hence "UNIV = {s. \<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P}" 
    by(subst ffb_eq[symmetric], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P)}" 
    by auto
  then show "s2p (F x) y \<longrightarrow> y \<in> P" 
    by auto
qed

text \<open>Next, we introduce assignments and their wlps.\<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd x i a \<equiv> \<chi> j. ((($) x)(i := a)) j"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) \<Rightarrow> ('a^'b) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> (\<lambda>s. {vec_upd s x (e s)})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> (x ::= e) Q = {s. (vec_upd s x (e s)) \<in> Q}"
  by(subst ffb_eq) simp

text \<open>The wlp of a (kleisli) composition is just the composition of the wlps.\<close>

lemma ffb_kcomp: "fb\<^sub>\<F> (G \<circ>\<^sub>K F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by(auto simp: kcomp_def)

lemma ffb_kcomp_ge:
  assumes "P \<le> fb\<^sub>\<F> F R" "R \<le> fb\<^sub>\<F> G Q"
  shows "P \<le> fb\<^sub>\<F> (F \<circ>\<^sub>K G) Q"
  by(subst ffb_kcomp) (rule ffb_mono_ge[OF assms])

text \<open>We also have an implementation of the conditional operator and its wlp.\<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where 
  "IF P THEN X ELSE Y FI \<equiv> (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else:
  "fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q = {s. T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q} \<inter> {s. \<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q}"
  unfolding ffb_eq ifthenelse_def by auto

lemma ffb_if_then_else_ge:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
  using assms apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

lemma ffb_if_then_elseI:
  assumes "T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q"
    and "\<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q"
  shows "s \<in> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
  using assms apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

text \<open>The final wlp we add is that of the finite iteration.\<close>

lemma kstar_inv: "I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  by(auto simp: kcomp_prop) 

lemma ffb_star_induct_self: "I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (kstar F) I"
  apply(subst ffb_eq, subst (asm) ffb_eq)
  unfolding kstar_def apply clarsimp
  using kstar_inv by blast

lemma ffb_kstarI:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using assms(2) ffb_star_induct_self by blast
  hence "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  thus ?thesis
    using assms(3) ffb_mono_ge by blast
qed


section \<open>Verification of hybrid programs\<close>

notation g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) s \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0) s"

subsection \<open>Verification by providing solutions\<close>

lemma ffb_g_orbital: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = 
  {s. \<forall>x\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (G \<rhd> x (down T t)) \<longrightarrow> (x t) \<in> Q}"
  unfolding g_orbital_eq ffb_eq ivp_sols_def by auto

lemma ffb_guard_eq: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. R s} = fb\<^sub>\<F> (g_orbital f G T S t\<^sub>0) {s. Q s}"
  unfolding ffb_g_orbital using assms by auto

context local_flow
begin

lemma ffb_orbit: 
  assumes "S = UNIV"
  shows "fb\<^sub>\<F> \<gamma>\<^sup>\<phi> Q = {s. \<forall> t \<in> T. \<phi> t s \<in> Q}"
  using orbit_eq unfolding assms ffb_eq by auto

lemma ffb_g_orbit: 
  assumes "S = UNIV"
  shows "fb\<^sub>\<F> (\<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G) Q = {s. \<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) (down T t)) \<longrightarrow> (\<phi> t s) \<in> Q}"
  using g_orbit_eq unfolding assms ffb_eq by auto

lemma invariant_set_eq_dl_invariant:
  assumes "S = UNIV"
  shows "(\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s)) = ({s. I s} = fb\<^sub>\<F> (orbit) {s. I s})"
  apply(safe, simp_all add: ffb_orbit[OF assms])
    apply(erule_tac x=x in ballE, simp_all add: assms)
  apply(erule_tac x=0 in ballE, erule_tac x=x in allE)
  by(auto simp: ivp(2) init_time assms)

end

text\<open> The previous lemma allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immediately after.\<close>

lemma dSolution:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t\<in>T. (G \<rhd> (\<lambda>\<tau>. \<phi> \<tau> s) (down T t)) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T UNIV @ 0) Q"
  using assms by(subst local_flow.ffb_g_orbit) auto

lemma line_is_local_flow: 
  "0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow> open T \<Longrightarrow> local_flow (\<lambda> s. c) T UNIV (\<lambda> t s. s + t *\<^sub>R c)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def, clarsimp)
   apply(rule_tac x=1 in exI, clarsimp, rule_tac x="1/2" in exI, simp)
  apply(rule_tac f'1="\<lambda> s. 0" and g'1="\<lambda> s. c" in derivative_intros(191))
  apply(rule derivative_intros, simp)+
  by simp_all

lemma ffb_line: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) Q = 
  {x. \<forall>t\<in>T. (G \<rhd> (\<lambda>\<tau>. x + \<tau> *\<^sub>R c) (down T t)) \<longrightarrow> (x + t *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. c" _ _ "(\<lambda>t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in our verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>

lemma DW: "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. G s \<longrightarrow> s \<in> Q}"
  by(auto intro: g_orbitalD simp: ffb_eq)
  
lemma dWeakening: 
  assumes "{s. G s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
  using assms by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq ffb_eq)

subsubsection\<open> Differential Cut \<close>

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

lemma DC:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
    then obtain \<tau>::real and x where x_ivp: "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
      "x \<in> T \<rightarrow> S" and guard_x:"G \<rhd> x (down T \<tau>)" and "s' = x \<tau>" "\<tau> \<in> T"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by clarsimp metis
    hence "\<forall>t\<in>(down T \<tau>).\<forall>\<tau>\<in>(down T t). G (x \<tau>)"
      by (simp add: closed_segment_eq_real_ivl)
    also have "\<forall>\<tau>\<in>(down T \<tau>). \<tau> \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). x t \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp] by meson
    hence "C \<rhd> x (down T \<tau>)" 
      using assms by (meson ffb_eq_univD mem_Collect_eq)
    hence "s' \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>s' = x \<tau>\<close> by fastforce}
  thus "(x\<acute>=f & G on T S @ t\<^sub>0) s \<subseteq> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s"
    by blast
next show "\<And>s. (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) s \<subseteq> (x\<acute>=f & G on T S @ t\<^sub>0) s" 
    by (auto simp: g_orbital_eq)
qed

lemma dCut:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and ffb_C: "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. C s}"
    and ffb_Q: "P \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
proof(subst ffb_eq, subst g_orbital_eq, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "(x t\<^sub>0) \<in> P" and "\<tau> \<in> T"
    and x_solves:"D x = (\<lambda>t. f (x t)) on T" "x \<in> T \<rightarrow> S" 
    and guard_x:"\<forall>t. s2p T t \<and> t \<le> \<tau> \<longrightarrow> G (x t)"
  hence "\<forall>r\<in>(down T \<tau>). x r \<in> (x\<acute>=f & G on T S @ t\<^sub>0) (x t\<^sub>0)"
    by (auto intro!: g_orbitalI x_solves)
  hence "\<forall>t\<in>(down T \<tau>). C (x t)" 
    using ffb_C \<open>(x t\<^sub>0) \<in> P\<close> by (subst (asm) ffb_eq, auto)
  hence "x \<tau> \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) (x t\<^sub>0)"
    using guard_x \<open>\<tau> \<in> T\<close> by (auto intro!: g_orbitalI x_solves)
  thus "(x \<tau>) \<in> Q"
    using \<open>(x t\<^sub>0) \<in> P\<close> ffb_Q by (subst (asm) ffb_eq) auto
qed

subsubsection\<open> Differential Invariant \<close>

lemma DI_sufficiency:
  assumes "\<forall>s. \<exists>x. x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and "t\<^sub>0 \<in> T" and "\<forall>s. \<forall>x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>\<tau>. s2p T \<tau> \<and> \<tau> \<le> t\<^sub>0 \<longrightarrow> G (x \<tau>)"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q \<le> fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q"
  unfolding ffb_g_orbital using assms(1) unfolding ffb_eq apply clarsimp
  apply(rename_tac s, erule_tac x="s" in allE, clarsimp)
  apply(erule_tac x="x" in ballE, erule_tac x="t\<^sub>0" in ballE, erule impE)
  using assms(3) by (simp_all add: \<open>t\<^sub>0 \<in> T\<close> ivp_solsD(2))

lemma (in local_flow) DI_necessity: (* Not true... check Bohrer formalisation *)
  assumes "S = UNIV" "T = UNIV"
  shows "fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ 0) Q"
  apply(subst ffb_g_orbit, simp add: assms, subst ffb_eq, clarsimp)
  oops

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T S from t\<^sub>0" and "I\<^sub>S = {s\<in>S. I s}"
  shows "I\<^sub>S \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) I\<^sub>S"
  using assms by(auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma dInvariant_converse:
  assumes "{s\<in>S. I s} \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. True) on T S @ t\<^sub>0) {s\<in>S. I s}"
  shows "I is_diff_invariant_of f along T S from t\<^sub>0"
  using assms unfolding invariant_to_set ffb_eq by auto

lemma ffb_g_orbital_le_requires:
  assumes "\<forall>s. \<exists>x. x \<in> (x\<acute>=f & G on T S @ t\<^sub>0) s" "\<forall>t\<in>T. t\<^sub>0 \<le> t" "t\<^sub>0\<in>T"
  shows "fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) {s. I s} \<le> {s. I s}"
  using assms unfolding ffb_eq apply clarsimp
  apply(erule_tac x=x in allE, erule exE)
  apply(drule g_orbitalE, clarsimp)
  apply(frule ivp_solsD(2))
  apply(erule_tac x="xb t\<^sub>0" in allE)
  by(auto intro!: g_orbitalI dest: ivp_solsD)

lemma dI:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "P \<le> I" and "I \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G on T S @ t\<^sub>0) Q"
  apply(rule_tac C="\<lambda>s. s \<in> I" in dCut[OF Thyp])
  using assms apply force
  apply(rule dWeakening)
  using assms by auto

end