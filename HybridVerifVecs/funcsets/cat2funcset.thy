theory cat2funcset
  imports "../hs_prelims" "Transformer_Semantics.Kleisli_Quantale"
                        
begin

chapter \<open>Hybrid System Verification\<close>

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
type_synonym 'a pred = "'a \<Rightarrow> bool"
no_notation bres (infixr "\<rightarrow>" 60)

section \<open>Verification of regular programs\<close>

text \<open>First we add lemmas for computation of weakest liberal preconditions (wlps).\<close>

lemma ffb_eta[simp]: "fb\<^sub>\<F> \<eta> X = X"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

lemma ffb_eq: "fb\<^sub>\<F> F X = {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> X}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

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

lemma ffb_mono_ge:
  assumes "P \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> F Q"
  using assms unfolding ffb_eq by auto

lemma ffb_kcomp_ge:
  assumes "P \<le> fb\<^sub>\<F> F I" "I \<le> fb\<^sub>\<F> G Q"
  shows "P \<le> fb\<^sub>\<F> (F \<circ>\<^sub>K G) Q"
  by(subst ffb_kcomp) (rule ffb_mono_ge[OF assms])

text \<open>We also have an implementation of the conditional operator and its wlp.\<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where 
  "IF P THEN X ELSE Y FI \<equiv> (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
  using assms apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

lemma ffb_if_then_elseD:
  assumes "T x \<longrightarrow> x \<in> fb\<^sub>\<F> X Q"
    and "\<not> T x \<longrightarrow> x \<in> fb\<^sub>\<F> Y Q"
  shows "x \<in> fb\<^sub>\<F> (IF T THEN X ELSE Y FI) Q"
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

lemma ffb_starI:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using assms(2) ffb_star_induct_self by blast
  hence "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  thus ?thesis
    using assms(3) by(subst ffb_eq, subst (asm) ffb_eq, auto)
qed


section \<open>Verification of hybrid programs\<close>

subsection \<open>Verification by providing solutions\<close>

abbreviation guards :: "('a \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real set) \<Rightarrow> bool" ("_ \<rhd> _ _" [70, 65] 61) 
  where "G \<rhd> x T \<equiv> \<forall> r \<in> T. G (x r)"

definition "g_orbital f T S t\<^sub>0 G s = 
  \<Union> {{x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0--t} }|x. x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f T S t\<^sub>0 G s =
  {x t |t x. t \<in> T \<and> (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> x \<in> T \<rightarrow> S \<and> G \<rhd> x {t\<^sub>0--t}}"
  unfolding g_orbital_def ivp_sols_def by auto

lemma "g_orbital f T S t\<^sub>0 G s = (\<Union> x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. {x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0--t}})"
  unfolding g_orbital_def ivp_sols_def by auto

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _ _ _)") where "x\<acute>=f & G T S \<equiv> (\<lambda> s. g_orbital f T S 0 G s)"

lemmas g_evol_def = g_orbital_eq[where t\<^sub>0 = 0]

lemma g_evolI:
  assumes "D x = (f \<circ> x) on T" "x 0 = s" "x \<in> T \<rightarrow> S"
    and "t \<in> T" and "G \<rhd> x {0--t}"
  shows "x t \<in> (x\<acute>=f & G T S) s"
  using assms unfolding g_evol_def by auto

lemma g_evolD:
  assumes "s' \<in> (x\<acute>=f & G T S) s"
  obtains x and t where "x \<in> ivp_sols (\<lambda>t. f) T UNIV 0 s" 
  and "D x = (f \<circ> x) on T" "x 0 = s" "x \<in> T \<rightarrow> S"
  and "x t = s'" and "t \<in> T" and "G \<rhd> x {0--t}"
  using assms unfolding g_orbital_def ivp_sols_def by auto

lemma ffb_g_evol: 
  "fb\<^sub>\<F> (x\<acute>=f & G T S) Q = {s. \<forall>x \<in> ivp_sols (\<lambda>t. f) T S 0 s. \<forall>t\<in>T. (G \<rhd> x {0--t}) \<longrightarrow> (x t) \<in> Q}"
  unfolding g_evol_def ffb_eq ivp_sols_def by auto

lemma ffb_guard_eq: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) {s. R s} = fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) {s. Q s}"
  unfolding ffb_g_evol using assms by auto

context local_flow
begin

definition "orbit s = g_orbital f T S 0 (\<lambda>s. True) s"

lemma orbit_eq[simp]: 
  assumes "s \<in> S"
  shows "orbit s = {\<phi> t s| t. t \<in> T}"
  unfolding orbit_def apply safe
  using eq_solution assms apply(subst (asm) g_orbital_def, blast)
  unfolding g_orbital_eq by(auto intro!: has_vderiv_on_domain ivp(2) 
      in_domain assms simp: init_time)

lemma g_evol_collapses: 
  assumes "s \<in> S"
  shows "(x\<acute>=f & G T S) s = {\<phi> t s| t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0--t}}" (is "_ = ?gorbit")
proof(rule subset_antisym, simp_all only: subset_eq)
  {fix s' assume "s' \<in> (x\<acute>=f & G T S) s"
    then obtain x and t where x_ivp:"x \<in> ivp_sols (\<lambda>t. f) T S 0 s" 
      and "x t = s'" and "t \<in> T" and guard:"G \<rhd> x {0--t}"
      unfolding g_orbital_def by auto
    hence obs:"\<forall>\<tau>\<in>{0..t}. x \<tau> = \<phi> \<tau> s"
      using eq_solution[OF x_ivp _ assms] init_time
      by (meson atLeastAtMost_iff interval_time mem_is_interval_1_I)
    hence "G \<rhd> (\<lambda>r. \<phi> r s) {0--t}"
      using guard by (metis \<open>s2p T t\<close> assms closed_segment_subset_domainI 
          eq_solution init_time x_ivp) 
    also have "\<phi> t s = x t"
      using eq_solution[OF x_ivp \<open>t \<in> T\<close> assms] by simp
    ultimately have "s' \<in> ?gorbit"
      using \<open>x t = s'\<close> \<open>t \<in> T\<close> by auto}
  thus "\<forall>s'\<in>(x\<acute>=f & G T S) s. s' \<in> ?gorbit"
    by blast
next
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) {0--t}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> (x\<acute>=f & G T S) s"
      using assms by(auto intro!: g_evolI in_domain ivp(2) 
          has_vderiv_on_domain simp: init_time)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> (x\<acute>=f & G T S) s"
    by blast
qed

lemma ffb_orbit: 
  assumes "S = UNIV"
  shows "fb\<^sub>\<F> (orbit) Q = {s. \<forall> t \<in> T. \<phi> t s \<in> Q}"
  using orbit_eq unfolding assms ffb_eq by auto

lemma ffb_g_orbit: 
  assumes "S = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>=f & G T S) Q = {s. \<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) {0--t}) \<longrightarrow> (\<phi> t s) \<in> Q}"
  using g_evol_collapses unfolding assms ffb_eq by auto

lemma ivp_sols_collapse: 
  assumes "S = UNIV" "T = UNIV"
  shows "ivp_sols (\<lambda>t. f) T S 0 s = {(\<lambda>t. \<phi> t s)}"
  using in_ivp_sols eq_solution unfolding assms by auto

end

text\<open> The previous lemma allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t \<in> UNIV. (G \<rhd> (\<lambda>r. \<phi> r s) {0--t}) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G UNIV UNIV) Q"
  using assms by(subst local_flow.ffb_g_orbit) auto

lemma ffb_line: 
  fixes c::"'a::{heine_borel, banach}"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G UNIV UNIV) Q = 
    {x. \<forall> \<tau>. (G \<rhd> (\<lambda>r. x + r *\<^sub>R c) {0--\<tau>}) \<longrightarrow> (x + \<tau> *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda>s. c" _ _ "(\<lambda> t x. x + t *\<^sub>R c)"])
  by(auto simp: line_is_local_flow)

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in our verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>

lemma DW: "fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q = fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) {s. G s \<longrightarrow> s \<in> Q}"
  by(auto intro: g_evolD simp: ffb_eq)
  
lemma dWeakening: 
  assumes "{s. G s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q"
  using assms by(auto intro: g_evolD simp: le_fun_def g_evol_def ffb_eq)

subsubsection\<open> Differential Cut \<close>

lemma ffb_g_orbit_eq_univD:
  assumes "fb\<^sub>\<F> (x\<acute>=f & G T S) {s. C s} = UNIV" 
    and "\<forall> r\<in>{0..t}. x r \<in> (x\<acute>=f & G T S) s"
  shows "\<forall>r\<in>{0..t}. C (x r)"
proof
  fix r assume "r \<in> {0..t}"
  then have "x r \<in> (x\<acute>=f & G T S) s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (x\<acute>=f & G T S) s \<longrightarrow> C y" 
    using assms(1) ffb_eq_univD by fastforce
  ultimately show "C (x r)" by blast
qed

lemma DC:
  assumes "fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q = fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>=f & G {0..t} S) s"
    then obtain \<tau>::real and x where x_ivp: "D x = (f \<circ> x) on {0..t}" "x 0 = s"
      "x \<in> {0..t} \<rightarrow> S" and guard_x:"G \<rhd> x {0--\<tau>}" and "s' = x \<tau>" "\<tau> \<in> {0..t}"
      using g_evolD[of s' "f" "{0..t}" S G s] by metis
    from guard_x have "\<forall>r\<in>{0--\<tau>}.\<forall>\<tau>\<in>{0..r}. G (x \<tau>)"
      by (simp add: closed_segment_eq_real_ivl)
    also have "\<forall>\<tau>\<in>{0--\<tau>}. \<tau> \<in> {0..t}"
      using \<open>\<tau> \<in> {0..t}\<close> by (auto simp: closed_segment_eq_real_ivl)
    ultimately have "\<forall>\<tau>\<in>{0--\<tau>}. x \<tau> \<in> (x\<acute>=f & G {0..t} S) s"
      using g_evolI[OF x_ivp] closed_segment_eq_real_ivl by fastforce
    hence "C \<rhd> x {0--\<tau>}" 
      using ffb_g_orbit_eq_univD assms by (meson ffb_eq_univD mem_Collect_eq)
    hence "s' \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) s"
      using g_evolI[OF x_ivp \<open>\<tau> \<in> {0..t}\<close>] guard_x \<open>s' = x \<tau>\<close> by fastforce}
  thus "(x\<acute>=f & G {0..t} S) s \<subseteq> (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) s"
    by blast
next show "\<And>s. (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) s \<subseteq> (x\<acute>=f & G {0..t} S) s" 
    by (auto simp: g_evol_def)
qed

lemma dCut:
  assumes ffb_C:"P \<le> fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) {s. C s}"
    and ffb_Q:"P \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q"
proof(subst ffb_eq, subst g_evol_def, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "(x 0) \<in> P" and "0 \<le> \<tau>" and "\<tau> \<le> t"
    and x_solves:"D x = (\<lambda>t. f (x t)) on {0..t}" "x \<in> {0..t} \<rightarrow> S" 
    and guard_x:"(\<forall> r \<in> {0--\<tau>}. G (x r))"
  hence "\<forall>r\<in>{0--\<tau>}.\<forall>\<tau>\<in>{0..r}. G (x \<tau>)"
    by (simp add: closed_segment_eq_real_ivl)
  hence "\<forall>r\<in>{0--\<tau>}. x r \<in> (x\<acute>=f & G {0..t} S) (x 0)"
    using g_evolI x_solves \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce
  hence "\<forall>r\<in>{0--\<tau>}. C (x r)" 
    using ffb_C \<open>(x 0) \<in> P\<close> by(subst (asm) ffb_eq, auto)
  hence "x \<tau> \<in> (x\<acute>=f & (\<lambda>s. G s \<and> C s) {0..t} S) (x 0)"
    using g_evolI x_solves guard_x \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> by fastforce
  from this \<open>(x 0) \<in> P\<close> and ffb_Q show "(x \<tau>) \<in> Q"
    by(subst (asm) ffb_eq) auto
qed

subsubsection\<open> Differential Invariant \<close>

lemma DI_sufficiency:
  assumes "0 \<le> t" "\<forall>s. \<exists>x. x \<in> ivp_sols (\<lambda>t. f) {0..t} S 0 s"
  shows "fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q \<le> fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q"
  using assms apply(subst ffb_eq, subst ffb_eq, clarsimp)
  apply(rename_tac s, erule_tac x="s" in allE, erule impE)
  apply(simp add: g_evol_def ivp_sols_def)
  apply(erule_tac x="s" in allE, clarify)
  by(rule_tac x="0" in exI, rule_tac x=x in exI, auto)

lemma (in local_flow) DI_necessity: (* Not true... check Bohrer formalisation *)
  assumes "S = UNIV" "T \<subseteq> {z. z \<ge> 0}"
  shows "fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q \<le> fb\<^sub>\<F> (x\<acute>=f & G T S) Q"
  apply(subst ffb_g_orbit, simp add: assms, subst ffb_eq)
  using assms apply(auto simp: subset_eq)
   apply(erule_tac x=0 and P="\<lambda>t. G (\<phi> t x)" in ballE)
  using ivp(2) apply simp_all
  apply(erule_tac x=t and P="\<lambda>t. G (\<phi> t x)" in ballE)
  oops

definition diff_invariant :: "'a pred \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool" 
("(_)/ is'_diff'_invariant'_of (_)/ along (_ _)" [70,65]61) 
where "I is_diff_invariant_of f along T S \<equiv> 
  (\<forall>s\<in>S. I s \<longrightarrow> (\<forall> x. x \<in> ivp_sols (\<lambda>t. f) T S 0 s \<longrightarrow> (\<forall> t \<in> T. I (x t))))"

lemma invariant_to_set:
  shows "(I is_diff_invariant_of f along T S) = 
  (\<forall>s\<in>S. I s \<longrightarrow> (g_orbital f T S 0 (\<lambda>s. True) s) \<subseteq> {s. I s})"
  unfolding diff_invariant_def ivp_sols_def g_orbital_eq apply safe
   apply(erule_tac x="xa 0" in ballE)
   apply(drule mp, simp_all)
  apply(erule_tac x="xa 0" in ballE)
  apply(drule mp, simp_all add: subset_eq)
  apply(erule_tac x="xa t" in allE)
  by(drule mp, auto)

context local_flow
begin

lemma diff_invariant_eq_invariant_set:
  "(I is_diff_invariant_of f along T S) = (\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s))"
  apply(subst invariant_to_set, safe)
   apply(erule_tac x=s in ballE)
  unfolding g_evol_collapses by auto

lemma invariant_set_eq_dl_invariant:
  assumes "S = UNIV"
  shows "(\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s)) = ({s. I s} = fb\<^sub>\<F> (orbit) {s. I s})"
  apply(safe, simp_all add: ffb_orbit[OF assms])
    apply(erule_tac x=x in ballE, simp_all add: assms)
  apply(erule_tac x=0 in ballE, erule_tac x=x in allE)
  by(auto simp: ivp(2) init_time assms)

end

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T S" and "I\<^sub>s = {s\<in>S. I s}"
  shows "I\<^sub>s \<le> fb\<^sub>\<F> (x\<acute>=f & G T S) I\<^sub>s"
  using assms by(auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma dInvariant_converse:
  assumes "{s\<in>S. I s} \<le> fb\<^sub>\<F> (x\<acute>=f & (\<lambda>s. True) T S) {s\<in>S. I s}"
  shows "I is_diff_invariant_of f along T S"
  using assms unfolding invariant_to_set ffb_eq by auto

lemma ffb_g_evol_le_requires:
  assumes "\<forall>s. \<exists>x. x \<in> (ivp_sols (\<lambda>t. f) T S 0 s) \<and> G (x 0) \<and> 0 \<in> T"
  shows "fb\<^sub>\<F> (x\<acute>=f & G T S) {s. I s} \<le> {s. I s}"
  unfolding ffb_g_evol apply auto
  using assms apply(erule_tac x=x in allE)
  unfolding ivp_sols_def by auto

lemma dI:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>=f & G {0..t} S) Q"
  apply(rule_tac C="\<lambda>s. s \<in> I" in dCut)
  using assms apply force
  apply(rule dWeakening)
  using assms by auto

text\<open> Finally, we obtain some conditions to prove specific instances of differential invariants. \<close>

named_theorems diff_invariant_rules "compilation of rules for differential invariants."

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> 
  (\<forall>\<tau>\<in>{0..t}. (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = ((*\<^sub>R) 0) on {0..\<tau>}))"
  shows "(\<lambda>s. \<theta> s = \<nu> s) is_diff_invariant_of f along {0..t} S"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<theta> (x 0) = \<nu> (x 0)" 
  hence "\<forall> t \<in> {0..\<tau>}. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R 0) at t within {0..\<tau>}" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>t\<in>{0..\<tau>}. \<theta> (x \<tau>) - \<nu> (x \<tau>) - (\<theta> (x 0) - \<nu> (x 0)) = (\<tau> - 0) \<cdot> 0" 
    by(rule_tac mvt_very_simple) (auto simp: tHyp)
  thus "\<theta> (x \<tau>) = \<nu> (x \<tau>)" by (simp add: x_ivp(2))
qed

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> (\<forall>\<tau>\<in>{0..t}. \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>) \<and> 
  (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>r. \<theta>' (x r) - \<nu>' (x r)) on {0..\<tau>}))"
  shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_diff_invariant_of f along {0..t} S"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t" 
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<nu> (x 0) \<le> \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0..\<tau>}. (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) - \<nu>' (x r))) 
  at r within {0..\<tau>}) \<and> \<nu>' (x r) \<le> \<theta>' (x r)" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>r\<in>{0..\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - 0)" 
    by(rule_tac mvt_very_simple) (auto simp: tHyp)
  then obtain r where "r \<in> {0..\<tau>}" 
    and "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... \<ge> 0" 
    using tHyp(1) x_ivp(2) primed calculation(1) by auto 
  ultimately show "\<nu> (x \<tau>) \<le> \<theta> (x \<tau>)" 
    by simp
qed

lemma [diff_invariant_rules]:
fixes \<theta>::"'a::banach \<Rightarrow> real"
assumes "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> (\<forall>\<tau>\<in>{0..t}. \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>) \<and> 
  (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>r. \<theta>' (x r) - \<nu>' (x r)) on {0..\<tau>}))"
shows "(\<lambda>s. \<nu> s < \<theta> s) is_diff_invariant_of f along {0..t} S"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"0 \<le> \<tau>" "\<tau> \<le> t"
    and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}" "\<nu> (x 0) < \<theta> (x 0)"
  hence primed:"\<forall> r \<in> {0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) has_derivative 
(\<lambda>\<tau>. \<tau> *\<^sub>R  (\<theta>' (x r) -  \<nu>' (x r)))) (at r within {0..\<tau>}) \<and> \<theta>' (x r) \<ge> \<nu>' (x r)" 
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  hence "\<exists>r\<in>{0..\<tau>}. (\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x 0) - \<nu> (x 0)) = 
  (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r))) (\<tau> - 0)" 
    by(rule_tac mvt_very_simple) (auto simp: tHyp)
  then obtain r where "r \<in> {0..\<tau>}" and 
    "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - 0) *\<^sub>R (\<theta>' (x r) -  \<nu>' (x r)) + (\<theta> (x 0) - \<nu> (x 0))" 
    by force 
  also have "... > 0" 
    using tHyp(1) x_ivp(2) primed by (metis (no_types,hide_lams) Groups.add_ac(2) add_sign_intros(1) 
        calculation(1) diff_gt_0_iff_gt ge_iff_diff_ge_0 less_eq_real_def zero_le_scaleR_iff) 
  ultimately show "\<nu> (x \<tau>) < \<theta> (x \<tau>)" 
    by simp
qed

lemma [diff_invariant_rules]:
assumes "I\<^sub>1 is_diff_invariant_of f along {0..t} S" 
    and "I\<^sub>2 is_diff_invariant_of f along {0..t} S"
shows "(\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) is_diff_invariant_of f along {0..t} S"
  using assms unfolding diff_invariant_def by auto

lemma [diff_invariant_rules]:
assumes "I\<^sub>1 is_diff_invariant_of f along {0..t} S" 
    and "I\<^sub>2 is_diff_invariant_of f along {0..t} S"
shows "(\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) is_diff_invariant_of f along {0..t} S"
  using assms unfolding diff_invariant_def by auto

end