theory cat2funcset
  imports "../hs_prelims" "Transformer_Semantics.Kleisli_Quantale"
                        
begin

chapter \<open>Hybrid System Verification\<close>

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
type_synonym 'a pred = "'a \<Rightarrow> bool"

section \<open>Verification of regular programs\<close>

text \<open>First we add lemmas for computation of weakest liberal preconditions (wlps).\<close>

lemma ffb_eta[simp]:"fb\<^sub>\<F> \<eta> X = X"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

lemma ffb_eq:"fb\<^sub>\<F> F X = {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> X}"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by auto

lemma ffb_eq_univD:"fb\<^sub>\<F> F P = UNIV \<Longrightarrow> (\<forall>y. y \<in> (F x) \<longrightarrow> y \<in> P)"
proof
  fix y assume "fb\<^sub>\<F> F P = UNIV"
  hence "UNIV = {s. \<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P}" 
    by(subst ffb_eq[THEN sym], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. y \<in> (F s) \<longrightarrow> y \<in> P)}" 
    by auto
  then show "s2p (F x) y \<longrightarrow> y \<in> P" 
    by auto
qed

text \<open>Next, we introduce assignments and their wlps.\<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) 
  where "x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) \<Rightarrow> ('a^'b) set" ("(2[_ ::== _])" [70, 65] 61) 
  where "[x ::== expr]\<equiv> (\<lambda>s. {s[x :== expr s]})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> ([x ::== expr]) Q = {s. (s[x :== expr s]) \<in> Q}"
  by(subst ffb_eq, simp)

text \<open>The wlp of a (kleisli) composition is just the composition of the wlps.\<close>

lemma ffb_kcomp:"fb\<^sub>\<F> (G \<circ>\<^sub>K F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_def apply(simp add: kop_def klift_def map_dual_def)
  unfolding dual_set_def f2r_def r2f_def by(auto simp: kcomp_def)

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

lemma kstar_inv:"I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  by(auto simp: kcomp_prop) 

lemma ffb_star_induct_self:"I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (kstar F) I"
  apply(subst ffb_eq, subst (asm) ffb_eq)
  unfolding kstar_def apply clarsimp
  using kstar_inv by blast

lemma ffb_starI:
assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> F I" and "I \<le> Q"
shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  from assms(2) have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using ffb_star_induct_self by blast
  then have "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  from this and assms(3) show ?thesis
    by(subst ffb_eq, subst (asm) ffb_eq, auto)
qed


section \<open>Verification of hybrid programs\<close>

subsection \<open>Verification by providing solutions\<close>

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

text\<open>We use closed segments instead of closed intervals for the following definition due to the 
following property.\<close>

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

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> real set \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1[x\<acute>=_]_ & _)") 
  where "[x\<acute>=f]T & G \<equiv> (\<lambda> s. g_orbital f T 0 G s)"

lemmas g_evol_def = g_orbital_eq[where t\<^sub>0=0]

lemma g_evolI:
  assumes "D x = (f \<circ> x) on T" "x 0 = s"
    and "0 \<in> T" "t \<in> T" and "G \<rhd> x {0--t}"
  shows "x t \<in> ([x\<acute>=f]T & G) s"
  using assms unfolding g_orbital_def ivp_sols_def by blast

lemma g_evolD:
  assumes "s' \<in> ([x\<acute>=f]T & G) s"
  obtains x and t where "x \<in> ivp_sols f T 0 s" 
  and "D x = (f \<circ> x) on T" "x 0 = s"
  and "x t = s'" and "0 \<in> T" "t \<in> T" and "G \<rhd> x {0--t}"
  using assms unfolding g_orbital_def ivp_sols_def by blast

context local_flow
begin

lemma in_ivp_sols: "(\<lambda>t. \<phi> t s) \<in> ivp_sols f T 0 s"
  by(auto intro: ivp_solsI simp: ivp init_time)

definition "orbit s = g_orbital f T 0 (\<lambda>s. True) s"

lemma orbit_eq[simp]: "orbit s = {\<phi> t s| t. t \<in> T}"
  unfolding orbit_def g_evol_def 
  by(auto intro: usolves_ivp intro!: ivp simp: init_time)

lemma g_evol_collapses: 
  shows "([x\<acute>=f]T & G) s = {\<phi> t s| t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0--t}}" (is "_ = ?gorbit")
proof(rule subset_antisym, simp_all only: subset_eq)
  {fix s' assume "s' \<in> ([x\<acute>=f]T & G) s"
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
  thus "\<forall>s'\<in>([x\<acute>=f]T & G) s. s' \<in> ?gorbit"
    by blast
next
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) {0--t}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> ([x\<acute>=f]T & G) s"
      by(auto intro: g_evolI simp: ivp init_time)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> ([x\<acute>=f]T & G) s"
    by blast
qed

lemma ffb_orbit: "fb\<^sub>\<F> (orbit) Q = {s. \<forall> t \<in> T. \<phi> t s \<in> Q}"
  unfolding orbit_eq ffb_eq by auto

lemma ffb_g_orbit: "fb\<^sub>\<F> ([x\<acute>=f]T & G) Q = {s. \<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) {0--t}) \<longrightarrow> (\<phi> t s) \<in> Q}"
  unfolding g_evol_collapses ffb_eq by auto 

end

lemma (in global_flow) ivp_sols_collapse[simp]: "ivp_sols f UNIV 0 s = {(\<lambda>t. \<phi> t s)}"
  by(auto intro: usolves_ivp simp: ivp_sols_def ivp)

text\<open> The previous lemma allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f T L \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall> t \<in> T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> ([x\<acute>=f]T & G) Q"
  using assms apply(subst local_flow.ffb_g_orbit)
  by (auto simp: Starlike.closed_segment_eq_real_ivl)

lemma ffb_line: "0 \<le> t \<Longrightarrow> fb\<^sub>\<F> ([x\<acute>=\<lambda>t. c]{0..t} & G) Q = 
    {x. \<forall> \<tau> \<in> {0..t}. (G \<rhd> (\<lambda>r. x + r *\<^sub>R c) {0..\<tau>}) \<longrightarrow> (x + \<tau> *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_orbit[of "\<lambda> t. c" _ "1/(t + 1)" "(\<lambda> t x. x + t *\<^sub>R c)"])
  by(auto simp: line_is_local_flow closed_segment_eq_real_ivl)

subsection\<open> Verification with differential invariants \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in our verification proofs.\<close>

subsubsection\<open> Differential Weakening \<close>
        
lemma DW:
  shows "fb\<^sub>\<F> ([x\<acute>=f]T & G) Q = fb\<^sub>\<F> ([x\<acute>=f]T & G) {s. G s \<longrightarrow> s \<in> Q}"
  by(auto intro: g_evolD simp: ffb_eq)
  
lemma dWeakening: 
assumes "{s. G s} \<le> Q"
shows "P \<le> fb\<^sub>\<F> ([x\<acute>=f]T & G) Q"
  using assms by(auto intro: g_evolD simp: le_fun_def g_evol_def ffb_eq)

subsubsection\<open> Differential Cut \<close>

lemma ffb_g_orbit_eq_univD:
  assumes "fb\<^sub>\<F> ([x\<acute>=f]T & G) {s. C s} = UNIV" 
    and "\<forall> r\<in>{0--t}. x r \<in> ([x\<acute>=f]T & G) s"
  shows "\<forall>r\<in>{0--t}. C (x r)"
proof
  fix r assume "r \<in> {0--t}"
  then have "x r \<in> ([x\<acute>=f]T & G) s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> ([x\<acute>=f]T & G) s \<longrightarrow> C y" 
    using assms(1) ffb_eq_univD by fastforce
  ultimately show "C (x r)" by blast
qed

lemma DC:
  assumes "interval T" and "fb\<^sub>\<F> ([x\<acute>=f]T & G) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> ([x\<acute>=f]T & G) Q = fb\<^sub>\<F> ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> ([x\<acute>=f]T & G) s"
    then obtain t::real and x where x_ivp: "D x = (f \<circ> x) on T" "x 0 = s"
      and guard_x:"G \<rhd> x {0--t}" and "s' = x t" and "0 \<in> T" "t \<in> T"
      using g_evolD[of s' "f" T G s] by (metis (full_types))
    from guard_x have "\<forall>r\<in>{0--t}.\<forall> \<tau>\<in>{0--r}. G (x \<tau>)"
      by (metis contra_subsetD ends_in_segment(1) subset_segment(1))
    also have "\<forall>\<tau>\<in>{0--t}. \<tau> \<in> T"
      using interval.closed_segment_subset_domain[OF assms(1) \<open>0 \<in> T\<close> \<open>t \<in> T\<close>] by blast
    ultimately have "\<forall>\<tau>\<in>{0--t}. x \<tau> \<in> ([x\<acute>=f]T & G) s"
      using g_evolI[OF x_ivp \<open>0 \<in> T\<close>] by blast
    hence "C \<rhd> x {0--t}" 
      using ffb_g_orbit_eq_univD assms(2) by blast
    hence "s' \<in> ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) s"
      using g_evolI[OF x_ivp \<open>0 \<in> T\<close> \<open>t \<in> T\<close>] guard_x \<open>s' = x t\<close> by fastforce}
  thus "([x\<acute>=f]T & G) s \<subseteq> ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) s"
    by blast
next show "\<And>s. ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) s \<subseteq> ([x\<acute>=f]T & G) s" 
    by (auto simp: g_evol_def)
qed

lemma dCut:
  assumes ffb_C:"P \<le> fb\<^sub>\<F> ([x\<acute>=f]{0..t} & G) {s. C s}"
    and ffb_Q:"P \<le> fb\<^sub>\<F> ([x\<acute>=f]{0..t} & (\<lambda> s. G s \<and> C s)) Q"
  shows "P \<le> fb\<^sub>\<F> ([x\<acute>=f]{0..t} & G) Q"
proof(subst ffb_eq, subst g_evol_def, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "(x 0) \<in> P" and "0 \<le> \<tau>" and "\<tau> \<le> t"
    and x_solves:"D x = (\<lambda>t. f (x t)) on {0..t}" and guard_x:"(\<forall> r \<in> {0--\<tau>}. G (x r))"
  hence "\<forall>r\<in>{0--\<tau>}.\<forall>\<tau>\<in>{0--r}. G (x \<tau>)"
    using closed_segment_closed_segment_subset by blast
  hence "\<forall>r\<in>{0--\<tau>}. x r \<in> ([x\<acute>=f]{0..t} & G) (x 0)"
    using g_evolI x_solves \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce 
  hence "\<forall>r\<in>{0--\<tau>}. C (x r)" 
    using ffb_C \<open>(x 0) \<in> P\<close> by(subst (asm) ffb_eq, auto)
  hence "x \<tau> \<in> ([x\<acute>=f]{0..t} & (\<lambda> s. G s \<and> C s)) (x 0)"
    using g_evolI x_solves guard_x \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> by fastforce
  from this \<open>(x 0) \<in> P\<close> and ffb_Q show "(x \<tau>) \<in> Q"
    by(subst (asm) ffb_eq, auto simp: closed_segment_eq_real_ivl)
qed

subsubsection\<open> Differential Invariant \<close>

lemma DI_sufficiency:
  assumes "\<forall>s. \<exists>x. x \<in> ivp_sols f T 0 s"
  shows "fb\<^sub>\<F> ([x\<acute>=f]T & G) Q \<le> fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q"
  using assms apply(subst ffb_eq, subst ffb_eq, clarsimp)
  apply(rename_tac s, erule_tac x="s" in allE, erule impE)
  apply(simp add: g_evol_def ivp_sols_def)
  apply(erule_tac x="s" in allE, clarify)
  by(rule_tac x="0" in exI, rule_tac x=x in exI, auto)

lemma (in local_flow) DI_necessity: (* Not true... check Bohrer formalisation *)
  shows "fb\<^sub>\<F> (\<lambda> x. {s. s = x \<and> G s}) Q \<le> fb\<^sub>\<F> ([x\<acute>=f]T & G) Q"
  unfolding ffb_g_orbit apply(subst ffb_eq, clarsimp, safe)
   apply(erule_tac x="0" in ballE)
    apply(simp add: ivp, simp)
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

context local_flow
begin

lemma diff_invariant_eq_invariant_set:
  "(I is_diff_invariant_of f along T) = (\<forall>s. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s))"
  by(subst invariant_to_set, auto simp: g_evol_collapses)

lemma invariant_set_eq_dl_invariant:
  shows "(\<forall>s. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s)) = ({s. I s} = fb\<^sub>\<F> (orbit) {s. I s})"
  apply(safe, simp_all add: ffb_orbit)
   apply(erule_tac x=0 in ballE)
  by(auto simp: ivp(2) init_time)

end

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T"
  shows "{s. I s} \<le> fb\<^sub>\<F> ([x\<acute>=f]T & G) {s. I s}"
  using assms by(auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma dInvariant_converse:
  assumes "{s. I s} \<le> fb\<^sub>\<F> ([x\<acute>=f]T & (\<lambda>s. True)) {s. I s}"
  shows "I is_diff_invariant_of f along T"
  using assms unfolding invariant_to_set ffb_eq by auto

lemma ffb_g_evol_le_requires:
  assumes "\<forall>s. \<exists>x. x \<in> (ivp_sols f T 0 s) \<and> G s"
    shows "fb\<^sub>\<F> ([x\<acute>=f]T & G) {s. I s} \<le> {s. I s}"
  apply(simp add: ffb_eq g_orbital_eq, clarify)
  apply(erule_tac x="x" in allE, erule impE, simp_all)
  using assms ivp_solsD(1) by(fastforce simp: ivp_sols_def)

lemma dI:
assumes "I is_diff_invariant_of f along {0..t}"
    and "P \<le> {s. I s}" and "{s. I s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> ([x\<acute>=f]{0..t} & G) Q"
  apply(rule_tac C="I" in dCut)
  using dInvariant assms apply blast
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