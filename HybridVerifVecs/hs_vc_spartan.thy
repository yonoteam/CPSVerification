theory hs_vc_spartan
  imports hs_prelims_dyn_sys
                        
begin


chapter \<open>Hybrid System Verification\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

notation Union ("\<mu>")
     and g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")

abbreviation "skip \<equiv> (\<lambda>s. {s})"

section \<open>Verification of regular programs\<close>

text \<open>First we add lemmas for computation of weakest liberal preconditions (wlps).\<close>

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred" ("|_] _" [61,81] 82)
  where "|F] P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

lemma fbox_iso: "P \<le> Q \<Longrightarrow> |F] P \<le> |F] Q"
  unfolding fbox_def by auto

lemma fbox_invariants: 
  assumes "I \<le> |F] I" and "J \<le> |F] J"
  shows "(\<lambda>s. I s \<and> J s) \<le> |F] (\<lambda>s. I s \<and> J s)"
    and "(\<lambda>s. I s \<or> J s) \<le> |F] (\<lambda>s. I s \<or> J s)"
  using assms unfolding fbox_def by auto

text \<open>Now, we compute wlps for specific programs.\<close>

lemma fbox_eta[simp]: "fbox skip P = P"
  unfolding fbox_def by simp

text \<open>Next, we introduce assignments and their wlps.\<close>

definition vec_upd :: "'a^'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'a^'n"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'n \<Rightarrow> ('a^'n \<Rightarrow> 'a) \<Rightarrow> 'a^'n \<Rightarrow> ('a^'n) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})" 

lemma fbox_assign[simp]: "|x ::= e] Q = (\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding vec_upd_def assign_def by (subst fbox_def) simp

text \<open>The wlp of a (kleisli) composition is just the composition of the wlps.\<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl ";" 75) where
  "F ; G = \<mu> \<circ> \<P> G \<circ> F"

lemma kcomp_eq: "(f ; g) x = \<Union> {g y |y. y \<in> f x}"
  unfolding kcomp_def image_def by auto

lemma fbox_kcomp[simp]: "|G ; F] P = |G] |F] P"
  unfolding fbox_def kcomp_def by auto

lemma fbox_kcomp_ge:
  assumes "P \<le> |G] R" "R \<le> |F] Q"
  shows "P \<le> |G ; F] Q"
  apply(subst fbox_kcomp) 
  by (rule order.trans[OF assms(1)]) (rule fbox_iso[OF assms(2)])

text \<open>We also have an implementation of the conditional operator and its wlp.\<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where 
  "IF P THEN X ELSE Y \<equiv> (\<lambda>s. if P s then X s else Y s)"

lemma fbox_if_then_else[simp]:
  "|IF T THEN X ELSE Y] Q = (\<lambda>s. (T s \<longrightarrow> ( |X] Q) s) \<and> (\<not> T s \<longrightarrow> ( |Y] Q) s))"
  unfolding fbox_def ifthenelse_def by auto

lemma fbox_if_then_else_ge:
  assumes "(\<lambda>s. P s \<and> T s) \<le> |X] Q"
    and "(\<lambda>s. P s \<and> \<not> T s) \<le> |Y] Q"
  shows "P \<le> |IF T THEN X ELSE Y] Q"
  using assms unfolding fbox_def ifthenelse_def by auto

lemma fbox_if_then_elseI:
  assumes "T s \<longrightarrow> ( |X] Q) s"
    and "\<not> T s \<longrightarrow> ( |Y] Q) s"
  shows "( |IF T THEN X ELSE Y] Q) s"
  using assms unfolding fbox_def ifthenelse_def by auto

text \<open>The final wlp we add is that of the finite iteration.\<close>

definition kpower :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where "kpower f n = (\<lambda>s. ((;) f ^^ n) skip s)"

lemma kpower_base:
  shows "kpower f 0 s = {s}" and "kpower f (Suc 0) s = f s"
  unfolding kpower_def by(auto simp: kcomp_eq)

lemma kpower_simp: "kpower f (Suc n) s = (f ; kpower f n) s"
  unfolding kcomp_eq apply(induct n)
  unfolding kpower_base apply(rule subset_antisym, clarsimp, force, clarsimp)
  unfolding kpower_def kcomp_eq by simp

definition kleene_star :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>*)" [1000] 999)
  where "(f\<^sup>*) s = \<Union> {kpower f n s |n. n \<in> UNIV}"

lemma kpower_inv: 
  fixes F :: "'a \<Rightarrow> 'a set"
  assumes "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> F s \<longrightarrow> I s')" 
  shows "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> (kpower F n s) \<longrightarrow> I s')"
  apply(clarsimp, induct n)
  unfolding kpower_base apply simp
  unfolding kpower_simp apply(simp add: kcomp_eq, clarsimp) 
  apply(subgoal_tac "I y", simp)
  using assms by blast

lemma kstar_inv: "I \<le> |F] I \<Longrightarrow> I \<le> |F\<^sup>*] I"
  unfolding kleene_star_def fbox_def apply clarsimp
  apply(unfold le_fun_def, subgoal_tac "\<forall>x. I x \<longrightarrow> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  apply(thin_tac "\<forall>x. I x \<le> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  using kpower_inv[of I F] by blast simp

lemma fbox_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F] I" 
  shows "P \<le> |F\<^sup>*] Q"
proof-
  have "I \<le> |F\<^sup>*] I"
    using assms(3) kstar_inv by blast
  hence "P \<le> |F\<^sup>*] I"
    using assms(1) by auto
  also have "|F\<^sup>*] I \<le> |F\<^sup>*] Q"
    by (rule fbox_iso[OF assms(2)])
  finally show ?thesis .
qed

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP F INV I \<equiv> (F\<^sup>*)"

lemma fbox_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F] I \<Longrightarrow> P \<le> |LOOP F INV I] Q"
  unfolding loopi_def using fbox_kstarI[of "P"] by simp


section \<open>Verification of hybrid programs\<close>


subsection \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "EVOL \<phi> G T = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G T)"

lemma fbox_g_evol[simp]: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G T] Q = (\<lambda>s. (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding g_evol_def g_orbit_eq fbox_def by auto


subsection \<open>Verification by providing solutions\<close>

lemma fbox_g_orbital: "|x\<acute>=f & G on T S @ t\<^sub>0] Q = 
  (\<lambda>s. \<forall>X\<in>Sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq by (auto simp: fun_eq_iff)

context local_flow
begin

lemma fbox_g_ode: "|x\<acute>=f & G on T S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))" (is "_ = ?wlp")
  unfolding fbox_g_orbital apply(rule ext, safe, clarsimp)
    apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE)
  using in_ivp_sols apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma fbox_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> |x\<acute>=f & G on {0..t} S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding fbox_g_orbital apply(rule ext, clarsimp, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t s" in ballE, force)
  using in_ivp_sols_ivl apply(force simp: closed_segment_eq_real_ivl)
  using in_ivp_sols_ivl apply(force simp: ivp_sols_def)
   apply(subgoal_tac "\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. X \<tau> = \<phi> \<tau> s)", simp, clarsimp)
  apply(subst eq_solution_ivl, simp_all add: ivp_sols_def)
     apply(rule has_vderiv_on_subset, force, force simp: closed_segment_eq_real_ivl)
    apply(force simp: closed_segment_eq_real_ivl)
  using interval_time init_time apply (meson is_interval_1 order_trans) 
  using init_time by force

lemma fbox_orbit: "|\<gamma>\<^sup>\<phi>] Q = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  unfolding orbit_def fbox_g_ode by simp

end


subsection\<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma fbox_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "|x\<acute>=f & G on T S @ t\<^sub>0] Q = |x\<acute>=f & G on T S @ t\<^sub>0] H "
  unfolding fbox_g_orbital using assms by auto

lemma fbox_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> |x\<acute>=f & G on T S @ t\<^sub>0] I" and "I \<le> Q"
  shows "P \<le> |x\<acute>=f & G on T S @ t\<^sub>0] Q"
  using assms(1) apply(rule order.trans)
  using assms(2) apply(rule order.trans)
  by (rule fbox_iso[OF assms(3)])

lemma fbox_diff_inv[simp]: 
  "(I \<le> |x\<acute>=f & G on T S @ t\<^sub>0] I) = diff_invariant I f T S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def fbox_def g_orbital_eq)

lemma fbox_g_odei: "P \<le> I \<Longrightarrow> I \<le> |x\<acute>= f & G on T S @ t\<^sub>0] I \<Longrightarrow> (\<lambda>s. I s \<and> G s) \<le> Q \<Longrightarrow> 
  P \<le> |x\<acute>= f & G on T S @ t\<^sub>0 DINV I] Q"
  unfolding g_ode_inv_def apply(rule_tac b="|x\<acute>= f & G on T S @ t\<^sub>0] I" in order.trans)
   apply(rule_tac I="I" in fbox_g_orbital_inv, simp_all)
  apply(subst fbox_g_orbital_guard, simp)
  by (rule fbox_iso, force)

abbreviation g_global_orbit ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>=f & G DINV I) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0 DINV I)"

end