theory hs_prelims_dyn_sys
  imports hs_prelims

begin

section\<open> Dynamical Systems \<close>

subsection\<open> Initial value problems and orbits \<close>

definition "ivp_sols f T S t\<^sub>0 s = {X |X. (D X = (\<lambda>t. f t (X t)) on T) \<and> X t\<^sub>0 = s \<and> X \<in> T \<rightarrow> S}"

lemma ivp_solsI: 
  assumes "D X = (\<lambda>t. f t (X t)) on T" "X t\<^sub>0 = s" "X \<in> T \<rightarrow> S"
  shows "X \<in> ivp_sols f T S t\<^sub>0 s"
  using assms unfolding ivp_sols_def by blast

lemma ivp_solsD:
  assumes "X \<in> ivp_sols f T S t\<^sub>0 s"
  shows "D X = (\<lambda>t. f t (X t)) on T"
    and "X t\<^sub>0 = s" and "X \<in> T \<rightarrow> S"
  using assms unfolding ivp_sols_def by auto

abbreviation guards :: "('a \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real set) \<Rightarrow> bool" ("_ \<rhd> _ _" [70, 65] 61) 
  where "G \<rhd> X T \<equiv> \<forall>\<tau>\<in>T. G (X \<tau>)"

abbreviation "down T t \<equiv> {t'\<in>T. t'\<le> t}"

definition g_orbital :: "(('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "g_orbital f G T S t\<^sub>0 s = \<Union>{{x t|t. t \<in> T \<and> G \<rhd> x (down T t)}|x. x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f G T S t\<^sub>0 s = 
  {x t|t x. t \<in> T \<and> (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> x \<in> T \<rightarrow> S \<and> G \<rhd> x (down T t)}"
  unfolding g_orbital_def ivp_sols_def by auto

lemma "g_orbital f G T S t\<^sub>0 s = (\<Union>x\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. {x t|t. t \<in> T \<and> G \<rhd> x (down T t)})"
  unfolding g_orbital_def ivp_sols_def by auto

lemma g_orbitalI:
  assumes "D x = (f \<circ> x) on T" "x t\<^sub>0 = s" "x \<in> T \<rightarrow> S"
    and "t \<in> T" and "G \<rhd> x (down T t)"
  shows "x t \<in> g_orbital f G T S t\<^sub>0 s"
  using assms unfolding g_orbital_eq by auto

lemma g_orbitalE:
  assumes "s' \<in> g_orbital f G T S t\<^sub>0 s"
  shows "\<exists> x t. x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s \<and> x t = s' \<and> t \<in> T \<and> G \<rhd> x (down T t)"
  using assms unfolding g_orbital_def ivp_sols_def by auto

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f G T S t\<^sub>0 s"
  obtains x and t where "x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
  and "D x = (f \<circ> x) on T" "x t\<^sub>0 = s" "x \<in> T \<rightarrow> S"
  and "x t = s'" and "t \<in> T" and "G \<rhd> x (down T t)"
  using assms unfolding g_orbital_def ivp_sols_def by auto


subsection\<open> Differential Invariants \<close>

definition diff_invariant :: "('a \<Rightarrow> bool) \<Rightarrow> (('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
  'a set \<Rightarrow> real \<Rightarrow> bool" ("(_)/ is'_diff'_invariant'_of (_)/ along (_ _)/ from (_)" [70,65]61) 
  where "I is_diff_invariant_of f along T S from t\<^sub>0 \<equiv> 
    (\<forall>s\<in>S. I s \<longrightarrow> (\<forall> x. x \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s \<longrightarrow> (\<forall> t \<in> T. I (x t))))"

lemma invariant_to_set: "(I is_diff_invariant_of f along T S from t\<^sub>0) = 
  (\<forall>s\<in>S. I s \<longrightarrow> (g_orbital f (\<lambda>s. True) T S t\<^sub>0 s) \<subseteq> {s. I s})"
  unfolding diff_invariant_def ivp_sols_def g_orbital_eq apply safe
   apply(erule_tac x="xa t\<^sub>0" in ballE)
   apply(drule mp, simp_all)
  apply(erule_tac x="X t\<^sub>0" in ballE)
  apply(drule mp, simp_all add: subset_eq)
  apply(erule_tac x="X t" in allE)
  by(drule mp, auto)

text\<open> Finally, we obtain some conditions to prove specific instances of differential invariants. \<close>

named_theorems diff_invariant_rules "compilation of rules for differential invariants."

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall>x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on T) \<longrightarrow> (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = ((*\<^sub>R) 0) on T)"
  shows "(\<lambda>s. \<theta> s = \<nu> s) is_diff_invariant_of f along T S from t\<^sub>0"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume tHyp:"\<tau> \<in> T" and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on T" "\<theta> (x t\<^sub>0) = \<nu> (x t\<^sub>0)" 
  hence obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R 0) at t within T"
    using assms by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0--\<tau>} \<subseteq> T"
    using closed_segment_subset_interval tHyp Thyp by blast
  hence "D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0--\<tau>}" and "\<theta> (x \<tau>) - \<nu> (x \<tau>) - (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0)) = (\<tau> - t\<^sub>0) * t *\<^sub>R 0"
    using mvt_very_simple_closed_segmentE by blast
  thus "\<theta> (x \<tau>) = \<nu> (x \<tau>)" 
    by (simp add: x_ivp(2))
qed

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on T) \<longrightarrow> (\<forall>\<tau>\<in>T. (\<tau> > t\<^sub>0 \<longrightarrow> \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>)) \<and> 
(\<tau> < t\<^sub>0 \<longrightarrow> \<theta>' (x \<tau>) \<le> \<nu>' (x \<tau>))) \<and> (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>\<tau>. \<theta>' (x \<tau>) - \<nu>' (x \<tau>)) on T)"
  shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_diff_invariant_of f along T S from t\<^sub>0"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume "\<tau> \<in> T" and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on T" "\<nu> (x t\<^sub>0) \<le> \<theta> (x t\<^sub>0)"
  {assume "\<tau> \<noteq> t\<^sub>0"
  hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>)" 
    "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<theta>' (x \<tau>) \<le> \<nu>' (x \<tau>)"
    using x_ivp assms by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x t) - \<nu>' (x t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<\<tau>} \<subseteq> T" "{t\<^sub>0--\<tau>} \<subseteq> T"
    using \<open>\<tau> \<in> T\<close> Thyp \<open>\<tau> \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>\<tau>. \<theta>' (x \<tau>) - \<nu>' (x \<tau>)) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0<--<\<tau>}" and
    "(\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<theta>' (x t) -  \<nu>' (x t))) (\<tau> - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>\<tau> \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) + (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0))" 
    by force
  have  "\<tau> > t\<^sub>0 \<Longrightarrow> t > t\<^sub>0" "\<not> t\<^sub>0 \<le> \<tau> \<Longrightarrow> t < t\<^sub>0" "t \<in> T"
    using \<open>t \<in> {t\<^sub>0<--<\<tau>}\<close> obs2 unfolding open_segment_eq_real_ivl by auto
  moreover have "t > t\<^sub>0 \<Longrightarrow> (\<theta>' (x t) -  \<nu>' (x t)) \<ge> 0" "t < t\<^sub>0 \<Longrightarrow> (\<theta>' (x t) -  \<nu>' (x t)) \<le> 0"
    using primed(1,2)[OF \<open>t \<in> T\<close>] by auto
  ultimately have "(\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) \<ge> 0"
    apply(case_tac "\<tau> \<ge> t\<^sub>0") by (force, auto simp: split_mult_pos_le)
  hence "(\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) + (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0)) \<ge> 0" 
    using  x_ivp(2) by auto
  hence "\<nu> (x \<tau>) \<le> \<theta> (x \<tau>)" 
    using mvt by simp}
  thus "\<nu> (x \<tau>) \<le> \<theta> (x \<tau>)"
    using x_ivp by blast
qed

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "\<forall> x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on T) \<longrightarrow> (\<forall>\<tau>\<in>T. (\<tau> > t\<^sub>0 \<longrightarrow> \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>)) \<and> 
(\<tau> < t\<^sub>0 \<longrightarrow> \<theta>' (x \<tau>) \<le> \<nu>' (x \<tau>))) \<and> (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>\<tau>. \<theta>' (x \<tau>) - \<nu>' (x \<tau>)) on T)"
  shows "(\<lambda>s. \<nu> s < \<theta> s) is_diff_invariant_of f along T S from t\<^sub>0"
proof(simp add: diff_invariant_def ivp_sols_def, clarsimp)
  fix x \<tau> assume "\<tau> \<in> T" and x_ivp:"D x = (\<lambda>\<tau>. f (x \<tau>)) on T" "\<nu> (x t\<^sub>0) < \<theta> (x t\<^sub>0)"
  {assume "\<tau> \<noteq> t\<^sub>0"
  hence primed: "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> > t\<^sub>0 \<Longrightarrow> \<theta>' (x \<tau>) \<ge> \<nu>' (x \<tau>)" 
    "\<And>\<tau>. \<tau> \<in> T \<Longrightarrow> \<tau> < t\<^sub>0 \<Longrightarrow> \<theta>' (x \<tau>) \<le> \<nu>' (x \<tau>)"
    using x_ivp assms by auto
  have obs1: "\<forall>t\<in>T. D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R (\<theta>' (x t) - \<nu>' (x t))) at t within T"
    using assms x_ivp by (auto simp: has_vderiv_on_def has_vector_derivative_def)
  have obs2: "{t\<^sub>0<--<\<tau>} \<subseteq> T" "{t\<^sub>0--\<tau>} \<subseteq> T"
    using \<open>\<tau> \<in> T\<close> Thyp \<open>\<tau> \<noteq> t\<^sub>0\<close> by (auto simp: convex_contains_open_segment 
        is_interval_convex_1 closed_segment_subset_interval)
  hence "D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = (\<lambda>\<tau>. \<theta>' (x \<tau>) - \<nu>' (x \<tau>)) on {t\<^sub>0--\<tau>}"
    using obs1 x_ivp by (auto intro!: has_derivative_subset[OF _ obs2(2)]
        simp: has_vderiv_on_def has_vector_derivative_def)
  then obtain t where "t \<in> {t\<^sub>0<--<\<tau>}" and
    "(\<theta> (x \<tau>) - \<nu> (x \<tau>)) - (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0)) = (\<lambda>\<tau>. \<tau> * (\<theta>' (x t) -  \<nu>' (x t))) (\<tau> - t\<^sub>0)"
    using mvt_simple_closed_segmentE \<open>\<tau> \<noteq> t\<^sub>0\<close> by blast
  hence mvt: "\<theta> (x \<tau>) - \<nu> (x \<tau>) = (\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) + (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0))" 
    by force
  have  "\<tau> > t\<^sub>0 \<Longrightarrow> t > t\<^sub>0" "\<not> t\<^sub>0 \<le> \<tau> \<Longrightarrow> t < t\<^sub>0" "t \<in> T"
    using \<open>t \<in> {t\<^sub>0<--<\<tau>}\<close> obs2 unfolding open_segment_eq_real_ivl by auto
  moreover have "t > t\<^sub>0 \<Longrightarrow> (\<theta>' (x t) -  \<nu>' (x t)) \<ge> 0" "t < t\<^sub>0 \<Longrightarrow> (\<theta>' (x t) -  \<nu>' (x t)) \<le> 0"
    using primed(1,2)[OF \<open>t \<in> T\<close>] by auto
  ultimately have "(\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) \<ge> 0"
    apply(case_tac "\<tau> \<ge> t\<^sub>0") by (force, auto simp: split_mult_pos_le)
  hence "(\<tau> - t\<^sub>0) * (\<theta>' (x t) -  \<nu>' (x t)) + (\<theta> (x t\<^sub>0) - \<nu> (x t\<^sub>0)) > 0" 
    using x_ivp(2) by auto
  hence "\<nu> (x \<tau>) < \<theta> (x \<tau>)" 
    using mvt by simp}
  thus "\<nu> (x \<tau>) < \<theta> (x \<tau>)"
    using x_ivp by blast
qed

lemma [diff_invariant_rules]:
assumes "I\<^sub>1 is_diff_invariant_of f along T S from t\<^sub>0" 
    and "I\<^sub>2 is_diff_invariant_of f along T S from t\<^sub>0"
shows "(\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) is_diff_invariant_of f along T S from t\<^sub>0"
  using assms unfolding diff_invariant_def by auto

lemma [diff_invariant_rules]:
assumes "I\<^sub>1 is_diff_invariant_of f along T S from t\<^sub>0" 
    and "I\<^sub>2 is_diff_invariant_of f along T S from t\<^sub>0"
shows "(\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) is_diff_invariant_of f along T S from t\<^sub>0"
  using assms unfolding diff_invariant_def by auto


subsection\<open> Picard-Lindeloef \<close>

text\<open> The next locale makes explicit the conditions for applying the Picard-Lindeloef theorem. This
guarantees a unique solution for every initial value problem represented with a vector field 
@{term f} and an initial time @{term t\<^sub>0}. It is mostly a simplified reformulation of the approach 
taken by the people who created the Ordinary Differential Equations entry in the AFP. \<close>

locale picard_lindeloef =
  fixes f::"real \<Rightarrow> ('a::{heine_borel,banach}) \<Rightarrow> 'a" and T::"real set" and S::"'a set" and t\<^sub>0::real
  assumes init_time: "t\<^sub>0 \<in> T"
    and cont_vec_field: "\<forall>s \<in> S. continuous_on T (\<lambda>t. f t s)"
    and lipschitz_vec_field: "local_lipschitz T S f"
    and interval_time: "is_interval T"
    and open_domain: "open T" "open S"
begin

sublocale ll_on_open_it T f S t\<^sub>0
  by (unfold_locales) (auto simp: cont_vec_field lipschitz_vec_field interval_time open_domain) 

lemmas subintervalI = closed_segment_subset_domain

lemma subintervalD:
  assumes "{t\<^sub>1--t\<^sub>2} \<subseteq> T"
  shows "t\<^sub>1 \<in> T" and "t\<^sub>2 \<in> T"
  using assms by auto

lemma csols_eq: "csols t\<^sub>0 s = {(X, t). t \<in> T \<and>  X \<in> ivp_sols f {t\<^sub>0--t} S t\<^sub>0 s}"
  unfolding ivp_sols_def csols_def solves_ode_def using subintervalI[OF init_time] by auto

abbreviation "ex_ivl s \<equiv> existence_ivl t\<^sub>0 s"

lemma unique_solution:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on {t\<^sub>0--t}" "X t\<^sub>0 = s" "X \<in> {t\<^sub>0--t} \<rightarrow> S" and "t \<in> T"
    and yivp: "D Y = (\<lambda>t. f t (Y t)) on {t\<^sub>0--t}" "Y t\<^sub>0 = s" "Y \<in> {t\<^sub>0--t} \<rightarrow> S" and "s \<in> S" 
  shows "X t = Y t"
proof-
  have "(X, t) \<in> csols t\<^sub>0 s"
    using xivp \<open>t \<in> T\<close> unfolding csols_eq ivp_sols_def by auto
  hence ivl_fact: "{t\<^sub>0--t} \<subseteq> ex_ivl s"
    unfolding existence_ivl_def by auto
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>{t\<^sub>0--t}. X \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" X] xivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  also have "\<forall>\<tau>\<in>{t\<^sub>0--t}. Y \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "{t\<^sub>0--t}" Y] yivp ivl_fact flow_initial_time[OF init_time  \<open>s \<in> S\<close>] 
    unfolding solves_ode_def by simp
  ultimately show "X t = Y t"
    by auto
qed

lemma solution_eq_flow:
  assumes xivp: "D X = (\<lambda>t. f t (X t)) on ex_ivl s" "X t\<^sub>0 = s" "X \<in> ex_ivl s \<rightarrow> S" 
    and "t \<in> ex_ivl s" and "s \<in> S" 
  shows "X t = flow t\<^sub>0 s t"
proof-
  have obs: "\<And>z T'. t\<^sub>0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> ex_ivl s \<and> (z solves_ode f) T' S \<Longrightarrow> 
  z t\<^sub>0 = flow t\<^sub>0 s t\<^sub>0 \<Longrightarrow> (\<forall>t\<in>T'. z t = flow t\<^sub>0 s t)"
    using flow_usolves_ode[OF init_time \<open>s \<in> S\<close>] unfolding usolves_ode_from_def by blast
  have "\<forall>\<tau>\<in>ex_ivl s. X \<tau> = flow t\<^sub>0 s \<tau>"
    using obs[of "ex_ivl s" X] existence_ivl_initial_time[OF init_time \<open>s \<in> S\<close>]
      xivp flow_initial_time[OF init_time \<open>s \<in> S\<close>] unfolding solves_ode_def by simp
  thus "X t = flow t\<^sub>0 s t"
    by (auto simp: \<open>t \<in> ex_ivl s\<close>)
qed

end

subsection\<open> Flows for ODEs \<close>

text\<open> This locale is a particular case of the previous one. It makes the unique solution for initial 
value problems explicit, it restricts the vector field to reflect autonomous systems (those that do 
not depend explicitly on time), and it sets the initial time equal to 0. This is the first step 
towards formalizing the flow of a differential equation, i.e. the function that maps every point to 
the unique trajectory tangent to the vector field. \<close>

locale local_flow = picard_lindeloef "(\<lambda> t. f)" T S 0 
  for f::"('a::{heine_borel,banach}) \<Rightarrow> 'a" and T S L +
  fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ivp:"\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--t})"
              "\<And> s. s \<in> S \<Longrightarrow> \<phi> 0 s = s"
              "\<And> t s. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> (\<lambda>t. \<phi> t s) \<in> {0--t} \<rightarrow> S"
begin

abbreviation g_orbit :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" ("\<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d")
  where "\<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s \<equiv> g_orbital f G T S 0 s"

definition "orbit s = \<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d (\<lambda>s. True) s"

notation orbit ("\<gamma>\<^sup>\<phi>")

lemma in_ivp_sols_ivl: 
  assumes "t \<in> T" "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> ivp_sols (\<lambda>t. f) {0--t} S 0 s"
  apply(rule ivp_solsI)
  using ivp assms by auto

lemma ex_ivl_eq:
  assumes "s \<in> S"
  shows "ex_ivl s = T"
  using existence_ivl_subset[of s] apply safe
  unfolding existence_ivl_def csols_eq 
  using in_ivp_sols_ivl[OF _ assms] by blast

lemma in_domain:
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> T \<rightarrow> S"
  unfolding ex_ivl_eq[symmetric] existence_ivl_def
  using local.mem_existence_ivl_subset ivp(3)[OF _ assms] by blast

lemma has_derivative_on_open1: 
  assumes  "t > 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t + r/2 > 0"
    using \<open>r > 0\<close> \<open>t > 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t + r/2} \<subseteq> T"
    unfolding abs_le_eq abs_le_eq real_ivl_eqs[OF \<open>t > 0\<close>] real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] 
    by clarify (case_tac "t < x", simp_all add: cball_def ball_def dist_norm subset_eq field_simps)
  have "t + r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs[OF rHyp(1)] by (simp add: subset_eq)
  hence "{0--t + r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t + r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t + r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by auto
  have "t \<in> {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] using rHyp \<open>t > 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t + r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t + r/2}"
    unfolding real_ivl_eqs[OF \<open>t + r/2 > 0\<close>] by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open2: 
  assumes "t < 0" "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball t r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) \<open>t \<in> T\<close> by blast
  moreover have "t - r/2 < 0"
    using \<open>r > 0\<close> \<open>t < 0\<close> by auto
  moreover have "{0--t} \<subseteq> T" 
    using subintervalI[OF init_time \<open>t \<in> T\<close>] .
  ultimately have subs: "{0<--<t - r/2} \<subseteq> T"
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl
      real_ivl_eqs[OF rHyp(1)] by(auto simp: subset_eq)
  have "t - r/2 \<in> T"
    using rHyp unfolding real_ivl_eqs by (simp add: subset_eq)
  hence "{0--t - r/2} \<subseteq> T"
    using subintervalI[OF init_time] by blast
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(t - r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  hence vderiv: "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0<--<t - r/2})"
    apply(rule has_vderiv_on_subset)
    unfolding open_segment_eq_real_ivl closed_segment_eq_real_ivl by auto
  have "t \<in> {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl using rHyp \<open>t < 0\<close> by simp
  moreover have "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) (at t within {0<--<t - r/2})"
    using vderiv calculation unfolding has_vderiv_on_def has_vector_derivative_def by blast
  moreover have "open {0<--<t - r/2}"
    unfolding open_segment_eq_real_ivl by simp
  ultimately show ?thesis
    using subs that by blast
qed

lemma has_derivative_on_open3: 
  assumes "s \<in> S"
  obtains B where "0 \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) at 0 within B" 
proof-
  obtain r::real where rHyp: "r > 0" "ball 0 r \<subseteq> T"
    using open_contains_ball_eq open_domain(1) init_time by blast
  hence "r/2 \<in> T" "-r/2 \<in> T" "r/2 > 0"
    unfolding real_ivl_eqs by auto
  hence subs: "{0--r/2} \<subseteq> T" "{0--(-r/2)} \<subseteq> T"
    using subintervalI[OF init_time] by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)})"
    using ivp(1)[OF _ \<open>s \<in> S\<close>] by auto
  also have "{0--r/2} = {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    "{0--(-r/2)} = {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  ultimately have vderivs:
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--r/2} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {0--(-r/2)} \<union> closure {0--r/2} \<inter> closure {0--(-r/2)})"
    unfolding closed_segment_eq_real_ivl \<open>r/2 > 0\<close> by auto
  have obs: "0 \<in> {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl using \<open>r/2 > 0\<close> by auto
  have union: "{-r/2--r/2} = {0--r/2} \<union> {0--(-r/2)}"
    unfolding closed_segment_eq_real_ivl by auto
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2--r/2})"
    using has_vderiv_on_union[OF vderivs] by simp
  hence "(D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on {-r/2<--<r/2})"
    using has_vderiv_on_subset[OF _ segment_open_subset_closed[of "-r/2" "r/2"]] by auto
  hence "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> 0 s)) (at 0 within {-r/2<--<r/2})"
    unfolding has_vderiv_on_def has_vector_derivative_def using obs by blast
  moreover have "open {-r/2<--<r/2}"
    unfolding open_segment_eq_real_ivl by simp
  moreover have "{-r/2<--<r/2} \<subseteq> T"
    using subs union segment_open_subset_closed by blast 
  ultimately show ?thesis
    using obs that by blast
qed

lemma has_derivative_on_open: 
  assumes "t \<in> T" "s \<in> S"
  obtains B where "t \<in> B" and "open B" and "B \<subseteq> T"
    and "D (\<lambda>\<tau>. \<phi> \<tau> s) \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f (\<phi> t s)) at t within B" 
  apply(subgoal_tac "t < 0 \<or> t = 0 \<or> t > 0")
  using has_derivative_on_open1[OF _ assms] has_derivative_on_open2[OF _ assms]
    has_derivative_on_open3[OF \<open>s \<in> S\<close>] by blast force

lemma has_vderiv_on_domain:
  assumes "s \<in> S"
  shows "D (\<lambda>t. \<phi> t s) = (\<lambda>t. f (\<phi> t s)) on T"
proof(unfold has_vderiv_on_def has_vector_derivative_def, clarsimp)
  fix t assume "t \<in> T"
  then obtain B where "t \<in> B" and "open B" and "B \<subseteq> T" 
    and Dhyp: "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>xa. xa *\<^sub>R f (\<phi> t s)) at t within B"
    using assms has_derivative_on_open[OF \<open>t \<in> T\<close>] by blast
  hence "t \<in> interior B"
    using interior_eq by auto
  thus "D (\<lambda>t. \<phi> t s) \<mapsto> (\<lambda>xa. xa *\<^sub>R f (\<phi> t s)) at t within T"
    using has_derivative_at_within_mono[OF _ \<open>B \<subseteq> T\<close> Dhyp] by blast
qed

lemma eq_solution:
  assumes "X \<in> (ivp_sols (\<lambda>t. f) T S 0 s)" and "t \<in> T" and "s \<in> S"
  shows "X t = \<phi> t s"
proof-
  have "D X = (\<lambda>t. f (X t)) on (ex_ivl s)" and "X 0 = s" and "X \<in> (ex_ivl s) \<rightarrow> S"
    using ivp_solsD[OF assms(1)] unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by auto
  note solution_eq_flow[OF this]
  hence "X t = flow 0 s t"
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] using assms by blast
  also have "\<phi> t s = flow 0 s t"
    apply(rule solution_eq_flow ivp)
        apply(simp_all add: assms(2,3) ivp(2)[OF \<open>s \<in> S\<close>])
    unfolding ex_ivl_eq[OF \<open>s \<in> S\<close>] by (auto simp: has_vderiv_on_domain assms in_domain)
  ultimately show "X t = \<phi> t s"
    by simp
qed

lemma in_ivp_sols: 
  assumes "s \<in> S"
  shows "(\<lambda>t. \<phi> t s) \<in> ivp_sols (\<lambda>t. f) T S 0 s"
  using has_vderiv_on_domain ivp(2) in_domain apply(rule ivp_solsI)
  using assms by auto

lemma eq_solution_ivl:
  assumes xivp: "D X = (\<lambda>t. f (X t)) on {0--t}" "X 0 = s" "X \<in> {0--t} \<rightarrow> S" 
    and indom: "t \<in> T" "s \<in> S"
  shows "X t = \<phi> t s"
  apply(rule unique_solution[OF xivp \<open>t \<in> T\<close>])
  using \<open>s \<in> S\<close> ivp indom by auto

lemma additive_in_ivp_sols:
  assumes "s \<in> S" and "(\<lambda>\<tau>. \<tau> + t) ` T \<subseteq> T"
  shows "(\<lambda>\<tau>. \<phi> (\<tau> + t) s) \<in> ivp_sols (\<lambda>t. f) T S 0 (\<phi> (0 + t) s)"
  apply(rule ivp_solsI, rule vderiv_on_compose_add)
  using has_vderiv_on_domain has_vderiv_on_subset assms apply blast
  using in_domain assms by auto

lemma is_monoid_action:
  assumes indom: "t\<^sub>1 \<in> T" "t\<^sub>2 \<in> T" "s \<in> S" 
    and "(\<lambda>\<tau>. \<tau> + t\<^sub>2) ` T \<subseteq> T"
  shows "\<phi> 0 s = s"
    and "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
proof-
  show "\<phi> 0 s = s"
    using ivp indom by simp
  have "\<phi> (0 + t\<^sub>2) s = \<phi> t\<^sub>2 s" 
    by simp
  also have "\<phi> t\<^sub>2 s \<in> S"
    using in_domain indom by auto
  finally show "\<phi> (t\<^sub>1 + t\<^sub>2) s = \<phi> t\<^sub>1 (\<phi> t\<^sub>2 s)"
    using eq_solution[OF additive_in_ivp_sols] assms by auto
qed

lemma orbit_eq[simp]: 
  assumes "s \<in> S"
  shows "\<gamma>\<^sup>\<phi> s = {\<phi> t s| t. t \<in> T}"
  using eq_solution assms unfolding orbit_def g_orbital_eq ivp_sols_def
  by(auto intro!: has_vderiv_on_domain ivp(2) in_domain)

lemma g_orbit_eq: 
  assumes "s \<in> S"
  shows "\<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s = {\<phi> t s| t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) (down T t)}" (is "_ = ?gorbit")
proof(rule subset_antisym, simp_all only: subset_eq)
  {fix s' assume "s' \<in> \<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s"
    then obtain x and t where x_ivp:"x \<in> ivp_sols (\<lambda>t. f) T S 0 s" 
      and "x t = s'" and "t \<in> T" and guard:"G \<rhd> x (down T t)"
      unfolding g_orbital_def by auto
    hence obs:"\<forall>\<tau>\<in>(down T t). x \<tau> = \<phi> \<tau> s"
      using eq_solution[OF x_ivp _ assms] init_time
      by blast
    hence "G \<rhd> (\<lambda>r. \<phi> r s) (down T t)"
      using guard
      by auto 
    also have "\<phi> t s = x t"
      using eq_solution[OF x_ivp \<open>t \<in> T\<close> assms] by simp
    ultimately have "s' \<in> ?gorbit"
      using \<open>x t = s'\<close> \<open>t \<in> T\<close> by auto}
  thus "\<forall>s'\<in>\<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s. s' \<in> ?gorbit"
    by blast
next
  {fix s' assume "s' \<in> ?gorbit"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) (down T t)" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> \<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s"
      using assms by(auto intro!: g_orbitalI in_domain ivp(2) 
          has_vderiv_on_domain simp: init_time)}
  thus "\<forall>s'\<in>?gorbit. s' \<in> \<gamma>\<^sup>\<phi>\<^sub>G\<^sub>u\<^sub>a\<^sub>r\<^sub>d G s"
    by blast
qed

lemma ivp_sols_collapse: 
  assumes "S = UNIV" "T = UNIV"
  shows "ivp_sols (\<lambda>t. f) T S 0 s = {(\<lambda>t. \<phi> t s)}"
  using in_ivp_sols eq_solution unfolding assms by auto

lemma diff_invariant_eq_invariant_set:
  "(I is_diff_invariant_of f along T S from 0) = (\<forall>s\<in>S. \<forall>t\<in>T. I s \<longrightarrow> I (\<phi> t s))"
  apply(subst invariant_to_set, safe)
   apply(erule_tac x=s in ballE)
  unfolding g_orbit_eq by auto

end

end