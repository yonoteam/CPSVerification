theory cat2ndfun
  imports "../hs_prelims_matrices" "Transformer_Semantics.Kleisli_Quantale" "KAD.Modal_Kleene_Algebra"
                        
begin

chapter\<open> Hybrid System Verification with nondeterministic functions \<close>

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Isotone_Transformers.bqtran ("\<lfloor>_\<rfloor>")

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

section\<open> Nondeterministic Functions \<close>

text\<open> Our semantics correspond now to nondeterministic functions @{typ "'a nd_fun"}. Below we prove
some auxiliary lemmas for them and show that they form an antidomain kleene algebra. The proof just 
extends the results on the Transformer\_Semantics.Kleisli\_Quantale theory.\<close>

declare Abs_nd_fun_inverse [simp]

\<comment> \<open>Analog of already existing @{thm fun_eq_iff[no_vars]}.\<close>
lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject apply blast
  by(rule ext, simp)

instantiation nd_fun :: (type) antidomain_kleene_algebra
begin

lift_definition antidomain_op_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun" 
  is "\<lambda>f. (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>".

lift_definition zero_nd_fun :: "'a nd_fun" 
  is "\<zeta>\<^sup>\<bullet>".

lift_definition star_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun" 
  is "\<lambda>(f::'a nd_fun).qstar f".

lift_definition plus_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" 
  is "\<lambda>f g.((f\<^sub>\<bullet>) \<squnion> (g\<^sub>\<bullet>))\<^sup>\<bullet>".

named_theorems nd_fun_aka "antidomain kleene algebra properties for nondeterministic functions."

lemma nd_fun_assoc[nd_fun_aka]: "(a::'a nd_fun) + b + c = a + (b + c)"
  by(transfer, simp add: ksup_assoc)

lemma nd_fun_comm[nd_fun_aka]: "(a::'a nd_fun) + b = b + a"
  by(transfer, simp add: ksup_comm)

lemma nd_fun_distr[nd_fun_aka]: "((x::'a nd_fun) + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_aka]: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  by(transfer, simp add: kcomp_distr, transfer, simp add: kcomp_distl)

lemma nd_fun_zero_sum[nd_fun_aka]: "0 + (x::'a nd_fun) = x" 
  and nd_fun_zero_dot[nd_fun_aka]: "0 \<cdot> x = 0"
  by(transfer, simp, transfer, auto) 

lemma nd_fun_leq[nd_fun_aka]: "((x::'a nd_fun) \<le> y) = (x + y = y)"
  and nd_fun_leq_add[nd_fun_aka]: " z \<cdot> x \<le> z \<cdot> (x + y)"
   apply(transfer)
   apply(metis (no_types, lifting) less_eq_nd_fun.transfer sup.absorb_iff2 sup_nd_fun.transfer)
  by(transfer, simp add: kcomp_isol)

lemma nd_fun_ad_zero[nd_fun_aka]: "ad (x::'a nd_fun) \<cdot> x = 0"
  and nd_fun_ad[nd_fun_aka]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and nd_fun_ad_one[nd_fun_aka]: "ad (ad x) + ad x = 1"
   apply(transfer, rule nd_fun_ext, simp add: kcomp_def)
   apply(transfer, rule nd_fun_ext, simp, simp add: kcomp_def)
  by(transfer, simp, rule nd_fun_ext, simp add: kcomp_def)

lemma nd_star_one[nd_fun_aka]: "1 + (x::'a nd_fun) \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_aka]: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_aka]: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
    apply(transfer, metis Abs_nd_fun_inverse Rep_comp_hom UNIV_I fun_star_unfoldr 
      le_sup_iff less_eq_nd_fun.abs_eq mem_Collect_eq one_nd_fun.abs_eq qstar_comm)
   apply(transfer, metis (no_types, lifting) Abs_comp_hom Rep_nd_fun_inverse 
      fun_star_inductl less_eq_nd_fun.transfer sup_nd_fun.transfer)
  by(transfer, metis qstar_inductr Rep_comp_hom Rep_nd_fun_inverse 
      less_eq_nd_fun.abs_eq sup_nd_fun.transfer)

instance
  apply intro_classes apply auto
  using nd_fun_aka apply simp_all
  by(transfer; auto)+

end

text\<open> Now that we know that nondeterministic functions form an Antidomain Kleene Algebra, we give
 a lifting operation from predicates to @{typ "'a nd_fun"} and prove some useful results for them. 
Then we add an operation that does the opposite and prove the relationship between both of these. \<close>

abbreviation p2ndf :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

lemma le_p2ndf_iff[simp]: "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  by(transfer, auto simp: le_fun_def)

lemma p2ndf_le_eta[simp]: "\<lceil>P\<rceil> \<le> \<eta>\<^sup>\<bullet>"
  by(transfer, simp add: le_fun_def, clarify)

lemma ads_d_p2ndf[simp]: "d \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  unfolding ads_d_def antidomain_op_nd_fun_def by(rule nd_fun_ext, auto)

lemma ad_p2ndf[simp]: "ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding antidomain_op_nd_fun_def by(rule nd_fun_ext, auto)

abbreviation ndf2p :: "'a nd_fun \<Rightarrow> 'a \<Rightarrow> bool" ("(1\<lfloor>_\<rfloor>)")
  where "\<lfloor>f\<rfloor> \<equiv> (\<lambda>x. x \<in> Domain (\<R> (f\<^sub>\<bullet>)))"

lemma p2ndf_ndf2p_id: "F \<le> \<eta>\<^sup>\<bullet> \<Longrightarrow> \<lceil>\<lfloor>F\<rfloor>\<rceil> = F"
  unfolding f2r_def apply(rule nd_fun_ext)
  apply(subgoal_tac "\<forall>x. (F\<^sub>\<bullet>) x \<subseteq> {x}", simp)
  by(blast, simp add: le_fun_def less_eq_nd_fun.rep_eq)

section\<open> Verification of regular programs \<close>

text\<open> As expected, the weakest precondition is just the forward box operator from the KAD. Below 
we explore its behavior with the previously defined lifting ($\lceil-\rceil$*) and dropping 
($\lfloor-\rfloor$*) operators \<close>

abbreviation "wp f \<equiv> fbox (f::'a nd_fun)"

lemma wp_eta[simp]: "wp (\<eta>\<^sup>\<bullet>) \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  apply(simp add: fbox_def, transfer, simp)
  by(rule nd_fun_ext, auto simp: kcomp_def)

lemma wp_nd_fun: "wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. y \<in> (F x) \<longrightarrow> P y\<rceil>"
  apply(simp add: fbox_def, transfer, simp)
  by(rule nd_fun_ext, auto simp: kcomp_def)

lemma wp_nd_fun2: "wp F \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. y \<in> ((F\<^sub>\<bullet>) x) \<longrightarrow> P y\<rceil>"
  apply(simp add: fbox_def antidomain_op_nd_fun_def)
  by(rule nd_fun_ext, auto simp: Rep_comp_hom kcomp_prop)

lemma wp_nd_fun_etaD: "wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<eta>\<^sup>\<bullet> \<Longrightarrow>  (\<forall>y. y \<in> (F x) \<longrightarrow> P y)"
proof
  fix y assume "wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = (\<eta>\<^sup>\<bullet>)"
  from this have "\<eta>\<^sup>\<bullet> = \<lceil>\<lambda>s. \<forall>y. s2p (F s) y \<longrightarrow> P y\<rceil>" 
    by(subst wp_nd_fun[THEN sym], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. s2p (F s) y \<longrightarrow> P y)}"
    apply(subst (asm) Abs_nd_fun_inject, simp_all)
    by(drule_tac x="x" in fun_cong, simp)
  then show "s2p (F x) y \<longrightarrow> P y" by auto
qed

lemma p2ndf_ndf2p_wp: "\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  apply(rule p2ndf_ndf2p_id)
  by (simp add: a_subid fbox_def one_nd_fun.transfer)

lemma ndf2p_wpD: "\<lfloor>wp F \<lceil>Q\<rceil>\<rfloor> s = (\<forall>s'. s' \<in> (F\<^sub>\<bullet>) s \<longrightarrow> Q s')"  
  apply(subgoal_tac "F = (F\<^sub>\<bullet>)\<^sup>\<bullet>")
  apply(rule ssubst[of F "(F\<^sub>\<bullet>)\<^sup>\<bullet>"], simp)
  apply(subst wp_nd_fun)
  by(simp_all add: f2r_def)

text\<open> We can verify that our introduction of @{text "wp"} coincides with another definition of the 
forward box operator @{thm ffb_def[no_vars]} with the following characterization lemmas. \<close>

lemma ffb_is_wp: "fb\<^sub>\<F> (F\<^sub>\<bullet>) {x. P x} = {s. \<lfloor>wp F \<lceil>P\<rceil>\<rfloor> s}"
  unfolding ffb_def unfolding map_dual_def klift_def kop_def fbox_def
  unfolding r2f_def f2r_def apply clarsimp
  unfolding antidomain_op_nd_fun_def unfolding dual_set_def 
  unfolding times_nd_fun_def kcomp_def by force

lemma wp_is_ffb: "wp F P = (\<lambda>x. {x} \<inter> fb\<^sub>\<F> (F\<^sub>\<bullet>) {s. \<lfloor>P\<rfloor> s})\<^sup>\<bullet>"
  apply(rule nd_fun_ext, simp)
  unfolding ffb_def unfolding map_dual_def klift_def kop_def fbox_def
  unfolding r2f_def f2r_def apply clarsimp
  unfolding antidomain_op_nd_fun_def unfolding dual_set_def 
  unfolding times_nd_fun_def apply auto
  unfolding kcomp_prop by auto

text\<open> Next, we introduce assignments and compute their @{text "wp"}. \<close>

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd x i a \<equiv> vec_lambda ((vec_nth x)(i := a))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e)\<equiv> (\<lambda>s. {vec_upd s x (e s)})\<^sup>\<bullet>" 

lemma wp_assign[simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (vec_upd s x (e s))\<rceil>"
  by(subst wp_nd_fun, rule nd_fun_ext, simp)

text\<open> The @{text "wp"} of the composition was already obtained in KAD.Antidomain\_Semiring:
@{thm fbox_mult[no_vars]}. \<close>

text\<open> We also have an implementation of the conditional operator and its @{text "wp"}. \<close>

definition (in antidomain_kleene_algebra) cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  ("if _ then _ else _ fi" [64,64,64] 63) where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" 
  ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where "IF P THEN X ELSE Y FI \<equiv> cond \<lceil>P\<rceil> X Y"

lemma wp_if_then_else:
  assumes "\<lceil>\<lambda>s. P s \<and> T s\<rceil> \<le> wp X \<lceil>Q\<rceil>"
    and "\<lceil>\<lambda>s. P s \<and> \<not> T s\<rceil> \<le> wp Y \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (IF T THEN X ELSE Y FI) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun2)
  apply(subst (asm) wp_nd_fun2)+
  unfolding cond_def apply(clarsimp, transfer)
  by(auto simp: kcomp_prop)

text\<open> Finally we also deal with finite iteration. \<close>

lemma (in antidomain_kleene_algebra) fbox_starI: 
  assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
  shows "d p \<le> |x\<^sup>\<star>] q"
  by (meson assms local.dual_order.trans local.fbox_iso local.fbox_star_induct_var)

lemma ads_d_mono: "x \<le> y \<Longrightarrow> d x \<le> d y"
  by (metis ads_d_def fbox_antitone_var fbox_dom)

lemma nd_fun_top_ads_d:"(x::'a nd_fun) \<le> 1 \<Longrightarrow> d x = x"
  apply(simp add: ads_d_def, transfer, simp)
  apply(rule nd_fun_ext, simp)
  apply(subst (asm) le_fun_def)
  by auto

lemma wp_starI:
  assumes "P \<le> I" and "I \<le> wp F I" and "I \<le> Q"
  shows "P \<le> wp (qstar F) Q"
proof-
  have "P \<le> 1"
    using assms(1,2) by (metis a_subid basic_trans_rules(23) fbox_def) 
  hence "d P = P" using nd_fun_top_ads_d by blast
  have "\<And> x y. d (wp x y) = wp x y"
    by(metis ds.ddual.mult_oner fbox_mult fbox_one)
  hence "d P \<le> d I \<and> d I \<le> wp F I \<and> d I \<le> d Q"
    using assms by (metis (no_types) ads_d_mono assms)
  hence "d P \<le> wp (F\<^sup>\<star>) Q"
    by(simp add: fbox_starI[of _ I])
  thus "P \<le> wp (qstar F) Q"
    using \<open>d P = P\<close> by (transfer, simp)
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

definition "g_orbital f T t\<^sub>0 G s = \<Union> {{x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0..t} }|x. x \<in> ivp_sols f T t\<^sub>0 s}"

lemma g_orbital_eq: "g_orbital f T t\<^sub>0 G s = 
  {x t |t x. t \<in> T \<and> (D x = (f \<circ> x) on T) \<and> x t\<^sub>0 = s \<and> t\<^sub>0 \<in> T \<and> G \<rhd> x {t\<^sub>0..t}}"
  unfolding g_orbital_def ivp_sols_def by auto

lemma "g_orbital f T t\<^sub>0 G s = (\<Union> x \<in> ivp_sols f T t\<^sub>0 s. {x t|t. t \<in> T \<and> G \<rhd> x {t\<^sub>0..t}})"
  unfolding g_orbital_def ivp_sols_def by auto

lemma g_orbitalI:
  assumes "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
    and "t\<^sub>0 \<in> T" "t \<in> T" and "G \<rhd> x {t\<^sub>0..t}"
  shows "x t \<in> g_orbital f T t\<^sub>0 G s"
  using assms unfolding g_orbital_def ivp_sols_def by blast

lemma g_orbitalD:
  assumes "s' \<in> g_orbital f T t\<^sub>0 G s"
  obtains x and t where "x \<in> ivp_sols f T t\<^sub>0 s" 
  and "D x = (f \<circ> x) on T" "x t\<^sub>0 = s"
  and "x t = s'" and "t\<^sub>0 \<in> T" "t \<in> T" and "G \<rhd> x {t\<^sub>0..t}"
  using assms unfolding g_orbital_def ivp_sols_def by blast

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> real set \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1[x\<acute>=_]_ & _)") 
  where "[x\<acute>=f]T & G \<equiv> (\<lambda> s. g_orbital f T 0 G s)\<^sup>\<bullet>"

lemmas g_evol_def = g_orbital_eq[where t\<^sub>0=0]

context local_flow
begin

lemma in_ivp_sols: "(\<lambda>t. \<phi> t s) \<in> ivp_sols f T 0 s"
  by(auto intro: ivp_solsI simp: ivp init_time)

definition "orbit s = g_orbital f T 0 (\<lambda>s. True) s"

lemma orbit_eq[simp]: "orbit s = {\<phi> t s| t. t \<in> T}"
  unfolding orbit_def g_evol_def 
  by(auto intro: usolves_ivp intro!: ivp simp: init_time)

lemma g_evol_collapses: 
  shows "([x\<acute>=f]T & G) = (\<lambda>s. {\<phi> t s| t. t \<in> T \<and> G \<rhd> (\<lambda>r. \<phi> r s) {0..t}})\<^sup>\<bullet>"
proof(rule nd_fun_ext, rule subset_antisym, simp_all add: subset_eq)
  fix s
  let "?P s s'" = "\<exists>t. s' = \<phi> t s \<and> s2p T t \<and> (\<forall>r\<in>{0..t}. G (\<phi> r s))"
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
    ultimately have "\<exists>t. s' = \<phi> t s \<and> s2p T t \<and> (\<forall>r\<in>{0..t}. G (\<phi> r s))"
      using \<open>x t = s'\<close> \<open>t \<in> T\<close> by auto}
  thus "\<forall>s'\<in>g_orbital f T 0 G s. ?P s s'"
    by blast
  {fix s' assume "\<exists>t. s' = \<phi> t s \<and> s2p T t \<and> (\<forall>r\<in>{0..t}. G (\<phi> r s))"
    then obtain t where "G \<rhd> (\<lambda>r. \<phi> r s) {0..t}" and "t \<in> T" and "\<phi> t s = s'"
      by blast
    hence "s' \<in> g_orbital f T 0 G s"
      by(auto intro: g_orbitalI simp: ivp init_time)}
  thus "\<forall>s'. ?P s s' \<longrightarrow> s' \<in> (g_orbital f T 0 G s)"
    by blast
qed

lemma wp_orbit: "wp ((\<lambda> s. orbit s)\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
  unfolding orbit_eq wp_nd_fun apply(rule nd_fun_ext) by auto

lemma wp_g_orbit: "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall>t\<in>T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding g_evol_collapses wp_nd_fun apply(rule nd_fun_ext) by auto

end

lemma (in local_flow) ivp_sols_collapse: "ivp_sols f T 0 s = {(\<lambda>t. \<phi> t s)}"
  apply(auto simp: ivp_sols_def ivp init_time fun_eq_iff)
  apply(rule unique_solution, simp_all add: ivp)
  oops

text\<open> The previous lemma allows us to compute wlps for known systems of ODEs. We can also implement
a version of it as an inference rule. A simple computation of a wlp is shown immmediately after.\<close>

lemma dSolution:
  assumes "local_flow f T L \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. (G \<rhd> (\<lambda>r. \<phi> r s) {0..t}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_orbit, auto)

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
        
lemma DW: "wp ([x\<acute>=f]{0..t} & G) \<lceil>Q\<rceil> = wp ([x\<acute>=f]{0..t} & G) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  apply(rule nd_fun_ext)
  by (auto intro: g_orbitalD simp: wp_nd_fun)

lemma dWeakening: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & G) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun)
  by(auto simp: g_evol_def)

subsubsection\<open> Differential Cut \<close>

lemma wp_g_orbit_etaD:
  assumes "wp ([x\<acute>=f]T & G) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>" and "\<forall> r\<in>{0..t}. x r \<in> g_orbital f T 0 G s"
  shows "\<forall>r\<in>{0..t}. C (x r)"
proof
  fix r assume "r \<in> {0..t}"
  then have "x r \<in> g_orbital f T 0 G s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f T 0 G s) \<longrightarrow> C y" 
    using assms(1) wp_nd_fun_etaD by fastforce
  ultimately show "C (x r)" by blast
qed

lemma DC:
  assumes "interval T" and "wp ([x\<acute>=f]T & G) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> = wp ([x\<acute>=f]T & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym, simp_all)
  fix s
  {fix s' assume "s' \<in> g_orbital f T 0 G s"
    then obtain t::real and x where x_ivp: "D x = (f \<circ> x) on T" "x 0 = s"
      and guard_x:"G \<rhd> x {0..t}" and "s' = x t" and "0 \<in> T" "t \<in> T"
      using g_orbitalD[of s' "f" T 0 G s] by (metis (full_types))
    from guard_x have "\<forall>r\<in>{0..t}.\<forall> \<tau>\<in>{0..r}. G (x \<tau>)"
      by auto
    also have "\<forall>\<tau>\<in>{0..t}. \<tau> \<in> T"
      by (meson \<open>0 \<in> T\<close> \<open>t \<in> T\<close> assms(1) atLeastAtMost_iff interval.interval mem_is_interval_1_I) 
    ultimately have "\<forall>\<tau>\<in>{0..t}. x \<tau> \<in> g_orbital f T 0 G s"
      using g_orbitalI[OF x_ivp \<open>0 \<in> T\<close>] by blast
    hence "C \<rhd> x {0..t}" 
      using wp_g_orbit_etaD assms(2) by blast
    hence "s' \<in> g_orbital f T 0 (\<lambda>s. G s \<and> C s) s"
      using g_orbitalI[OF x_ivp \<open>0 \<in> T\<close> \<open>t \<in> T\<close>] guard_x \<open>s' = x t\<close> by fastforce}
  thus "g_orbital f T 0 G s \<subseteq> g_orbital f T 0 (\<lambda>s. G s \<and> C s) s"
    by blast
next show "\<And>s. g_orbital f T 0 (\<lambda>s. G s \<and> C s) s \<subseteq> g_orbital f T 0 G s" 
    by (auto simp: g_evol_def)
qed

lemma dCut:
  assumes wp_C:"\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & G) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & (\<lambda> s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ([x\<acute>=f]{0..t} & G) \<lceil>Q\<rceil>"
proof(simp add: wp_nd_fun g_orbital_eq, clarsimp)
  fix \<tau>::real and x::"real \<Rightarrow> 'a" assume "P (x 0)" and "0 \<le> \<tau>" and "\<tau> \<le> t"
    and x_solves:"D x = (\<lambda>t. f (x t)) on {0..t}" and guard_x:"(\<forall> r \<in> {0..\<tau>}. G (x r))"
  hence "\<forall>r\<in>{0..\<tau>}.\<forall>\<tau>\<in>{0..r}. G (x \<tau>)"
    by auto
  hence "\<forall>r\<in>{0..\<tau>}. x r \<in> g_orbital f {0..t} 0 G (x 0)"
    using g_orbitalI x_solves \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> closed_segment_eq_real_ivl by fastforce 
  hence "\<forall>r\<in>{0..\<tau>}. C (x r)" 
    using wp_C \<open>P (x 0)\<close> by(subst (asm) wp_nd_fun, auto)
  hence "x \<tau> \<in> g_orbital f {0..t} 0 (\<lambda>s. G s \<and> C s) (x 0)"
    using g_orbitalI x_solves guard_x \<open>0 \<le> \<tau>\<close> \<open>\<tau> \<le> t\<close> by fastforce
  from this \<open>P (x 0)\<close> and wp_Q show "Q (x \<tau>)"
    by(subst (asm) wp_nd_fun, auto simp: closed_segment_eq_real_ivl)
qed

subsubsection\<open> Differential Invariant \<close>

lemma DI_sufficiency:
  assumes "\<forall>s. \<exists>x. x \<in> ivp_sols f T 0 s"
  shows "wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil> \<le> wp \<lceil>G\<rceil> \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun, subst wp_nd_fun, clarsimp)
  apply(rename_tac s, erule_tac x="s" in allE, erule impE)
  apply(simp add: g_evol_def ivp_sols_def)
  apply(erule_tac x="s" in allE, clarify)
  by(rule_tac x="0" in exI, rule_tac x=x in exI, auto)

lemma (in local_flow) DI_necessity:
  shows "wp \<lceil>G\<rceil> \<lceil>Q\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>Q\<rceil>"
  unfolding wp_g_orbit apply(subst wp_nd_fun, clarsimp, safe)
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

lemma dInvariant:
  assumes "I is_diff_invariant_of f along T"
  shows "\<lceil>I\<rceil> \<le> wp ([x\<acute>=f]T & G) \<lceil>I\<rceil>"
  using assms unfolding diff_invariant_def apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff, clarify)
  apply(erule_tac x="s" in allE)
  unfolding g_orbital_def by auto

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

named_theorems diff_invariant_rules "compilation of rules for differential invariants."

lemma [diff_invariant_rules]:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (D x = (\<lambda>\<tau>. f (x \<tau>)) on {0..t}) \<longrightarrow> 
  (\<forall>\<tau>\<in>{0..t}. (D (\<lambda>\<tau>. \<theta> (x \<tau>) - \<nu> (x \<tau>)) = ((*\<^sub>R) 0) on {0..\<tau>}))"
  shows "(\<lambda>s. \<theta> s = \<nu> s) is_diff_invariant_of f along {0..t}"
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
  shows "(\<lambda>s. \<nu> s \<le> \<theta> s) is_diff_invariant_of f along {0..t}"
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
shows "(\<lambda>s. \<nu> s < \<theta> s) is_diff_invariant_of f along {0..t}"
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
assumes "I\<^sub>1 is_diff_invariant_of f along {0..t}" 
    and "I\<^sub>2 is_diff_invariant_of f along {0..t}"
shows "(\<lambda>s. I\<^sub>1 s \<and> I\<^sub>2 s) is_diff_invariant_of f along {0..t}"
  using assms unfolding diff_invariant_def by auto

lemma [diff_invariant_rules]:
assumes "I\<^sub>1 is_diff_invariant_of f along {0..t}" 
    and "I\<^sub>2 is_diff_invariant_of f along {0..t}"
shows "(\<lambda>s. I\<^sub>1 s \<or> I\<^sub>2 s) is_diff_invariant_of f along {0..t}"
  using assms unfolding diff_invariant_def by auto

end