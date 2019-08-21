theory cat2ndfun
  imports "../hs_prelims_dyn_sys" "Transformer_Semantics.Kleisli_Quantale" "KAD.Modal_Kleene_Algebra"
                        
begin


chapter\<open> Hybrid System Verification with non-deterministic functions \<close>

\<comment> \<open>We start by deleting some notation and introducing some new.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and "Relation.relcomp" (infixl ";" 75) 
        and Isotone_Transformers.bqtran ("\<lfloor>_\<rfloor>")
        and bres (infixr "\<rightarrow>" 60)

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)
     and fbox ("wp")
     and qstar ("loop")

section\<open> Nondeterministic Functions \<close>

text\<open> Our semantics now corresponds to nondeterministic functions @{typ "'a nd_fun"}. Below we prove
some auxiliary lemmas for them and show that they form an antidomain kleene algebra. The proof just 
extends the results on the Transformer\_Semantics.Kleisli\_Quantale theory.\<close>

declare Abs_nd_fun_inverse [simp]

lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject apply blast
  by(rule ext, simp)

lemma nd_fun_eq_iff: "(\<forall>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) = (f = g)"
  by (auto simp: nd_fun_ext)

instantiation nd_fun :: (type) antidomain_kleene_algebra
begin

lift_definition antidomain_op_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun" 
  is "\<lambda>f. (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>".

lift_definition zero_nd_fun :: "'a nd_fun" 
  is "\<zeta>\<^sup>\<bullet>".

lift_definition star_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun" 
  is "\<lambda>(f::'a nd_fun). qstar f".

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
 a lifting operation from @{typ "'a pred"} to @{typ "'a nd_fun"}.\<close>

abbreviation p2ndf :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

lemma le_p2ndf_iff[simp]: "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  by(transfer, auto simp: le_fun_def)

lemma eq_p2ndf_iff[simp]: "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (P = Q)"
  by(subst eq_iff, auto simp: fun_eq_iff)

lemma p2ndf_le_eta[simp]: "\<lceil>P\<rceil> \<le> \<eta>\<^sup>\<bullet>"
  by(transfer, simp add: le_fun_def, clarify)

lemma ads_d_p2ndf_simps[simp]: 
  "d (\<lceil>P\<rceil> \<cdot> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "d (\<lceil>P\<rceil> + \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "d \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  apply(simp_all add: ads_d_def times_nd_fun_def plus_nd_fun_def kcomp_def)
   apply(simp_all add: antidomain_op_nd_fun_def)
  by (rule nd_fun_ext, force)+

lemma ad_p2ndf[simp]: "ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding antidomain_op_nd_fun_def by(rule nd_fun_ext, auto)

abbreviation ndf2p :: "'a nd_fun \<Rightarrow> 'a \<Rightarrow> bool" ("(1\<lfloor>_\<rfloor>)")
  where "\<lfloor>f\<rfloor> \<equiv> (\<lambda>x. x \<in> Domain (\<R> (f\<^sub>\<bullet>)))"

lemma p2ndf_ndf2p_id: "F \<le> \<eta>\<^sup>\<bullet> \<Longrightarrow> \<lceil>\<lfloor>F\<rfloor>\<rceil> = F"
  unfolding f2r_def apply(rule nd_fun_ext)
  apply(subgoal_tac "\<forall>x. (F\<^sub>\<bullet>) x \<subseteq> {x}", simp)
  by(blast, simp add: le_fun_def less_eq_nd_fun.rep_eq)

section\<open> Verification of regular programs \<close>

text \<open>Properties of the forward box operator. \<close>

lemma wp_nd_fun: "wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<forall>s'. s' \<in> (F s) \<longrightarrow> P s'\<rceil>"
  apply(simp add: fbox_def, transfer, simp)
  by(rule nd_fun_ext, auto simp: kcomp_def)

lemma wp_nd_fun2: "wp F \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<forall>s'. s' \<in> ((F\<^sub>\<bullet>) s) \<longrightarrow> P s'\<rceil>"
  apply(simp add: fbox_def antidomain_op_nd_fun_def)
  by(rule nd_fun_ext, auto simp: Rep_comp_hom kcomp_prop)

lemma p2ndf_ndf2p_wp: "\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  apply(rule p2ndf_ndf2p_id)
  by (simp add: a_subid fbox_def one_nd_fun.transfer)

lemma ndf2p_wpD: "\<lfloor>wp F \<lceil>Q\<rceil>\<rfloor> s = (\<forall>s'. s' \<in> (F\<^sub>\<bullet>) s \<longrightarrow> Q s')"  
  apply(subgoal_tac "F = (F\<^sub>\<bullet>)\<^sup>\<bullet>")
  apply(rule ssubst[of F "(F\<^sub>\<bullet>)\<^sup>\<bullet>"], simp)
  apply(subst wp_nd_fun)
  by(simp_all add: f2r_def)

lemma wp_invariants: 
  assumes "\<lceil>I\<rceil> \<le> wp F \<lceil>I\<rceil>" and "\<lceil>J\<rceil> \<le> wp F \<lceil>J\<rceil>"
  shows "\<lceil>\<lambda>s. I s \<and> J s\<rceil> \<le> wp F \<lceil>\<lambda>s. I s \<and> J s\<rceil>"
    and "\<lceil>\<lambda>s. I s \<or> J s\<rceil> \<le> wp F \<lceil>\<lambda>s. I s \<or> J s\<rceil>"
  using assms unfolding wp_nd_fun2 by simp_all force

text\<open> We check that @{term "fbox"} coincides with our other definition of the forward box operator 
@{thm ffb_def[no_vars]}. \<close>

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

text \<open>The weakest liberal precondition (wlp) of the ``skip'' program is the identity. \<close>

abbreviation "skip \<equiv> \<eta>\<^sup>\<bullet>"

lemma wp_eta[simp]: "wp skip \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  apply(simp add: fbox_def, transfer, simp)
  by(rule nd_fun_ext, auto simp: kcomp_def)

text\<open> Next, we introduce assignments and their @{text "wp"}. \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})\<^sup>\<bullet>" 

lemma wp_assign[simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)\<rceil>"
  unfolding wp_nd_fun2 nd_fun_eq_iff[symmetric] vec_upd_def assign_def by auto

text\<open> The @{text "wp"} of the composition was already obtained in KAD.Antidomain\_Semiring:
@{thm fbox_mult[no_vars]}. \<close>

abbreviation seq_comp :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" (infixl ";" 75)
  where "f ; g \<equiv> f \<cdot> g"

text\<open> We also have an implementation of the conditional operator and its @{text "wp"}. \<close>

definition (in antidomain_kleene_algebra) cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  ("if _ then _ else _ fi" [64,64,64] 63) where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure fbox_def fbox_mult
  by (metis (mono_tags, lifting) a_de_morgan ads_d_def) 

lemma fbox_cond_var[simp]: "|if p then x else y fi] q = (ad p + |x] q) \<cdot> (d p + |y] q)"  
  using cond_def a_closure' ads_d_def ans_d_def fbox_add2 fbox_export1 by (metis (no_types, lifting)) 

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" 
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where "IF P THEN X ELSE Y \<equiv> cond \<lceil>P\<rceil> X Y"

lemma wp_if_then_elseI:
  assumes "\<lceil>\<lambda>s. P s \<and> T s\<rceil> \<le> wp X \<lceil>Q\<rceil>"
    and "\<lceil>\<lambda>s. P s \<and> \<not> T s\<rceil> \<le> wp Y \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (IF T THEN X ELSE Y) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun2)
  apply(subst (asm) wp_nd_fun2)+
  unfolding cond_def apply(clarsimp, transfer)
  by(auto simp: kcomp_prop)

text\<open> We also deal with finite iteration. \<close>

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
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> wp F I"
  shows "P \<le> wp (loop (F::'a nd_fun)) Q"
proof-
  have "P \<le> 1"
    using assms(1,3) by (metis a_subid basic_trans_rules(23) fbox_def) 
  hence "d P = P" using nd_fun_top_ads_d by blast
  have "\<And> x y. d (wp x y) = wp x y"
    by (metis (mono_tags, lifting) a_d_add_closure ads_d_def as2 fbox_def fbox_simp)
  hence "d P \<le> d I \<and> d I \<le> wp F I \<and> d I \<le> d Q"
    using assms by (metis (no_types) ads_d_mono assms)
  hence "d P \<le> wp (F\<^sup>\<star>) Q"
    by(simp add: fbox_starI[of _ I])
  thus "P \<le> wp (loop F) Q"
    using \<open>d P = P\<close> by (transfer, simp)
qed


section\<open> Verification of hybrid programs \<close>

abbreviation g_evolution ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>=f & G on T S @ t\<^sub>0) \<equiv> (\<lambda> s. g_orbital f G T S t\<^sub>0 s)\<^sup>\<bullet>"


subsection \<open>Verification by providing solutions\<close>

text\<open>The wlp of evolution commands. \<close>

lemma wp_g_evolution: "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>= 
  \<lceil>\<lambda> s. \<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq(1) wp_nd_fun by (auto simp: fun_eq_iff image_le_pred)

context local_flow
begin

lemma wp_g_orbit: "wp (x\<acute>=f & G on T S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  unfolding wp_g_evolution apply(clarsimp, simp add: fun_eq_iff, safe)
    apply(erule_tac x="\<lambda>t. \<phi> t x" in ballE)
  using in_ivp_sols apply(force, force, force simp: init_time ivp_sols_def)
  apply(subgoal_tac "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> x", simp_all, clarsimp)
  apply(subst eq_solution, simp_all add: ivp_sols_def)
  using init_time by auto

lemma wp_orbit: "wp (\<gamma>\<^sup>\<phi>\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s))\<rceil>"
  unfolding orbit_def wp_g_orbit by auto

end

subsection\<open> Verification with differential invariants \<close>

lemma wp_g_evolution_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>H\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding wp_g_evolution using assms by auto

lemma wp_g_evolution_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule order.trans)
  using assms(2) apply(rule order.trans)
  apply(rule fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv: "(\<lceil>I\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_evolution image_le_pred by(auto simp: fun_eq_iff)


subsection\<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
  shows "wp (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_orbit[where f="\<lambda>s. c" and \<phi>="(\<lambda> t s. s + t *\<^sub>R c)"])
  using line_is_local_flow[OF assms] unfolding image_le_pred by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.wp_g_orbit, auto)

lemma diff_weak_axiom: "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_evolution image_def by force

lemma diff_weak_rule: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  by (subst wp_nd_fun) (auto simp: g_orbital_eq)

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

lemma wp_g_orbit_IdD:
  assumes "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
    and "\<forall>\<tau>\<in>(down T t). x \<tau> \<in> g_orbital f G T S t\<^sub>0 s"
  shows "\<forall>\<tau>\<in>(down T t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down T t)"
  hence "x \<tau> \<in> g_orbital f G T S t\<^sub>0 s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f G T S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_nd_fun by (subst (asm) nd_fun_eq_iff[symmetric]) auto
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym, simp_all)
  fix s 
  {fix s' assume "s' \<in> g_orbital f G T S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> T" and guard_x:"(\<P> X (down T \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G T S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down T \<tau>). \<P> X (down T t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down T \<tau>). t \<in> T"
      using \<open>\<tau> \<in> T\<close> Thyp by auto
    ultimately have "\<forall>t\<in>(down T \<tau>). X t \<in> g_orbital f G T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down T \<tau>). C (X t)" 
      using wp_g_orbit_IdD[OF assms(3)] by blast
    hence "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> T\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce}
  thus "g_orbital f G T S t\<^sub>0 s \<subseteq> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    by blast
next 
  fix s
  show "g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s \<subseteq> g_orbital f G T S t\<^sub>0 s" 
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & (\<lambda>s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(simp add: wp_nd_fun g_orbital_eq image_le_pred, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_nd_fun, auto)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_nd_fun) auto
qed

text\<open>The rules of dL\<close>

abbreviation g_evol ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>=f & G on UNIV UNIV @ 0)"

lemma DS: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = \<lceil>\<lambda>x. \<forall>t. (\<forall>\<tau>\<le>t. G (x + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + t *\<^sub>R c)\<rceil>"
  by (subst diff_solve_axiom[of UNIV]) (auto simp: fun_eq_iff)

lemma solve:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t. (\<forall>\<tau>\<le>t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule diff_solve_rule[OF assms(1)])
  using assms(2) unfolding image_le_pred by simp

lemma DW: "wp (x\<acute>=f & G) \<lceil>Q\<rceil> = wp (x\<acute>=f & G) \<lceil>\<lambda>s. G s \<longrightarrow> Q s\<rceil>"
  by (rule diff_weak_axiom)
  
lemma dW: "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  by (rule diff_weak_rule)

lemma DC:
  assumes "wp (x\<acute>=f & G) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp (x\<acute>=f & G) \<lceil>Q\<rceil> = wp (x\<acute>=f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  apply (rule diff_cut_axiom) 
  using assms by auto

lemma dC:
  assumes "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>C\<rceil>"
    and "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & (\<lambda>s. G s \<and> C s)) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule diff_cut_rule)
  using assms by auto

lemma dI:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f UNIV UNIV 0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>=f & G) \<lceil>Q\<rceil>"
  apply(rule wp_g_evolution_inv[OF assms(1) _ assms(3)])
  unfolding wp_diff_inv using assms(2) .

end