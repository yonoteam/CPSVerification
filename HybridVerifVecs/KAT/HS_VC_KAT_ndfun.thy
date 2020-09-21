(*  Title:       Verification and refinement of hybrid systems in the relational KAT
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification and refinement of HS in the relational KAT \<close>

text \<open> We use our state transformers model to obtain verification and refinement components for 
hybrid programs. We devise three methods for reasoning with evolution commands and their continuous 
dynamics: providing flows, solutions or invariants. \<close>

theory HS_VC_KAT_ndfun
  imports 
    "HS_VC_KAT"
    "../HS_ODEs"
    "Transformer_Semantics.Kleisli_Quantale"

begin

subsection \<open> Store and Hoare triples \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

\<comment> \<open>We start by deleting some conflicting notation.\<close>

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

declare Abs_nd_fun_inverse [simp]


no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and tau ("\<tau>")
        and Relation.relcomp (infixl ";" 75)
        and proto_near_quantale_class.bres (infixr "\<rightarrow>" 60)

lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject 
   apply blast
  by(rule ext, simp)

lemma nd_fun_eq_iff: "(f = g) = (\<forall>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x)"
  by (auto simp: nd_fun_ext)

instantiation nd_fun :: (type) kleene_algebra
begin

definition "0 = \<zeta>\<^sup>\<bullet>"

definition "star_nd_fun f = qstar f" for f::"'a nd_fun"

definition "f + g = ((f\<^sub>\<bullet>) \<squnion> (g\<^sub>\<bullet>))\<^sup>\<bullet>"

thm sup_nd_fun_def sup_fun_def

named_theorems nd_fun_aka "antidomain kleene algebra properties for nondeterministic functions."

lemma nd_fun_plus_assoc[nd_fun_aka]: "x + y + z = x + (y + z)"
  and nd_fun_plus_comm[nd_fun_aka]: "x + y = y + x"
  and nd_fun_plus_idem[nd_fun_aka]: "x + x = x" for x::"'a nd_fun"
  unfolding plus_nd_fun_def by (simp add: ksup_assoc, simp_all add: ksup_comm)

lemma nd_fun_distr[nd_fun_aka]: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_aka]: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z" for x::"'a nd_fun"
  unfolding plus_nd_fun_def times_nd_fun_def by (simp_all add: kcomp_distr kcomp_distl)

lemma nd_fun_plus_zerol[nd_fun_aka]: "0 + x = x" 
  and nd_fun_mult_zerol[nd_fun_aka]: "0 \<cdot> x = 0"
  and nd_fun_mult_zeror[nd_fun_aka]: "x \<cdot> 0 = 0" for x::"'a nd_fun"
  unfolding plus_nd_fun_def zero_nd_fun_def times_nd_fun_def by auto

lemma nd_fun_leq[nd_fun_aka]: "(x \<le> y) = (x + y = y)"
  and nd_fun_less[nd_fun_aka]: "(x < y) = (x + y = y \<and> x \<noteq> y)"
  and nd_fun_leq_add[nd_fun_aka]: "z \<cdot> x \<le> z \<cdot> (x + y)" for x::"'a nd_fun"
  unfolding less_eq_nd_fun_def less_nd_fun_def plus_nd_fun_def times_nd_fun_def sup_fun_def
  by (unfold nd_fun_eq_iff le_fun_def, auto simp: kcomp_def)

lemma nd_star_one[nd_fun_aka]: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_aka]: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_aka]: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y" for x::"'a nd_fun"
  unfolding plus_nd_fun_def star_nd_fun_def
    apply(simp_all add: fun_star_inductl sup_nd_fun.rep_eq fun_star_inductr)
  by (metis order_refl sup_nd_fun.rep_eq uwqlka.conway.dagger_unfoldl_eq)

instance
  apply intro_classes
  using nd_fun_aka by simp_all

end

instantiation nd_fun :: (type) kat
begin

definition "n f = (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>"

lemma nd_fun_n_op_one[nd_fun_aka]: "n (n (1::'a nd_fun)) = 1"
  and nd_fun_n_op_mult[nd_fun_aka]: "n (n (n x \<cdot> n y)) = n x \<cdot> n y"
  and nd_fun_n_op_mult_comp[nd_fun_aka]: "n x \<cdot> n (n x) = 0" 
  and nd_fun_n_op_de_morgan[nd_fun_aka]: "n (n (n x) \<cdot> n (n y)) = n x + n y" for x::"'a nd_fun"
  unfolding n_op_nd_fun_def one_nd_fun_def times_nd_fun_def plus_nd_fun_def zero_nd_fun_def 
  by (auto simp: nd_fun_eq_iff kcomp_def)

instance
  by (intro_classes, auto simp: nd_fun_aka)

end

instantiation nd_fun :: (type) rkat
begin

definition "Ref_nd_fun P Q \<equiv> (\<lambda>s. \<Union>{(f\<^sub>\<bullet>) s|f. Hoare P f Q})\<^sup>\<bullet>"

instance
  apply(intro_classes)
  by (unfold Hoare_def n_op_nd_fun_def Ref_nd_fun_def times_nd_fun_def)
    (auto simp: kcomp_def le_fun_def less_eq_nd_fun_def)

end

\<comment> \<open>Canonical lifting from predicates to state transformers and its simplification rules\<close>

definition p2ndf :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

lemma p2ndf_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> \<cdot> \<lceil>Q\<rceil>) = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> + \<lceil>Q\<rceil>) = \<lceil>\<lambda>s. P s \<or> Q s\<rceil>"
  "\<tt>\<tt> \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  "n \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding p2ndf_def one_nd_fun_def less_eq_nd_fun_def times_nd_fun_def plus_nd_fun_def 
  by (auto simp: nd_fun_eq_iff kcomp_def le_fun_def n_op_nd_fun_def)

\<comment> \<open> Meaning of the state-transformer Hoare triple \<close>

lemma ndfun_kat_H: "Hoare \<lceil>P\<rceil> X \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s s'. P s \<longrightarrow> s' \<in> (X\<^sub>\<bullet>) s \<longrightarrow> Q s')"
  unfolding Hoare_def p2ndf_def less_eq_nd_fun_def times_nd_fun_def kcomp_def 
  by (auto simp add: le_fun_def n_op_nd_fun_def)

\<comment> \<open> Hoare triple for skip and a simp-rule \<close>

abbreviation "skip \<equiv> (1::'a nd_fun)"

lemma H_skip: "Hoare \<lceil>P\<rceil> skip \<lceil>P\<rceil>"
  using H_skip by blast

lemma sH_skip[simp]: "Hoare \<lceil>P\<rceil> skip \<lceil>Q\<rceil> \<longleftrightarrow> \<lceil>P\<rceil> \<le> \<lceil>Q\<rceil>"
  unfolding ndfun_kat_H by (simp add: one_nd_fun_def)

\<comment> \<open> We introduce assignments and compute derive their rule of Hoare logic. \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})\<^sup>\<bullet>"

lemma H_assign: "P = (\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil>"
  unfolding ndfun_kat_H assign_def vec_upd_def by force

lemma sH_assign[simp]: "Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding ndfun_kat_H vec_upd_def assign_def by (auto simp: fun_upd_def)

\<comment> \<open> Next, the Hoare rule of the composition \<close>

abbreviation seq_seq :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" (infixl ";" 75)
  where "f ; g \<equiv> f \<cdot> g"

lemma H_seq: "Hoare \<lceil>P\<rceil> X \<lceil>R\<rceil> \<Longrightarrow> Hoare \<lceil>R\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> Hoare \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil>"
  by (auto intro: H_seq)

lemma sH_seq: "Hoare \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil> = Hoare \<lceil>P\<rceil> (X) \<lceil>\<lambda>s. \<forall>s'. s' \<in> (Y\<^sub>\<bullet>) s \<longrightarrow> Q s'\<rceil>"
  unfolding ndfun_kat_H by (auto simp: times_nd_fun_def kcomp_def)

\<comment> \<open> Rewriting the Hoare rule for the conditional statement \<close>

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF B THEN X ELSE Y \<equiv> kat_cond \<lceil>B\<rceil> X Y"

lemma H_cond: "Hoare \<lceil>\<lambda>s. P s \<and> B s\<rceil> X \<lceil>Q\<rceil> \<Longrightarrow> Hoare \<lceil>\<lambda>s. P s \<and> \<not> B s\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> 
  Hoare \<lceil>P\<rceil> (IF B THEN X ELSE Y) \<lceil>Q\<rceil>"
  by (rule H_cond, simp_all)

lemma sH_cond[simp]: "Hoare \<lceil>P\<rceil> (IF B THEN X ELSE Y) \<lceil>Q\<rceil> \<longleftrightarrow> 
  (Hoare \<lceil>\<lambda>s. P s \<and> B s\<rceil> X \<lceil>Q\<rceil> \<and> Hoare \<lceil>\<lambda>s. P s \<and> \<not> B s\<rceil> Y \<lceil>Q\<rceil>)"
  by (auto simp: H_cond_iff ndfun_kat_H)

\<comment> \<open> Rewriting the Hoare rule for the while loop \<close>

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" ("WHILE _ INV _ DO _" [64,64,64] 63) 
  where "WHILE B INV I DO X \<equiv> kat_while_inv \<lceil>B\<rceil> \<lceil>I\<rceil> X"

lemma sH_while_inv: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> B s \<longrightarrow> Q s \<Longrightarrow> Hoare \<lceil>\<lambda>s. I s \<and> B s\<rceil> X \<lceil>I\<rceil> 
  \<Longrightarrow> Hoare \<lceil>P\<rceil> (WHILE B INV I DO X) \<lceil>Q\<rceil>"
  by (rule H_while_inv, simp_all add: ndfun_kat_H)

\<comment> \<open> Finally, we add a Hoare triple rule for finite iterations. \<close>

abbreviation loopi_sugar :: "'a nd_fun \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP X INV I \<equiv> kat_loop_inv X \<lceil>I\<rceil>"

lemma H_loop: "Hoare \<lceil>P\<rceil> X \<lceil>P\<rceil> \<Longrightarrow> Hoare \<lceil>P\<rceil> (LOOP X INV I) \<lceil>P\<rceil>"
  by (auto intro: H_loop)

lemma H_loopI: "Hoare \<lceil>I\<rceil> X \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> Hoare \<lceil>P\<rceil> (LOOP X INV I) \<lceil>Q\<rceil>"
  using H_loop_inv[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" X "\<lceil>Q\<rceil>"] by auto


subsection\<open> Verification of hybrid programs \<close>

\<comment> \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> 'b nd_fun" ("EVOL")
  where "EVOL \<phi> G U = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G (U s))\<^sup>\<bullet>"

lemma sH_g_evol[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "Hoare \<lceil>P\<rceil> (EVOL \<phi> G U) \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding ndfun_kat_H g_evol_def g_orbit_eq by auto

lemma H_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes "P = (\<lambda>s. (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  shows "Hoare \<lceil>P\<rceil> (EVOL \<phi> G U) \<lceil>Q\<rceil>"
  by (simp add: assms)

\<comment> \<open>Verification by providing solutions\<close>

definition g_ode ::"(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a nd_fun" ("(1x\<acute>= _ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0) \<equiv> (\<lambda> s. g_orbital f G U S t\<^sub>0 s)\<^sup>\<bullet>"

lemma H_g_orbital: 
  "P = (\<lambda>s. (\<forall>X\<in>ivp_sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t))) \<Longrightarrow> 
  Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding ndfun_kat_H g_ode_def g_orbital_eq by clarsimp

lemma sH_g_orbital: "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  (\<forall>s. P s \<longrightarrow> (\<forall>X\<in>ivp_sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t)))"
  unfolding g_orbital_eq g_ode_def ndfun_kat_H by auto

context local_flow
begin

lemma sH_g_ode_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
proof(unfold sH_g_orbital, clarsimp, safe)
  fix s t
  assume hyps: "s \<in> S" "P s" "t \<in> U s" "\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)"
    and main: "\<forall>s. P s \<longrightarrow> (\<forall>X\<in>Sols (\<lambda>t. f) U S 0 s. \<forall>t\<in>U s. (\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> Q (X t))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) U S 0 s"
    using in_ivp_sols assms by blast
  thus "Q (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "P s" "X \<in> Sols (\<lambda>t. f) U S 0 s" "t \<in> U s"  "\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
    and main: "\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  hence obs: "s \<in> S"
    using ivp_sols_def[of "\<lambda>t. f"] init_time by auto
  hence "\<forall>\<tau>\<in>down (U s) t. X \<tau> = \<phi> \<tau> s"
    using eq_solution hyps assms by blast
  thus "Q (X t)"
    using hyps main obs by auto
qed

lemma H_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "P = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))" 
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<lceil>Q\<rceil>"
  using assms apply(subst sH_g_ode_subset[OF assms(1)])
  unfolding assms by auto

lemma sH_g_ode: "Hoare \<lceil>P\<rceil> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst sH_g_ode_subset, auto simp: init_time interval_time)

lemma sH_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> Hoare \<lceil>P\<rceil> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(subst sH_g_ode_subset; clarsimp, (force)?)
  using init_time interval_time mem_is_interval_1_I by blast

lemma sH_orbit: "Hoare \<lceil>P\<rceil> (\<gamma>\<^sup>\<phi>\<^sup>\<bullet>) \<lceil>Q\<rceil> = (\<forall>s \<in> S. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  using sH_g_ode unfolding orbit_def g_ode_def by auto

end

\<comment> \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma sH_g_orbital_guard: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>R\<rceil>" 
  using assms unfolding g_orbital_eq ndfun_kat_H ivp_sols_def g_ode_def by auto

lemma sH_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in H_consl, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in H_consr, simp)
  using assms(2) by simp

lemma sH_diff_inv[simp]: "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq ndfun_kat_H g_orbital_eq g_ode_def by auto

lemma H_g_ode_inv: "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> 
  \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def apply(rule_tac q'="\<lceil>\<lambda>s. I s \<and> G s\<rceil>" in H_consr, simp)
  apply(subst sH_g_orbital_guard[symmetric], force)
  by (rule_tac I="I" in sH_g_orbital_inv, simp_all)


subsection \<open> Refinement Components \<close>

\<comment> \<open> Skip \<close>

lemma R_skip: "(\<forall>s. P s \<longrightarrow> Q s) \<Longrightarrow> 1 \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (auto simp: spec_def ndfun_kat_H one_nd_fun_def)

\<comment> \<open> Composition \<close>

lemma R_seq: "(Ref \<lceil>P\<rceil> \<lceil>R\<rceil>) ; (Ref \<lceil>R\<rceil> \<lceil>Q\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using R_seq by blast

lemma R_seq_rule: "X \<le> Ref \<lceil>P\<rceil> \<lceil>R\<rceil> \<Longrightarrow> Y \<le> Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> X; Y \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def by (rule H_seq)

lemmas R_seq_mono = mult_isol_var

\<comment> \<open> Assignment \<close>

lemma R_assign: "(x ::= e) \<le> Ref \<lceil>\<lambda>s. P (\<chi> j. ((($) s)(x := e s)) j)\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_assign, clarsimp simp: fun_eq_iff fun_upd_def)

lemma R_assign_rule: "(\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> (x ::= e) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_assign[symmetric] spec_def .

lemma R_assignl: "P = (\<lambda>s. R (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> (x ::= e) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_rule)
  by (rule_tac R_assign_rule, simp_all)

lemma R_assignr: "R = (\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> Ref \<lceil>P\<rceil> \<lceil>R\<rceil>; (x ::= e) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_rule, simp)
  by (rule_tac R_assign_rule, simp)

lemma "(x ::= e) ; Ref \<lceil>Q\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>(\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j))\<rceil> \<lceil>Q\<rceil>"
  by (rule R_assignl) simp

lemma "Ref \<lceil>Q\<rceil> \<lceil>(\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j))\<rceil>; (x ::= e) \<le> Ref \<lceil>Q\<rceil> \<lceil>Q\<rceil>"
  by (rule R_assignr) simp

\<comment> \<open> Conditional \<close>

lemma R_cond: "(IF B THEN Ref \<lceil>\<lambda>s. B s \<and> P s\<rceil> \<lceil>Q\<rceil> ELSE Ref \<lceil>\<lambda>s. \<not> B s \<and> P s\<rceil> \<lceil>Q\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using R_cond[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] by simp

lemma R_cond_mono: "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (IF P THEN X ELSE Y) \<le> IF P THEN X' ELSE Y'"
  unfolding kat_cond_def times_nd_fun_def plus_nd_fun_def n_op_nd_fun_def
  by (auto simp: kcomp_def less_eq_nd_fun_def p2ndf_def le_fun_def)

\<comment> \<open> While loop \<close>

lemma R_while: "WHILE Q INV I DO (Ref \<lceil>\<lambda>s. P s \<and> Q s\<rceil> \<lceil>P\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>\<lambda>s. P s \<and> \<not> Q s\<rceil>"
  unfolding kat_while_inv_def using R_while[of "\<lceil>Q\<rceil>" "\<lceil>P\<rceil>"] by simp

lemma R_while_mono: "X \<le> X' \<Longrightarrow> (WHILE P INV I DO X) \<le> WHILE P INV I DO X'"
  by (simp add: kat_while_inv_def kat_while_def mult_isol mult_isor star_iso)

\<comment> \<open> Finite loop \<close>

lemma R_loop: "X \<le> Ref \<lceil>I\<rceil> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP X INV I \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def using H_loopI by blast

lemma R_loop_mono: "X \<le> X' \<Longrightarrow> LOOP X INV I \<le> LOOP X' INV I"
  unfolding kat_loop_inv_def by (simp add: star_iso)

\<comment> \<open> Evolution command (flow) \<close>

lemma R_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "(EVOL \<phi> G U) \<le> Ref \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s)\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_g_evol, simp)

lemma R_g_evol_rule: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "(\<forall>s. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> (EVOL \<phi> G U) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_evol[symmetric] spec_def .

lemma R_g_evoll: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "P = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s)) \<Longrightarrow> 
  (EVOL \<phi> G U) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_rule)
  by (rule_tac R_g_evol_rule, simp_all)

lemma R_g_evolr: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "R = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)) \<Longrightarrow> 
  Ref \<lceil>P\<rceil> \<lceil>R\<rceil>; (EVOL \<phi> G U) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_rule, simp)
  by (rule_tac R_g_evol_rule, simp)

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "EVOL \<phi> G U ; Ref \<lceil>Q\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_evoll) simp

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "Ref \<lceil>Q\<rceil> \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>; EVOL \<phi> G U \<le> Ref \<lceil>Q\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_evolr) simp

\<comment> \<open> Evolution command (ode) \<close>

context local_flow
begin

lemma R_g_ode_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "(x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> Ref \<lceil>\<lambda>s. s\<in>S \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s))\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_g_ode_subset[OF assms], auto)

lemma R_g_ode_rule_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def by (subst sH_g_ode_subset[OF assms], auto)

lemma R_g_odel_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "P = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s))"
  shows "(x\<acute>= (\<lambda>t. f) & G on U S @ 0) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply (rule_tac R=R in R_seq_rule, rule_tac R_g_ode_rule_subset)
  by (simp_all add: assms)

lemma R_g_oder_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "R = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "Ref \<lceil>P\<rceil> \<lceil>R\<rceil>; (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply (rule_tac R=R in R_seq_rule, simp)
  by (rule_tac R_g_ode_rule_subset, simp_all add: assms)

lemma R_g_ode: "(x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> Ref \<lceil>\<lambda>s. s\<in>S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s))\<rceil> \<lceil>P\<rceil>"
  by (rule R_g_ode_subset, auto simp: init_time interval_time)

lemma R_g_ode_rule: "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode[symmetric] by (rule R2)

lemma R_g_odel: "P = (\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s)) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_odel_subset, auto simp: init_time interval_time)

lemma R_g_oder: "R = (\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)) \<Longrightarrow> 
  Ref \<lceil>P\<rceil> \<lceil>R\<rceil>; (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_oder_subset, auto simp: init_time interval_time)

lemma R_g_ode_ivl: 
  "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl[symmetric] by (rule R2)

end

\<comment> \<open> Evolution command (invariants) \<close>

lemma R_g_ode_inv: "diff_invariant I f T S t\<^sub>0 G \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  (x\<acute>=f & G on T S @ t\<^sub>0 DINV I) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def by (auto simp: H_g_ode_inv)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive a generalised version of some domain specific rules of differential dynamic logic (dL).\<close>

abbreviation g_dl_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_rule1:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.sH_g_ode_subset, auto)

lemma diff_solve_rule2: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (s + t *\<^sub>R c))"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil>"
  apply(subst local_flow.sH_g_ode_subset[where T=UNIV and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms unfolding g_orbital_eq ndfun_kat_H ivp_sols_def g_ode_def by auto

lemma diff_cut_rule:
  assumes wp_C:"Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"Hoare \<lceil>P\<rceil> (x\<acute>= f & (\<lambda> s. G s \<and> C s) on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst ndfun_kat_H, simp add: g_orbital_eq p2ndf_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s
  assume "P s" and "t \<in> U s"
    and x_ivp:"X \<in> ivp_sols f U S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> U s \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down (U s) t). X t \<in> g_orbital f G U S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down (U s) t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) ndfun_kat_H, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) U S t\<^sub>0 s"
    using guard_x \<open>t \<in> U s\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) ndfun_kat_H) (auto simp: g_ode_def)
qed

lemma diff_inv_rule:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f U S t\<^sub>0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  apply(subst g_ode_inv_def[symmetric, where I=I], rule H_g_ode_inv)
  unfolding sH_diff_inv using assms by auto

end