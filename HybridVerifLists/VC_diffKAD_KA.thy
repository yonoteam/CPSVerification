(*  Title:       Verification components with Kleene Algebras
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with Kleene Algebras \<close>

text \<open> We create verification rules based on various Kleene Algebras. \<close>

theory VC_diffKAD_KA
  imports
  KAT_and_DRA.PHL_KAT
  "KAD.Modal_Kleene_Algebra"
  "Transformer_Semantics.Kleisli_Quantale"

begin

subsection \<open> Hoare logic and refinement in KAT \<close> 

text \<open> Here we derive the rules of Hoare Logic and a refinement calculus in 
Kleene algebra with tests. \<close>

notation t ("\<tt>\<tt>")

hide_const t

no_notation ars_r ("r")
        and if_then_else ("if _ then _ else _ fi" [64,64,64] 63)
        and while ("while _ do _ od" [64,64] 63)

context kat (* mostly by Victor Gomes, Georg Struth *)
begin
 
\<comment> \<open> Definitions of Hoare Triple \<close>

definition Hoare :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("H") where
  "H p x q \<longleftrightarrow> \<tt>\<tt> p \<cdot> x \<le> x \<cdot> \<tt>\<tt> q" 

lemma H_consl: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> H p' x q \<Longrightarrow> H p x q"
  using Hoare_def phl_cons1 by blast

lemma H_consr: "\<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> H p x q' \<Longrightarrow> H p x q"
  using Hoare_def phl_cons2 by blast         

lemma H_cons: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> \<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (simp add: H_consl H_consr)

\<comment> \<open> Skip program \<close>

lemma H_skip:  "H p 1 p"
  by (simp add: Hoare_def)

\<comment> \<open> Sequential composition \<close>

lemma H_seq: "H p x r \<Longrightarrow> H r y q \<Longrightarrow> H p (x \<cdot> y) q"
  by (simp add: Hoare_def phl_seq)

\<comment> \<open> Conditional statement \<close>

definition kat_cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = (\<tt>\<tt> p \<cdot> x + n p \<cdot> y)"

lemma H_var: "H p x q \<longleftrightarrow> \<tt>\<tt> p \<cdot> x \<cdot> n q = 0"
  by (metis Hoare_def n_kat_3 t_n_closed)

lemma H_cond_iff: "H p (if r then x else y fi) q \<longleftrightarrow> H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<and> H (\<tt>\<tt> p \<cdot> n r) y q"
proof -
  have "H p (if r then x else y fi) q \<longleftrightarrow> \<tt>\<tt> p \<cdot> (\<tt>\<tt> r \<cdot> x + n r \<cdot> y) \<cdot> n q = 0"
    by (simp add: H_var kat_cond_def)
  also have "... \<longleftrightarrow> \<tt>\<tt> p \<cdot> \<tt>\<tt> r \<cdot> x \<cdot> n q + \<tt>\<tt> p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (simp add: distrib_left mult_assoc)
  also have "... \<longleftrightarrow> \<tt>\<tt> p \<cdot> \<tt>\<tt> r \<cdot> x \<cdot> n q = 0 \<and> \<tt>\<tt> p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (metis add_0_left no_trivial_inverse)
  finally show ?thesis
    by (metis H_var test_mult)
qed

lemma H_cond: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<Longrightarrow> H (\<tt>\<tt> p \<cdot> n r) y q \<Longrightarrow> H p (if r then x else y fi) q"
  by (simp add: H_cond_iff)

\<comment> \<open> While loop \<close>

definition kat_while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while b do x od = (\<tt>\<tt> b \<cdot> x)\<^sup>\<star> \<cdot> n b"

definition kat_while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma H_exp1: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<Longrightarrow> H p (\<tt>\<tt> r \<cdot> x) q"
  using Hoare_def n_de_morgan_var2 phl.ht_at_phl_export1 by auto

lemma H_while: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x p \<Longrightarrow> H p (while r do x od) (\<tt>\<tt> p \<cdot> n r)"
proof -
  assume a1: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x p"
  have "\<tt>\<tt> (\<tt>\<tt> p \<cdot> n r) = n r \<cdot> \<tt>\<tt> p \<cdot> n r"
    using n_preserve test_mult by presburger
  then show ?thesis
    using a1 Hoare_def H_exp1 conway.phl.it_simr phl_export2 kat_while_def by auto
qed

lemma H_while_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<cdot> n r \<le> \<tt>\<tt> q \<Longrightarrow> H (\<tt>\<tt> i \<cdot> \<tt>\<tt> r) x i \<Longrightarrow> H p (while r inv i do x od) q"
  by (metis H_cons H_while test_mult kat_while_inv_def)

\<comment> \<open> Finite iteration \<close>

lemma H_star: "H i x i \<Longrightarrow> H i (x\<^sup>\<star>) i"
  unfolding Hoare_def using star_sim2 by blast

lemma H_star_inv: 
  assumes "\<tt>\<tt> p \<le> \<tt>\<tt> i" and "H i x i" and "(\<tt>\<tt> i) \<le> (\<tt>\<tt> q)"
  shows "H p (x\<^sup>\<star>) q"
proof-
  have "H i (x\<^sup>\<star>) i"
    using assms(2) H_star by blast
  hence "H p (x\<^sup>\<star>) i"
    unfolding Hoare_def using assms(1) phl_cons1 by blast
  thus ?thesis 
    unfolding Hoare_def using assms(3) phl_cons2 by blast
qed

definition kat_loop_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma H_loop: "H p x p \<Longrightarrow> H p (loop x inv i) p"
  unfolding kat_loop_inv_def by (rule H_star)

lemma H_loop_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> H i x i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> H p (loop x inv i) q"
  unfolding kat_loop_inv_def using H_star_inv by blast

\<comment> \<open> Invariants \<close>

lemma H_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> H i x i \<Longrightarrow> H p x q"
  by (rule_tac p'=i and q'=i in H_cons)

lemma H_inv_plus: "\<tt>\<tt> i = i \<Longrightarrow> \<tt>\<tt> j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i + j) x (i + j)"
  unfolding Hoare_def using combine_common_factor
  by (smt add_commute add.left_commute distrib_left join.sup.absorb_iff1 t_add_closed)

lemma H_inv_mult: "\<tt>\<tt> i = i \<Longrightarrow> \<tt>\<tt> j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i \<cdot> j) x (i \<cdot> j)"
  unfolding Hoare_def by (smt n_kat_2 n_mult_comm t_mult_closure mult_assoc)

end


subsection \<open> refinement KAT \<close> 

class rkat = kat +
  fixes Ref :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "x \<le> Ref p q \<longleftrightarrow> H p x q"

begin (* mostly by Victor Gomes, Georg Struth *)

lemma R1: "H p (Ref p q) q"
  using spec_def by blast

lemma R2: "H p x q \<Longrightarrow> x \<le> Ref p q"
  by (simp add: spec_def)

lemma R_cons: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> \<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> Ref p' q' \<le> Ref p q"
proof -
  assume h1: "\<tt>\<tt> p \<le> \<tt>\<tt> p'" and h2: "\<tt>\<tt> q' \<le> \<tt>\<tt> q"
  have "H p' (Ref p' q') q'"
    by (simp add: R1)
  hence "H p (Ref p' q') q"
    using h1 h2 H_consl H_consr by blast
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Abort and skip programs \<close>

lemma R_skip: "1 \<le> Ref p p"
proof -
  have "H p 1 p"
    by (simp add: H_skip)
  thus ?thesis
    by (rule R2)
qed

lemma R_zero_one: "x \<le> Ref 0 1"
proof -
  have "H 0 x 1"
    by (simp add: Hoare_def)
  thus ?thesis
    by (rule R2)
qed

lemma R_one_zero: "Ref 1 0 = 0"
proof -
  have "H 1 (Ref 1 0) 0"
    by (simp add: R1)
  thus ?thesis
    by (simp add: Hoare_def join.le_bot)
qed

\<comment> \<open> Sequential composition \<close>

lemma R_seq: "(Ref p r) \<cdot> (Ref r q) \<le> Ref p q"
proof -
  have "H p (Ref p r) r" and "H r (Ref r q) q"
    by (simp add: R1)+
  hence "H p ((Ref p r) \<cdot> (Ref r q)) q"
    by (rule H_seq)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Conditional statement \<close>

lemma R_cond: "if v then (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) else (Ref (n v \<cdot> \<tt>\<tt> p) q) fi \<le> Ref p q"
proof - 
  have "H (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) q" and "H (n v \<cdot> \<tt>\<tt> p) (Ref (n v \<cdot> \<tt>\<tt> p) q) q"
    by (simp add: R1)+
  hence "H p (if v then (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) else (Ref (n v \<cdot> \<tt>\<tt> p) q) fi) q"
    by (simp add: H_cond n_mult_comm)
 thus ?thesis
    by (rule R2)
qed

\<comment> \<open> While loop \<close>

lemma R_while: "while q do (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p) od \<le> Ref p (\<tt>\<tt> p \<cdot> n q)"
proof -
  have "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p)  p" 
    by (simp_all add: R1)
  hence "H p (while q do (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p) od) (\<tt>\<tt> p \<cdot> n q)"
    by (simp add: H_while)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Finite iteration \<close>

lemma R_star: "(Ref i i)\<^sup>\<star> \<le> Ref i i"
proof -
  have "H i (Ref i i) i"
    using R1 by blast
  hence "H i ((Ref i i)\<^sup>\<star>) i"
    using H_star by blast
  thus "Ref i i\<^sup>\<star> \<le> Ref i i"
    by (rule R2)
qed

lemma R_loop: "loop (Ref p p) inv i \<le> Ref p p"
  unfolding kat_loop_inv_def by (rule R_star)

\<comment> \<open> Invariants \<close>

lemma R_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> Ref i i \<le> Ref p q"
  using R_cons by force

end

no_notation kat_cond ("if _ then _ else _ fi" [64,64,64] 63)
        and kat_while ("while _ do _ od" [64,64] 63)
        and kat_while_inv ("while _ inv _ do _ od" [64,64,64] 63)
        and kat_loop_inv ("loop _ inv _ " [64,64] 63) 

subsection \<open> Verification in AKA (KAD) \<close>

text \<open>Here we derive verification components with weakest liberal preconditions based on 
antidomain Kleene algebra (or Kleene algebra with domain) \<close>

context antidomain_kleene_algebra
begin

\<comment> \<open> Sequential composition \<close>

declare fbox_mult [simp]

\<comment> \<open> Conditional statement \<close>

definition aka_cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) 
  where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure addual.ars_r_def fbox_def fbox_mult by auto

lemma fbox_cond [simp]: "|if p then x else y fi] q = (ad p + |x] q) \<cdot> (d p + |y] q)"  
  using aka_cond_def a_closure' ads_d_def ans_d_def fbox_add2 fbox_export1 by auto

\<comment> \<open> Finite iteration \<close>

definition aka_loop_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma fbox_stari: "d p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |x\<^sup>\<star>] q"
  by (meson dual_order.trans fbox_iso fbox_star_induct_var)

lemma fbox_loopi: "d p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> d p \<le> |loop x inv i] q"
  unfolding aka_loop_inv_def using fbox_stari by blast

\<comment> \<open> Invariants \<close>

lemma fbox_frame: "d p \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d q \<le> |x] r \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d r)"    
  using dual.mult_isol_var fbox_add1 fbox_demodalisation3 fbox_simp by auto

lemma plus_inv: "i \<le> |x] i \<Longrightarrow> j \<le> |x] j \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  by (metis ads_d_def dka.dsr5 fbox_simp fbox_subdist join.sup_mono order_trans)

lemma mult_inv: "d i \<le> |x] d i \<Longrightarrow> d j \<le> |x] d j \<Longrightarrow> (d i \<cdot> d j) \<le> |x] (d i \<cdot> d j)"
  using fbox_demodalisation3 fbox_frame fbox_simp by auto

end


subsection \<open> Relational model \<close>

text \<open>We show that relations form Kleene Algebras (KAT and AKA). \<close>

interpretation rel_uq: unital_quantale Id "(O)" "\<Inter>" "\<Union>" "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" UNIV
  by (unfold_locales, auto)

lemma power_is_relpow: "rel_uq.power X m = X ^^ m" for X::"'a rel"
proof (induct m)
  case 0 show ?case
    by (metis rel_uq.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_uq.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>m. rel_uq.power X m)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>m. X O rel_uq.power Y m)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>m. (rel_uq.power X m) O Y)"
  by (metis rel_star_def relcomp_UNION_distrib2)
         
interpretation rel_ka: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_uq.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_uq.power_inductr)
qed

interpretation rel_tests: test_semiring "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" "\<lambda>x. Id \<inter> ( - x)"
  by (standard, auto)

interpretation rel_kat: kat "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "\<lambda>x. Id \<inter> ( - x)"
  by (unfold_locales)

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.Hoare P X Q}"

interpretation rel_rkat: rkat "(\<union>)" "(;)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.Hoare_def)

lemma RdL_is_rRKAT: "(\<forall>x. {(x,x)}; R1 \<subseteq> {(x,x)}; R2) = (R1 \<subseteq> R2)" (* Refinement in dL is that of rKAT *)
  by auto

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ad R = {(x,x) | x. \<not> (\<exists>y. (x,y) \<in> R)}"

interpretation rel_aka: antidomain_kleene_algebra rel_ad "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
  by  unfold_locales (auto simp: rel_ad_def)


subsection \<open> State transformer model \<close>

text \<open>We show that state transformers form Kleene Algebras (KAT and AKA). \<close>

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

declare Abs_nd_fun_inverse [simp]

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

instantiation nd_fun :: (type) antidomain_kleene_algebra
begin

definition "ad f = (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>"

lemma nd_fun_ad_zero[nd_fun_aka]: "ad x \<cdot> x = 0"
  and nd_fun_ad[nd_fun_aka]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and nd_fun_ad_one[nd_fun_aka]: "ad (ad x) + ad x = 1" for x::"'a nd_fun"
  unfolding antidomain_op_nd_fun_def times_nd_fun_def plus_nd_fun_def zero_nd_fun_def 
  by (auto simp: nd_fun_eq_iff kcomp_def one_nd_fun_def)

instance
  apply intro_classes
  using nd_fun_aka by simp_all

end

end