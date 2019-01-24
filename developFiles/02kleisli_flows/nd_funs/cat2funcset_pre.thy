theory cat2funcset_pre
  imports "Ordinary_Differential_Equations.Initial_Value_Problem" flow_locales
"Transformer_Semantics.Kleisli_Quantale" "KAD.Modal_Kleene_Algebra"
                        
begin

section {* Preliminaries *}

text{* This file presents a miscellaneous collection of preliminary lemmas for verification of 
Hybrid Systems in Isabelle.*}

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Isotone_Transformers.bqtran ("\<lfloor>_\<rfloor>")

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)
type_synonym 'a pred = "'a \<Rightarrow> bool"

subsection{* Nondeterministic Functions *}

lemma Abs_nd_fun_inverse2[simp]:"(f\<^sup>\<bullet>)\<^sub>\<bullet> = f"
  by(simp add: Abs_nd_fun_inverse)

lemma nd_fun_ext:"(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
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

lemma nd_fun_assoc[nd_fun_aka]:"(a::'a nd_fun) + b + c = a + (b + c)"
  by(transfer, simp add: ksup_assoc)

lemma nd_fun_comm[nd_fun_aka]:"(a::'a nd_fun) + b = b + a"
  by(transfer, simp add: ksup_comm)

lemma nd_fun_distr[nd_fun_aka]:"((x::'a nd_fun) + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_aka]:"x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  by(transfer, simp add: kcomp_distr, transfer, simp add: kcomp_distl)

lemma nd_fun_zero_sum[nd_fun_aka]:"0 + (x::'a nd_fun) = x" 
  and nd_fun_zero_dot[nd_fun_aka]:"0 \<cdot> x = 0"
  by(transfer, simp, transfer, auto) 

lemma nd_fun_leq[nd_fun_aka]:"((x::'a nd_fun) \<le> y) = (x + y = y)"
  and nd_fun_leq_add[nd_fun_aka]:" z \<cdot> x \<le> z \<cdot> (x + y)"
   apply(transfer, metis Abs_nd_fun_inverse2 Rep_nd_fun_inverse le_iff_sup)
  by(transfer, simp add: kcomp_isol)

lemma nd_fun_ad_zero[nd_fun_aka]: "ad (x::'a nd_fun) \<cdot> x = 0"
  and nd_fun_ad[nd_fun_aka]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and nd_fun_ad_one[nd_fun_aka]: "ad (ad x) + ad x = 1"
   apply(transfer, rule nd_fun_ext, simp add: kcomp_def)
   apply(transfer, rule nd_fun_ext, simp, simp add: kcomp_def)
  by(transfer, simp, rule nd_fun_ext, simp add: kcomp_def)

lemma nd_star_one[nd_fun_aka]:"1 + (x::'a nd_fun) \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_aka]:"z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_aka]:"z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
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

subsection{* Weakest Liberal Preconditions *}

abbreviation p2ndf :: "'a pred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> Q s})\<^sup>\<bullet>"

lemma le_p2ndf_iff[simp]:"\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  by(transfer, auto simp: le_fun_def)

abbreviation ndf2p :: "'a nd_fun \<Rightarrow> 'a \<Rightarrow> bool" ("(1\<lfloor>_\<rfloor>)")
  where "\<lfloor>f\<rfloor> \<equiv> (\<lambda>x. x \<in> Domain (\<R> (f\<^sub>\<bullet>)))"

lemma p2ndf_ndf2p_id:"F \<le> \<eta>\<^sup>\<bullet> \<Longrightarrow> \<lceil>\<lfloor>F\<rfloor>\<rceil> = F"
  unfolding f2r_def apply(rule nd_fun_ext)
  apply(subgoal_tac "\<forall>x. (F\<^sub>\<bullet>) x \<subseteq> {x}", simp)
  by(blast, simp add: le_fun_def less_eq_nd_fun.rep_eq)

abbreviation "wp f \<equiv> fbox (f::'a nd_fun)"

lemma wp_nd_fun:"wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. y \<in> (F x) \<longrightarrow> P y\<rceil>"
  apply(simp add: fbox_def, transfer, simp)
  by(rule nd_fun_ext, auto simp: kcomp_def)

lemma wp_nd_fun_etaD:"wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = \<eta>\<^sup>\<bullet> \<Longrightarrow>  (\<forall>y. y \<in> (F x) \<longrightarrow> P y)"
proof
  fix y assume "wp (F\<^sup>\<bullet>) \<lceil>P\<rceil> = (\<eta>\<^sup>\<bullet>)"
  from this have "\<eta>\<^sup>\<bullet> = \<lceil>\<lambda>s. \<forall>y. s2p (F s) y \<longrightarrow> P y\<rceil>" 
    by(subst wp_nd_fun[THEN sym], simp)
  hence "\<And>x. {x} = {s. s = x \<and> (\<forall>y. s2p (F s) y \<longrightarrow> P y)}"
    apply(subst (asm) Abs_nd_fun_inject, simp_all)
    by(drule_tac x="x" in fun_cong, simp)
  then show "s2p (F x) y \<longrightarrow> P y" by auto
qed

lemma p2ndf_ndf2p_wp:"\<lceil>\<lfloor>wp R P\<rfloor>\<rceil> = wp R P"
  apply(rule p2ndf_ndf2p_id)
  by (simp add: a_subid fbox_def one_nd_fun.transfer) 

lemma p2ndf_ndf2p_wp_sym:"wp R P = \<lceil>\<lfloor>wp R P\<rfloor>\<rceil>"
  by(rule sym, simp add: p2ndf_ndf2p_wp)

lemma wp_trafo: "\<lfloor>wp F \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. \<forall>s'. s' \<in> (F\<^sub>\<bullet>) s \<longrightarrow> Q s')"  
  apply(subgoal_tac "F = (F\<^sub>\<bullet>)\<^sup>\<bullet>")
  apply(rule ssubst[of F "(F\<^sub>\<bullet>)\<^sup>\<bullet>"], simp)
  apply(subst wp_nd_fun)
  by(simp_all add: f2r_def)

abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) where 
"x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2[_ ::== _])" [70, 65] 61) where 
"[x ::== expr]\<equiv> (\<lambda>s. {s[x :== expr s]})\<^sup>\<bullet>" 

lemma wp_assign[simp]: "wp ([x ::== expr]) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s[x :== expr s])\<rceil>"
  by(subst wp_nd_fun, rule nd_fun_ext, simp)

lemma fbox_seq [simp]: "|x \<cdot> y] q = |x] |y] q"
  by (simp add: fbox_mult) 

definition (in antidomain_kleene_algebra) cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
("if _ then _ else _ fi" [64,64,64] 63) where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" 
("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> cond \<lceil>P\<rceil> X Y"

lemma (in antidomain_kleene_algebra) fbox_starI: 
assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
shows "d p \<le> |x\<^sup>\<star>] q"
  by (meson assms local.dual_order.trans local.fbox_iso local.fbox_star_induct_var)

lemma bot_pres_del:"bot_pres (If (\<not> Q x) (\<eta> x)) \<Longrightarrow> Q x"
  using empty_not_insert by fastforce thm empty_not_insert

lemma nd_fun_ads_d_def:"d (f::'a nd_fun) = (\<lambda>x. if (f\<^sub>\<bullet>) x = {} then {} else \<eta> x )\<^sup>\<bullet>"
  unfolding ads_d_def apply(rule nd_fun_ext, simp)
  apply transfer by auto

lemma ads_d_mono: "x \<le> y \<Longrightarrow> d x \<le> d y"
  by (metis ads_d_def fbox_antitone_var fbox_dom)

lemma nd_fun_top_ads_d:"(x::'a nd_fun) \<le> 1 \<Longrightarrow> d x = x"
  apply(simp add: ads_d_def, transfer, simp)
  apply(rule nd_fun_ext, simp)
  apply(subst (asm) le_fun_def)
  by auto

lemma rel_ad_mka_starI:
assumes "P \<le> I" and "I \<le> wp F I" and "I \<le> Q"
shows "P \<le> wp (qstar F) Q"
proof-
  from assms(1,2) have "P \<le> 1"
    by (metis a_subid basic_trans_rules(23) fbox_def) 
  hence "d P = P" using nd_fun_top_ads_d by blast
  have "\<And> x y. d (wp x y) = wp x y"
    by(metis ds.ddual.mult_oner fbox_mult fbox_one)
  from this and assms have "d P \<le> d I \<and> d I \<le> wp F I \<and> d I \<le> d Q"
    by (metis (no_types) ads_d_mono assms)
  hence "d P \<le> wp (F\<^sup>\<star>) Q"
    by(simp add: fbox_starI[of _ I])
  then show "P \<le> wp (qstar F) Q"
    using \<open>d P = P\<close> by (transfer, simp)
qed

subsection{* Real Numbers and Derivatives *}

lemma case_of_fst[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f t) = (\<lambda> x. (f \<circ> fst) x)"
  by auto

lemma case_of_snd[simp]:"(\<lambda>x. case x of (t, x) \<Rightarrow> f x) = (\<lambda> x. (f \<circ> snd) x)"
  by auto

lemma sqrt_le_itself: "1 \<le> x \<Longrightarrow> sqrt x \<le> x"
  by (metis basic_trans_rules(23) monoid_mult_class.power2_eq_square more_arith_simps(6) 
      mult_left_mono real_sqrt_le_iff' zero_le_one)

lemma sqrt_real_nat_le:"sqrt (real n) \<le> real n"
  by (metis (full_types) abs_of_nat le_square of_nat_mono of_nat_mult real_sqrt_abs2 real_sqrt_le_iff)

lemma closed_segment_mvt:
  fixes f :: "real \<Rightarrow> real"
  assumes "(\<And>r. r\<in>{a--b} \<Longrightarrow> (f has_derivative f' r) (at r within {a--b}))" and "a \<le> b"
  shows "\<exists>r\<in>{a--b}. f b - f a = f' r (b - a)"
  using assms closed_segment_eq_real_ivl and mvt_very_simple by auto

lemma convergences_solves_vec_nth:
  assumes "((\<lambda>y. (\<phi> y - \<phi> (netlimit (at x within {0..t})) - (y - netlimit (at x within {0..t})) *\<^sub>R f (\<phi> x)) /\<^sub>R
\<bar>y - netlimit (at x within {0..t})\<bar>) \<longlongrightarrow> 0) (at x within {0..t})" (is "((\<lambda>y. ?f y) \<longlongrightarrow> 0) ?net")
  shows "((\<lambda>y. (\<phi> y $ i - \<phi> (netlimit (at x within {0..t})) $ i - (y - netlimit (at x within {0..t})) *\<^sub>R f (\<phi> x) $ i) /\<^sub>R
\<bar>y - netlimit (at x within {0..t})\<bar>) \<longlongrightarrow> 0) (at x within {0..t})" (is "((\<lambda>y. ?g y i) \<longlongrightarrow> 0) ?net")
proof-
  from assms have  "((\<lambda>y. ?f y $ i) \<longlongrightarrow> 0 $ i) ?net" by(rule tendsto_vec_nth)
  also have "(\<lambda>y. ?f y $ i) = (\<lambda>y. ?g y i)" by auto
  ultimately show "((\<lambda>y. ?g y i) \<longlongrightarrow> 0) ?net" by auto
qed

lemma solves_vec_nth:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)"
  assumes "(\<phi> solves_ode (\<lambda> t. f)) {0..t} UNIV"
  shows "((\<lambda> t. (\<phi> t) $ i) solves_ode (\<lambda> t s. (f (\<phi> t)) $ i)) {0..t} UNIV"
  using assms unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def has_derivative_def 
  apply safe apply(auto simp: bounded_linear_def bounded_linear_axioms_def)[1]
   apply(erule_tac x="x" in ballE, clarsimp)
  apply(rule convergences_solves_vec_nth)
  by(simp_all add: Pi_def)

lemma solves_vec_lambda:
  fixes f::"(('a::banach)^('n::finite)) \<Rightarrow> ('a^'n)" and \<phi>::"real \<Rightarrow> ('a^'n)"
  assumes "\<forall> i::'n. ((\<lambda> t. (\<phi> t) $ i) solves_ode (\<lambda> t s. (f (\<phi> t)) $ i)) {0..t} UNIV"
  shows "(\<phi> solves_ode (\<lambda> t. f)) {0..t} UNIV"
  using assms unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def has_derivative_def 
  apply safe apply(auto simp: bounded_linear_def bounded_linear_axioms_def)[1]
  by(rule Finite_Cartesian_Product.vec_tendstoI, simp_all)

named_theorems poly_derivatives "compilation of derivatives for kinematics and polynomials."

declare has_vderiv_on_const [poly_derivatives]

lemma origin_line_vector_derivative:"((\<cdot>) a has_vector_derivative a) (at x within T)"
  by (auto intro: derivative_eq_intros)

lemma origin_line_derivative:"((\<cdot>) a has_derivative (\<lambda>x. x *\<^sub>R a)) (at x within T)"
  using origin_line_vector_derivative unfolding has_vector_derivative_def by simp

lemma quadratic_monomial_derivative:
"((\<lambda>t::real. a \<cdot> t\<^sup>2) has_derivative (\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t))) (at x within T)"
  apply(rule_tac g'1="\<lambda> t. 2 \<cdot> x \<cdot> t" in derivative_eq_intros(6))
   apply(rule_tac f'1="\<lambda> t. t" in derivative_eq_intros(15))
  by (auto intro: derivative_eq_intros) 

lemma quadratic_monomial_derivative_div:
"((\<lambda>t::real. a \<cdot> t\<^sup>2 / 2) has_derivative (\<lambda>t. a \<cdot> x \<cdot> t)) (at x within T)"
  apply(rule_tac f'1="\<lambda>t. a \<cdot> (2 \<cdot> x \<cdot> t)" and g'1="\<lambda> x. 0" in derivative_eq_intros(18))
  using quadratic_monomial_derivative by auto

lemma quadratic_monomial_vderiv[poly_derivatives]:"((\<lambda>t. a \<cdot> t\<^sup>2 / 2) has_vderiv_on (\<cdot>) a) T"
  apply(simp add: has_vderiv_on_def has_vector_derivative_def, clarify)
  using quadratic_monomial_derivative_div by (simp add: mult_commute_abs)

lemma pos_vderiv[poly_derivatives]:
"((\<lambda>t. a \<cdot> t\<^sup>2 / 2 + v \<cdot> t + x) has_vderiv_on (\<lambda>t. a \<cdot> t + v)) T"
  apply(rule_tac f'="\<lambda> x. a \<cdot> x + v" and g'1="\<lambda> x. 0" in derivative_intros(190))
    apply(rule_tac f'1="\<lambda> x. a \<cdot> x" and g'1="\<lambda> x. v" in derivative_intros(190))
  using poly_derivatives(2) by(auto intro: derivative_intros)

lemma pos_derivative:
"t \<in> T \<Longrightarrow> ((\<lambda>\<tau>. a \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + x) has_derivative (\<lambda>x. x *\<^sub>R (a \<cdot> t + v))) (at t within T)"
  using pos_vderiv unfolding has_vderiv_on_def has_vector_derivative_def by simp

lemma vel_vderiv[poly_derivatives]:"((\<lambda>r. a \<cdot> r + v) has_vderiv_on (\<lambda>t. a)) T"
  apply(rule_tac f'1="\<lambda> x. a" and g'1="\<lambda> x. 0" in derivative_intros(190))
  unfolding has_vderiv_on_def by(auto intro: derivative_eq_intros)

lemma pos_vderiv_minus[poly_derivatives]:
"((\<lambda>t. v \<cdot> t - a \<cdot> t\<^sup>2 / 2 + x) has_vderiv_on (\<lambda>x. v - a \<cdot> x)) {0..t}"
  apply(subgoal_tac "((\<lambda>t. - a \<cdot> t\<^sup>2 / 2 + v \<cdot> t  +x) has_vderiv_on (\<lambda>x. - a \<cdot> x + v)) {0..t}", simp)
  by(rule poly_derivatives)

lemma vel_vderiv_minus[poly_derivatives]:
"((\<lambda>t. v - a \<cdot> t) has_vderiv_on (\<lambda>x. - a)) {0..t}"
  apply(subgoal_tac "((\<lambda>t. - a \<cdot> t + v) has_vderiv_on (\<lambda>x. - a)) {0..t}", simp)
  by(rule poly_derivatives)

declare origin_line_vector_derivative [poly_derivatives]
    and origin_line_derivative [poly_derivatives]
    and quadratic_monomial_derivative [poly_derivatives]
    and quadratic_monomial_derivative_div [poly_derivatives]
    and pos_derivative [poly_derivatives]

subsection{* Vectors, norms and matrices. *}

subsubsection{* Unit vectors and vector norm *}

lemma norm_scalar_mult: "norm ((c::real) *s x) = \<bar>c\<bar> \<cdot> norm x"
  unfolding norm_vec_def L2_set_def real_norm_def vector_scalar_mult_def apply simp
  apply(subgoal_tac "(\<Sum>i\<in>UNIV. (c \<cdot> x $ i)\<^sup>2) = \<bar>c\<bar>\<^sup>2 \<cdot> (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2) ")
   apply(simp add: real_sqrt_mult)
  apply(simp add: sum_distrib_left)
  by (meson power_mult_distrib)

lemma squared_norm_vec:"(norm x)\<^sup>2 = (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
  unfolding norm_vec_def L2_set_def by (simp add: sum_nonneg)

lemma sgn_is_unit_vec:"sgn x = 1 / norm x *s x"
  unfolding sgn_vec_def scaleR_vec_def by(simp add: vector_scalar_mult_def divide_inverse_commute)

lemma norm_sgn_unit:"(x::real^'n) \<noteq> 0 \<Longrightarrow> norm (sgn x) = 1"
proof(subst sgn_is_unit_vec, unfold norm_vec_def L2_set_def, simp add: power_divide)
  assume "x \<noteq> 0"
  have "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2 / (norm x)\<^sup>2) = 1 / (norm x)\<^sup>2 \<cdot> (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2)"
    by (simp add: sum_divide_distrib)
  also have "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2) = (norm x)\<^sup>2" by(subst squared_norm_vec, simp)
  ultimately show "(\<Sum>i\<in>UNIV. (x $ i)\<^sup>2 / (sqrt (\<Sum>i\<in>UNIV. (x $ i)\<^sup>2))\<^sup>2) = 1"
    using \<open>x \<noteq> 0\<close> by simp
qed

lemma norm_matrix_sgn:"norm (A *v (x::real^'n)) = norm (A *v (sgn x)) \<cdot> norm x"
  unfolding sgn_is_unit_vec vector_scalar_commute norm_scalar_mult by simp 

lemma vector_norm_distr_minus:
  fixes A::"('a::{real_normed_vector, ring_1})^'n^'m"
  shows "norm (A *v x - A *v y) = norm (A *v (x - y))"
  by(subst matrix_vector_mult_diff_distrib, simp)

subsubsection{* Matrix norm *}

abbreviation "norm\<^sub>S (A::real^'n^'m) \<equiv> Sup {norm (A *v x) | x. norm x = 1}"

lemma unit_norms_bound:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "norm x = 1 \<Longrightarrow> norm (A *v x) \<le> norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)"
proof-
  assume "norm x = 1"
  from this have "\<And> j. \<bar>x $ j\<bar> \<le> 1"
    by (metis component_le_norm_cart)
  then have "\<And>i j. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar> \<le> \<bar>A $ i $ j\<bar> \<cdot> 1"
    using mult_left_mono by (simp add: mult_left_le) 
  from this have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar>)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    by (simp add: power_mono sum_mono sum_nonneg)
  also have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j \<cdot> x $ j\<bar>)\<^sup>2"
    using abs_le_square_iff by force 
  moreover have "\<And>i.(\<Sum>j\<in>UNIV. \<bar>A $ i $ j \<cdot> x $ j\<bar>)\<^sup>2 = (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> \<cdot> \<bar>x $ j\<bar>)\<^sup>2"
    by (simp add: abs_mult)
  ultimately have "\<And>i.(\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
    using order_trans by fastforce
  hence "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2) \<le> (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2)"
    by(simp add: sum_mono)
  then have "(sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j \<cdot> x $ j)\<^sup>2)) \<le> (sqrt (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2))"
    using real_sqrt_le_mono by blast
  thus "norm (A *v x) \<le> norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)"
    by(simp add: norm_vec_def L2_set_def matrix_vector_mult_def)
qed

lemma unit_norms_exists:
  fixes A::"real^('n::finite)^('m::finite)"
  shows bounded:"bounded {norm (A *v x) | x. norm x = 1}"
    and bdd_above:"bdd_above {norm (A *v x) | x. norm x = 1}"
    and non_empty:"{norm (A *v x) | x. norm x = 1} \<noteq> {}" (is "?U \<noteq> {}")
proof-
  show "bounded ?U"
    apply(unfold bounded_def,rule_tac x="0" in exI, simp add: dist_real_def)
    apply(rule_tac x="norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)" in exI, clarsimp)
    using unit_norms_bound by blast
next
  show "bdd_above ?U"
    apply(unfold bdd_above_def, rule_tac x="norm ((\<chi> i j. \<bar>A $ i $ j\<bar>) *v 1)" in exI, clarsimp)
    using unit_norms_bound by blast
next
  have "\<And>k::'n. norm (axis k (1::real)) = 1"
    using norm_axis_1 by blast
  hence "\<And>k::'n. norm ((A::real^('n::finite)^'m) *v (axis k (1::real))) \<in> ?U"
    by blast
  thus "?U \<noteq> {}" by blast
qed

lemma unit_norms: "norm x = 1 \<Longrightarrow> norm (A *v x) \<le> norm\<^sub>S A"
  using cSup_upper mem_Collect_eq unit_norms_exists(2) by (metis (mono_tags, lifting)) 

lemma unit_norms_ge_0:"0 \<le> norm\<^sub>S A"
  using ex_norm_eq_1 norm_ge_zero unit_norms basic_trans_rules(23) by blast

lemma norm_sgn_le_norms:"norm (A *v sgn x) \<le> norm\<^sub>S A"
  apply(cases "x=0")
  using sgn_zero unit_norms_ge_0 apply force
  using norm_sgn_unit unit_norms by blast

abbreviation "entries (A::real^'n^'m) \<equiv> {A $ i $ j | i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}"
abbreviation "maxAbs (A::real^'n^'m) \<equiv> Max (abs ` (entries A))"

lemma maxAbs_def:"maxAbs (A::real^'n^'m) = Max { \<bar>A $ i $ j\<bar> |i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}"
  apply(simp add: image_def, rule arg_cong[of _ _ Max])
  by auto

lemma finite_matrix_abs:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "finite {\<bar>A $ i $ j\<bar> |i j. i \<in> (UNIV::'m set) \<and> j \<in> (UNIV::'n set)}" (is "finite ?X")
proof-
  {fix i::'m
    have "finite {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)}" 
      using finite_Atleast_Atmost_nat by fastforce}
  hence "\<forall> i::'m. finite {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)}" by blast
  then have "finite (\<Union>i\<in>UNIV. {\<bar>A $ i $ j\<bar> | j. j \<in> (UNIV::'n set)})" (is "finite ?Y")
    using finite_class.finite_UNIV by blast
  also have "?X \<subseteq> ?Y" by auto
  ultimately show ?thesis using finite_subset by blast
qed

lemma maxAbs_ge_0:"maxAbs A \<ge> 0"
proof-
  have "\<And> i j. \<bar>A $ i $ j\<bar> \<ge> 0" by simp
  also have "\<And> i j. maxAbs A \<ge> \<bar>A $ i $ j\<bar>"
    unfolding maxAbs_def using finite_matrix_abs Max_ge maxAbs_def by blast
  finally show "0 \<le> maxAbs A" .
qed

lemma norms_le_dims_maxAbs:
  fixes A::"real^('n::finite)^('m::finite)"
  shows "norm\<^sub>S A \<le> real CARD('n) \<cdot> real CARD('m) \<cdot>(maxAbs A)" (is "norm\<^sub>S A \<le>?n \<cdot> ?m \<cdot> (maxAbs A)")
proof-
  {fix x::"(real, 'n) vec" assume "norm x = 1"
    hence comp_le_1:"\<forall> i::'n. \<bar>x $ i\<bar> \<le> 1"
      by (simp add: norm_bound_component_le_cart)
    have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)"
      using matrix_mult_sum by blast
    hence "norm (A *v x) \<le> (\<Sum>(i::'n)\<in>UNIV. norm ( x $ i *s column i A))"
      by (simp add: sum_norm_le)
    also have "... = (\<Sum>(i::'n)\<in>UNIV. \<bar>x $ i\<bar> \<cdot> norm (column i A))"
      by (simp add: norm_scalar_mult) 
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. norm (column i A))"
      by (metis (no_types, lifting) Groups.mult_ac(2) comp_le_1 mult_left_le norm_ge_zero sum_mono)
    also have "... \<le> (\<Sum>(i::'n)\<in>UNIV. ?m \<cdot> maxAbs A)"
    proof(unfold norm_vec_def L2_set_def real_norm_def)
      have "\<And>i j. \<bar>column i A $ j\<bar> \<le> maxAbs A"
        using finite_matrix_abs Max_ge unfolding column_def maxAbs_def by(simp, blast)
      hence "\<And>i j. \<bar>column i A $ j\<bar>\<^sup>2 \<le> (maxAbs A)\<^sup>2"
        by (metis (no_types, lifting) One_nat_def abs_ge_zero numerals(2) order_trans_rules(23) 
            power2_abs power2_le_iff_abs_le)
      then have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> (\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2)"
        by (meson sum_mono)
      also have "(\<Sum>(j::'m)\<in>UNIV. (maxAbs A)\<^sup>2) = ?m \<cdot> (maxAbs A)\<^sup>2" by simp
      ultimately have "\<And>i. (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> ?m \<cdot> (maxAbs A)\<^sup>2" by force
      hence "\<And>i. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2) \<le> sqrt (?m \<cdot> (maxAbs A)\<^sup>2)"
        by(simp add: real_sqrt_le_mono)
      also have "sqrt (?m \<cdot> (maxAbs A)\<^sup>2) \<le> sqrt ?m \<cdot> maxAbs A"
        using maxAbs_ge_0 real_sqrt_mult by auto
      also have "... \<le> ?m \<cdot> maxAbs A"
        using sqrt_real_nat_le maxAbs_ge_0 mult_right_mono by blast  
      finally show "(\<Sum>i\<in>UNIV. sqrt (\<Sum>j\<in>UNIV. \<bar>column i A $ j\<bar>\<^sup>2)) \<le> (\<Sum>(i::'n)\<in>UNIV. ?m \<cdot> maxAbs A)"
        by (meson sum_mono)
    qed
    also have "(\<Sum>(i::'n)\<in>UNIV. (maxAbs A)) = ?n \<cdot> (maxAbs A)"
      using sum_constant_scale by auto
    ultimately have "norm (A *v x) \<le> ?n \<cdot> ?m \<cdot> (maxAbs A)" by simp}
  from this show ?thesis 
    using unit_norms_exists[of A] Connected.bounded_has_Sup(2) by blast
qed

end