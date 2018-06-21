theory playing_flows
imports
  "Abstract_HL"
  "Ordinary_Differential_Equations.IVP/Initial_Value_Problem"
  "HOL-Library.FSet" (* Finite sets. *)

begin

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and VC_KAD.gets ("_ ::= _" [70, 65] 61)

lemma wp_rel:"wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
  by (simp add: wp_trafo pointfree_idE)
thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
  by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

named_theorems ubc_definitions "definitions used in the locale unique_on_bounded_closed"

declare unique_on_bounded_closed_def [ubc_definitions]
    and unique_on_bounded_closed_axioms_def [ubc_definitions]
    and unique_on_closed_def [ubc_definitions]
    and compact_interval_def [ubc_definitions]
    and compact_interval_axioms_def [ubc_definitions]
    and self_mapping_def [ubc_definitions]
    and self_mapping_axioms_def [ubc_definitions]
    and continuous_rhs_def [ubc_definitions]
    and closed_domain_def [ubc_definitions]
    and global_lipschitz_def [ubc_definitions]
    and interval_def [ubc_definitions]

locale local_flow = 
fixes \<phi> :: "real \<Rightarrow> ('a::banach) \<Rightarrow> 'a" and f::"'a \<Rightarrow> 'a" and S::"'a set" and T::"real set" and L::real
assumes flow_ubc:"\<And> s. s \<in> S \<Longrightarrow> unique_on_bounded_closed 0 T s (\<lambda> t. f) S L"
    and flow_def:"\<And> x s t. t \<in> T \<Longrightarrow> (x solves_ode (\<lambda> t. f))T S \<Longrightarrow> x 0 = s \<Longrightarrow> \<phi> t s = x t"
begin

named_theorems flow_ubcD "computation rules assuming {@term S} inhabited."

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "is_interval T"
using assms flow_ubc 
unfolding ubc_definitions
by (simp add: interval_def)

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "a \<in> T \<Longrightarrow> b \<in> T \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<in> T"
using assms unfolding is_interval_def
by (meson flow_ubcD(1) is_interval_1) 

lemma [flow_ubcD]:
assumes "s \<in> S"
obtains t0 t1 where "T = {t0 .. t1}"
using assms flow_ubc compact_interval.T_def 
unfolding ubc_definitions(1,3) by blast

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "compact T"
using assms flow_ubc
unfolding ubc_definitions by simp

lemma around_zero [flow_ubcD]:
assumes "s \<in> S"
shows "0 \<in> T"
using assms flow_ubc 
unfolding ubc_definitions by simp
  
lemma [flow_ubcD]:
assumes "s \<in> S"
shows "t \<in> T \<Longrightarrow> x 0 = s \<Longrightarrow> x \<in> {0--t} \<rightarrow> S 
  \<Longrightarrow> continuous_on {0--t} x 
  \<Longrightarrow> x 0 + ivl_integral 0 t (\<lambda>t. f (x t)) \<in> S"
using assms flow_ubc
unfolding ubc_definitions by blast

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "continuous_on (T \<times> S) (\<lambda>(t, x). f x)"
using assms flow_ubc
unfolding ubc_definitions by simp 

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "closed S"
using assms flow_ubc
unfolding ubc_definitions by simp

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "t \<in> T \<Longrightarrow> lipschitz S f L"
using assms flow_ubc
unfolding ubc_definitions by blast

lemma [flow_ubcD]:
assumes "s \<in> S"
shows "t0 \<in> T \<Longrightarrow> t1 \<in> T \<Longrightarrow> \<bar>t0 - t1\<bar> \<cdot> L < 1"
using assms flow_ubc
unfolding ubc_definitions by blast

abbreviation "phi t s \<equiv> (apply_bcontfun (unique_on_bounded_closed.fixed_point 0 T s (\<lambda> t. f) S)) t"

lemma fixed_point_ivp:
assumes "s \<in> S"
shows "((\<lambda> t. phi t s) solves_ode (\<lambda> t. f))T S"
  and "phi 0 s = s "
using assms flow_ubc unique_on_bounded_closed.fixed_point_solution apply blast
using assms flow_ubc unique_on_bounded_closed.fixed_point_iv by blast 

lemma flow_is_fixed_point:
assumes "s \<in> S" and "t \<in> T"
shows "\<phi> t s = phi t s"
using assms fixed_point_ivp 
  and flow_def by blast

theorem flow_solves:
assumes "s \<in> S"
shows "((\<lambda> t. \<phi> t s) solves_ode (\<lambda> t. f))T S"
using assms fixed_point_ivp 
  and flow_is_fixed_point by auto

theorem flow_action1:
assumes "s \<in> S"
shows "\<phi> 0 s = s"
using assms fixed_point_ivp flow_is_fixed_point
  and around_zero by auto

lemma flow_is_banach_endo:
assumes "s \<in> S" and "t \<in> T"
shows "\<phi> t s \<in> S"
apply(rule_tac A="T" in Pi_mem)
using assms flow_solves
unfolding solves_ode_def by auto

abbreviation "\<C> t \<equiv> {x \<in> T. t + x \<in> T}"

lemma is_interval_sub_translation:
assumes "s \<in> S"
shows "is_interval (\<C> t)" 
unfolding is_interval_def apply(clarify, safe, simp_all)
using assms flow_ubcD(2) apply blast
using assms flow_ubcD(2) by (meson add_left_mono)

lemma is_compact_sub_translation:
assumes "s \<in> S"
shows "compact (\<C> t)"
proof-
from assms obtain t0 t1 where "T = {t0 .. t1}"
using flow_ubcD(3) by blast
have "\<C> t = {x. t + x \<in> T} \<inter> T" by auto
hence *:"\<C> t = {t0 - t .. t1 - t} \<inter> {t0 .. t1}"
using \<open>T = {t0 .. t1}\<close> by(safe, simp_all)
then have "closed (\<C> t)" by simp
thus "compact (\<C> t)" by (simp add: *)
qed

lemma is_sub_translation: "(\<C> t \<times> S) \<subseteq> (T \<times> S)"
apply(rule subsetI) by auto

lemma ubc_sub_translation:"s \<in> S \<Longrightarrow> t \<in> T \<Longrightarrow> unique_on_bounded_closed 0 (\<C> t) (\<phi> t s) (\<lambda>t. f) S L"
unfolding ubc_definitions apply(simp add: is_compact_sub_translation is_interval_sub_translation 
  around_zero flow_is_banach_endo flow_ubcD(8-10), safe)
using around_zero nonempty_set_def apply force
using flow_ubcD(6) flow_is_banach_endo apply force
using flow_ubcD(7) is_sub_translation by (metis (no_types) continuous_on_subset)

lemma shifted_flow_solves:"s \<in> S \<Longrightarrow> ((\<lambda> \<tau>. \<phi> \<tau> s) solves_ode (\<lambda> \<tau>. f))((\<lambda>x. x + t) ` \<C> t) S"
apply(rule_tac S="T" and Y="S" in solves_ode_on_subset)
using flow_solves apply (simp_all add: Groups.add_ac(2) image_def)
by auto

lemma add_flow_solves:"s \<in> S \<Longrightarrow> ((\<lambda>\<tau>. \<phi> (\<tau> + t) s) solves_ode (\<lambda> t. f))(\<C> t) S"
using shifted_flow_solves unfolding solves_ode_def apply safe
apply(subgoal_tac "((\<lambda>\<tau>. \<phi> \<tau> s) \<circ> (\<lambda>\<tau>. \<tau> + t) has_vderiv_on 
(\<lambda>x. (\<lambda>\<tau>. 1) x *\<^sub>R (\<lambda>t. f (\<phi> t s)) ((\<lambda>\<tau>. \<tau> + t) x))) (\<C> t)", simp add: comp_def)
apply(rule has_vderiv_on_compose, simp)
apply(rule_tac f'1="\<lambda> x. 1 " and g'1="\<lambda> x. 0" in derivative_intros(173))
apply(rule derivative_intros, simp)+
by auto

theorem flow_action2:
assumes "s \<in> S" and "t1 \<in> \<C> t2" and "t2 \<in> T"
shows "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
using assms 
proof-
have g1:"\<phi> (0 + t2) s = \<phi> t2 s" by simp
have g2:"((\<lambda> \<tau>. \<phi> (\<tau> + t2) s) solves_ode (\<lambda> t. f))(\<C> t2) S" 
  using add_flow_solves assms(1) by simp
have h0:"\<phi> t2 s \<in> S" 
  using assms flow_is_banach_endo by simp
hence h1:"\<phi> 0 (\<phi> t2 s) = \<phi> t2 s" 
  using flow_action1 by simp
have h2:"((\<lambda> \<tau>. \<phi> \<tau> (\<phi> t2 s)) solves_ode (\<lambda> t. f))(\<C> t2) S"
  apply(rule_tac S="T" and Y="S" in solves_ode_on_subset)
  using h0 flow_solves by auto 
from g1 g2 h1 and h2 have "\<And> t. t \<in> \<C> t2 \<Longrightarrow> \<phi> (t + t2) s = \<phi> t (\<phi> t2 s)"
  using assms unique_on_bounded_closed.unique_solution 
  ubc_sub_translation by blast
thus "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)" 
  using assms(2) by simp
qed

definition "orbit s = {\<phi> t s |t. t \<in> T}"

lemma "\<R> (\<lambda> s. orbit s) = {(s, \<phi> t s)|s t. t \<in> T}"
apply(safe, simp_all add: f2r_def orbit_def)
by(rule_tac x="t" in exI, simp)

theorem wp_orbit:"wp (\<R> (\<lambda> s. orbit s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
unfolding orbit_def f2r_def by (subst wp_rel, auto)

end

lemma constant_is_ubc:"0 \<le> t \<Longrightarrow> unique_on_bounded_closed 0 {0..t} s (\<lambda>t s. c) UNIV (1 / (t + 1))"
unfolding ubc_definitions apply(simp add: nonempty_set_def lipschitz_def, safe)
using continuous_on_const by (blast, auto)

lemma line_solves_constant:"((\<lambda> \<tau>. x + \<tau> *\<^sub>R c) solves_ode (\<lambda>t s. c)) {0..t} UNIV"
unfolding solves_ode_def apply simp
apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(173))
apply(rule derivative_intros, simp)+
by simp_all

lemma line_is_local_flow:
"0 \<le> t \<Longrightarrow> local_flow (\<lambda> t x. x + t *\<^sub>R c) (\<lambda> s. c) UNIV {0..t} (1/(t + 1))"
unfolding local_flow_def apply(rule conjI)
using constant_is_ubc apply blast 
apply(rule)+ subgoal for x s \<tau>
apply(rule unique_on_bounded_closed.unique_solution
  [of 0 "{0..t}" s "(\<lambda>t s. c)" UNIV "(1 / (t + 1))"])
using constant_is_ubc apply blast
using line_solves_constant apply blast
by simp_all.

abbreviation "orbit \<phi> T \<equiv> \<lambda> s. local_flow.orbit \<phi> T s"

corollary DS:
assumes "0 \<le> t"
shows " wp (\<R>(orbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R c) {0..t})) \<lceil>Q\<rceil> = \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. Q (x + \<tau> *\<^sub>R c)\<rceil>"
apply(rule local_flow.wp_orbit[of "\<lambda> \<tau> x. x + \<tau> *\<^sub>R c" "\<lambda> s. c" UNIV "{0..t}" "1/(t + 1)"])
using assms line_is_local_flow by blast

locale guarded_flow = local_flow +
fixes G::"'a pred"

begin

definition "gorbit s = {\<phi> t s |t. t \<in> T \<and> G (\<phi> t s)}"

lemma ok:"\<lceil>P\<rceil> = Id \<Longrightarrow> \<forall> s. P s"
by (metis Id_O_R VC_KAD.p2r_neg_hom d_p2r empty_iff p2r_eq_prop p2r_subid rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.addual.bbox_def rel_antidomain_kleene_algebra.am1 rel_antidomain_kleene_algebra.fbox_one rpr wp_trafo)

theorem wp_orbit:"wp (\<R> (\<lambda> s. gorbit s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. G (\<phi> t s) \<longrightarrow> Q (\<phi> t s)\<rceil>"
unfolding gorbit_def f2r_def by(subst wp_rel, auto)

corollary ok2: "wp (\<R> (\<lambda> s. gorbit s)) \<lceil>Q\<rceil> = Id \<Longrightarrow> \<forall> s. \<forall> t \<in> T. G (\<phi> t s) \<longrightarrow> Q (\<phi> t s)"
apply(subst (asm) wp_orbit)
apply(clarsimp)
using ok by auto

end

theorem New_GenDS:
assumes "guarded_flow \<phi> f S T L"
shows "wp (\<R>(\<lambda> s. guarded_flow.gorbit \<phi> T G s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. G (\<phi> t s) \<longrightarrow> Q (\<phi> t s)\<rceil>"
apply(subst guarded_flow.wp_orbit[of \<phi> f S T L])
using assms(1) by simp_all

corollary New_DW:
assumes tHyp:"t \<ge> 0"
shows "wp (\<R>(\<lambda> s. guarded_flow.gorbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R c) {0..t} G s)) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> s. \<forall> \<tau> \<in> {0..t}. G (s + \<tau> *\<^sub>R c) \<longrightarrow> Q (s + \<tau> *\<^sub>R c)\<rceil>"
apply(subst New_GenDS[of "\<lambda> \<tau> x. x + \<tau> *\<^sub>R c" "\<lambda>t. c" UNIV "{0..t}" "1/(t + 1)"])
unfolding guarded_flow_def using tHyp and line_is_local_flow apply blast
by simp

lemma New_DC:
assumes "wp (\<R>(\<lambda> s. guarded_flow.gorbit \<phi> T G s)) \<lceil>C\<rceil> = Id"
  and "guarded_flow \<phi> f S T L"
shows "wp (\<R>(\<lambda> s. guarded_flow.gorbit \<phi> T G s)) \<lceil>Q\<rceil> = 
wp (\<R>(\<lambda> s. guarded_flow.gorbit \<phi> T (\<lambda> s. G s \<and> C s) s)) \<lceil>Q\<rceil>"
apply(subst guarded_flow.wp_orbit) defer
apply(subst guarded_flow.wp_orbit) defer
apply(clarsimp) using assms guarded_flow.ok2 apply blast
using assms by simp_all

theorem Platzer_GenDS:(* The guard should only be valid for the flow applied to initial state. *)
assumes "local_flow \<phi> f S T L"
    and "\<And> s t. t \<in> T \<Longrightarrow> s \<in> S \<Longrightarrow> G (\<phi> t s)"
shows "wp (\<R>(\<lambda> s. local_flow.orbit \<phi> T s)) \<lceil>Q\<rceil> = \<lceil>\<lambda> x. \<forall> t \<in> T. (\<forall> s \<in> S. G (\<phi> t s)) \<longrightarrow> Q (\<phi> t x)\<rceil>"
apply(subst local_flow.wp_orbit[of \<phi> f S T L])
subgoal using assms(1) by simp
apply(auto)
apply(erule_tac x="t" in ballE)
using assms(2) by simp_all

corollary Platzer_DS:
assumes "\<And> s \<tau>. \<tau> \<in> {-t .. t} \<Longrightarrow> G (s + \<tau> *\<^sub>R c)"
    and tHyp:"t \<ge> 0"
shows "wp (\<R>(orbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R c) {0..t})) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall> s. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
apply(subst Platzer_GenDS[of "\<lambda> t x. x + t *\<^sub>R c" "\<lambda> s. c" UNIV "{0..t}" "1/(t + 1)" G])
using tHyp and line_is_local_flow apply blast
using assms(1) by simp_all

term "x::real^('a::finite)"
term "(\<R>(\<lambda> s. local_flow.orbit (\<lambda> t x. x + t *\<^sub>R (c::real^'a)) {-t .. t} s))"
term "(op $ (x::real^'a))"
term "\<chi> i. (1::real)"
term "vec_lambda ((op $ (x::real^'a))(i := \<pi>))"
term "\<lambda> f x y. f(x := y)"
term "override_on (op $ (x::real^'a))"
term "\<chi> i. (op $ (x::real^'a))(i := \<pi>)"
(* OBS: instance vec :: (banach, finite) banach *)
(* definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
   "v ::= e = {(s,s (v := e s)) |s. True}" 
   string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel                'a store = string  \<Rightarrow> 'a
   string \<Rightarrow> ((string  \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> (string  \<Rightarrow> 'a) rel  real^'a = 'a \<Rightarrow> real
   string \<Rightarrow> ((string  \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> real) rel
*)

abbreviation assign :: "('a::finite) \<Rightarrow> real \<Rightarrow> (real, 'a) vec \<Rightarrow> ((real, 'a) vec) set" 
("_ ::= _" [70, 70] 70) where "i ::= r \<equiv> (\<lambda>x. {vec_lambda ((op $ x)(i:= r))})"

term "\<R>(i ::= r)"

lemma "y \<in> (i ::= r) x  \<Longrightarrow> op $ y = (op $ x)(i := r)"
by auto

typedef vars ="{''x'',''v'',''a''}" (*morphisms var str*)
apply(rule_tac x="''x''" in exI)
by simp

lemma card_of_vars:"card {''x'',''v'',''a''} = 3"
by auto

lemma CARD_of_vars:"CARD(vars) = 3"
using type_definition.card type_definition_vars by fastforce 

instance vars::finite
apply(standard, subst bij_betw_finite[of Rep_vars UNIV "{''x'',''v'',''a''}"])
apply(rule bij_betwI')
apply (simp add: Rep_vars_inject)
using Rep_vars apply blast
apply (metis Abs_vars_inverse UNIV_I)
by simp

abbreviation ith :: "(real, vars) vec \<Rightarrow> string \<Rightarrow> real" (infixl "\<downharpoonleft>" 90) where
"s \<downharpoonleft> x \<equiv> s $ Abs_vars x"

lemma
"PRE (\<lambda> s. s \<downharpoonleft> ''x'' = 0 \<and> s \<downharpoonleft> ''a'' > 0)
((\<R>((Abs_vars ''a'') ::= s \<downharpoonleft> ''a''));(\<R>(orbit (\<lambda> \<tau> x. x + \<tau> *\<^sub>R (\<chi> i. x \<downharpoonleft> ''v'')) {0..t})))\<^sup>*
POST (\<lambda> s. s \<downharpoonleft> ''x'' \<ge> 0)"
oops

(* 
TYPE: {v1, v2, v3, ..., vN}
VECTORS: (\<lbrakk>v1\<rbrakk>,\<lbrakk>v2\<rbrakk>,\<lbrakk>v3\<rbrakk>,...,\<lbrakk>vN\<rbrakk>)

*)

term "x::('a::finite_UNIV)"
lemma (in type_definition) "UNIV > 0"
oops

thm bij_betw_same_card bij_betwI
term "of_real"    (* real \<Rightarrow> 'a *)
term "of_nat"     (* nat \<Rightarrow> 'a *)
term "real_of_nat"(* nat \<Rightarrow> real *)
term "int"        (* nat \<Rightarrow> int *)
term "nat"        (* int \<Rightarrow> nat *)
term "real"       (* nat \<Rightarrow> real *)
term "numeral" 

typedef ('a::finite) sized_real_sets = "{x::real set|x. CARD('a) = card x}"
proof-
obtain n::nat where "card(UNIV::'a set) = n" by simp
let ?x = "{(of_nat m)::real |m. m < n}"
have "card {m|m. m < n} = n" by simp
have "card ?x = card {m|m. m < n}"
apply(subst bij_betw_same_card[of "\<lambda> n. of_nat n" "{m|m. m < n}" ?x])
apply(rule bij_betwI[of real "{m |m. m < n}" ?x "\<lambda> x. if (\<exists> n. real n = x) then n else 0"])
apply simp
unfolding Pi_def apply(clarsimp, safe)

oops

end