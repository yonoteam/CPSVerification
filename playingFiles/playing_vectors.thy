theory playing_vectors
imports
  "Abstract_HL"
  "Ordinary_Differential_Equations.IVP/Initial_Value_Problem"
  "HOL-Library.FSet" (* Finite sets. *)

begin

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")

(**************************************************************************************************)
section{* Experimentation *}
(**************************************************************************************************)
text{* Skip this part as it was just for my understanding of Isabelle's and local theories' syntax*}

--"Here I am just learning the meaning of this functions."
term "finite A"
term "CARD('a)"
term "a::'a::real_vector"
term "vector_space"
term "({|x,z|} |\<inter>| {|w,x,y,z|}) |\<subseteq>| {|x,y,z|}"
thm "has_vderiv_on_def"
typ "'a::real_normed_vector"
term "f \<in> T \<rightarrow> X"
term "(\<chi> i. (if i=1 then ''x'' else ''y''))"
term "(\<chi> i. 0)"
term "y::real^nat"
term "eventually "

lemma
assumes "\<forall> i. x $ i = (0::nat)"
shows "x = (\<chi> i. (0::nat))"
apply(subst vec_eq_iff)
using assms by simp

-- "Experimenting with Isabelle commands "
type_synonym 'a reals = "(real, 'a) vec"
definition "reals n = {x::(real, 'a) vec. CARD('a) = n}"

-- "Generating a finite type... "
typedef three ="{m::nat. m < 3}"
apply(rule_tac x="0" in exI)
by simp

term "Abs_three x"
term "Rep_three x"
thm bij_betw_finite
thm UNIV_I
thm bij_betwI
thm bij_betwI'
thm Rep_three_inject
thm Rep_three
thm Rep_three_cases
thm Abs_three_cases
thm Abs_three_inverse

lemma card_of_three:"card {m::nat. m < 3} = 3"
by auto

lemma CARD_of_three:"CARD(three) = 3"
using type_definition.card type_definition_three by fastforce 

instance three::finite
apply(standard, subst bij_betw_finite[of Rep_three UNIV "{m::nat. m < 3}"])
apply(rule bij_betwI')
apply (simp add: Rep_three_inject)
using Rep_three apply blast
apply (metis Abs_three_inverse UNIV_I)
by simp

--"Once the final type is attain, we can use it with other functions."
instance vec:: (real_normed_vector,finite) real_normed_vector
by standard

term "x::real \<Rightarrow> real^three"
term "((x::real \<Rightarrow> real^three) solves_ode f)T X"
term "((x::real \<Rightarrow> real^'a) solves_ode f)T X"


(**************************************************************************************************)
section{* Implementation *}
(**************************************************************************************************)
-- "Just stating the types"
term "is_a_state (s::real^'a)"
term "f::real^'a \<Rightarrow> real^'a"
term "\<phi>::real \<Rightarrow> (real^'a \<Rightarrow> real^'a)"
thm solves_ode_def
thm has_vderiv_on_def
thm uniformly_continuous_on_def
thm unique_on_bounded_closed.unique_solution

lemma wp_rel:"wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
proof-
have "\<lfloor>wp R \<lceil>P\<rceil>\<rfloor> = \<lfloor>\<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>\<rfloor>" 
  by (simp add: wp_trafo pointfree_idE)
thus "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>" 
  by (metis (no_types, lifting) wp_simp d_p2r pointfree_idE prp) 
qed

definition "orbit s \<phi> T b = {\<phi> t s |t. t \<in> T \<and> b}"

lemma "\<R> (\<lambda> s. orbit s \<phi> T b) = {(s, \<phi> t s)|s t. t \<in> T \<and> b}"
apply(safe, simp_all add: f2r_def orbit_def)
by(rule_tac x="t" in exI, simp)

lemma wp_orbit1:"b \<Longrightarrow> wp (\<R> (\<lambda> s. orbit s \<phi> T b)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. Q (\<phi> t s)\<rceil>"
unfolding orbit_def f2r_def by (subst wp_rel, auto)

theorem wp_orbit2:"wp (\<R> (\<lambda> s. orbit s \<phi> T b)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. b \<longrightarrow> Q (\<phi> t s)\<rceil>"
unfolding orbit_def f2r_def by (subst wp_rel, auto)

lemma wp_orbit3:"a \<Longrightarrow> wp (\<R> (\<lambda> s. orbit s \<phi> T (b \<and> a))) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. b \<longrightarrow> Q (\<phi> t s)\<rceil>"
unfolding orbit_def f2r_def by(subst wp_rel, auto)

(** PARTICULARIZING **)
definition is_local_flow ::"(real \<Rightarrow> ('a::banach \<Rightarrow> 'a)) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a \<Rightarrow> bool" 
where "is_local_flow \<phi> f T s \<equiv> \<phi> 0 s = s \<and> ((\<lambda> \<tau>. \<phi> \<tau> s) has_vderiv_on (\<lambda>\<tau>. f (\<phi> \<tau> s)))T"
(*"((\<lambda> \<tau>. \<phi> \<tau> s) solves_ode (\<lambda> \<tau>. f)) T S"*)
(*"((\<lambda> \<tau>. \<phi> \<tau> s) has_vderiv_on (\<lambda>\<tau>. f (\<phi> \<tau> s)))T \<and> (\<lambda> \<tau>. \<phi> \<tau> s) \<in> T \<rightarrow> S"*)

definition "f_orbit s \<phi> f T = orbit s \<phi> T (is_local_flow \<phi> f T s)"
definition "g_orbit s \<phi> f T G = orbit s \<phi> T (\<forall> t \<in> T. G (\<phi> t s) \<and> (\<forall> a. is_local_flow \<phi> f T a))"

theorem "wp (\<R>(\<lambda> s. f_orbit s \<phi> f T)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. (\<forall> a. is_local_flow \<phi> f T a) \<longrightarrow> Q (\<phi> t s)\<rceil>"
unfolding f_orbit_def by(subst wp_orbit2, simp)

theorem GenDS:
assumes "\<forall> a. is_local_flow \<phi> f T a"
shows "wp (\<R>(\<lambda> s. g_orbit s \<phi> f T G)) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. (\<forall>a. G (\<phi> t a)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
unfolding g_orbit_def apply(subst wp_orbit3)
using assms apply simp
apply clarsimp
apply(rule iffI)
apply(rule ballI, rule impI)
oops

corollary PreDS:
shows "wp (\<R>(\<lambda> s. g_orbit s (\<lambda> t x. x + c *\<^sub>R t) (\<lambda> x. c) T G)) \<lceil>Q\<rceil> = 
\<lceil>\<lambda> x. \<forall> t \<in> T. (\<forall> s. G s) \<longrightarrow> Q (x + c *\<^sub>R t)\<rceil>"
apply(subst GenDS) unfolding is_local_flow_def apply(rule allI, simp)
apply(rule_tac f'1="\<lambda> x. 0" and g'1="\<lambda> x. c" in derivative_intros(173))
apply(rule derivative_intros, simp)+
apply simp_all
sorry

corollary DS:
shows "\<lceil>\<lambda> x. \<forall> t \<in> T. (\<forall> \<tau> \<in> {0..t}. G (x + c *\<^sub>R t)) \<longrightarrow> Q (x + c *\<^sub>R t)\<rceil> = 
wp (\<R>(\<lambda> s. g_orbit s (\<lambda> t x. x + c *\<^sub>R t) T (\<lambda> x. c) S G)) \<lceil>Q\<rceil>"
apply(subst PreDS, clarsimp) 
apply(rule iffI, clarify)
apply(erule_tac x="t" in ballE) 
apply(erule impE, rule impI)
apply(insert assms(1))
apply(erule_tac x="s" in allE)
apply(simp add: Pi_def)
apply(erule_tac x="t" in allE, simp, simp)
apply(rule ballI, erule impE)
apply(rule_tac x="t" in exI)
using assms(2) 
using assms apply auto
oops

lemma DW:
assumes "\<forall>a\<in>S. (is_local_flow \<phi> f T a)" and "\<forall>s. (\<lambda> \<tau>. \<phi> \<tau> s) \<in> T \<rightarrow> S"
shows "wp (\<R>(\<lambda> s. g_orbit s \<phi> T f S G)) \<lceil>Q\<rceil> = wp (\<R>(\<lambda> s. g_orbit s \<phi> T f S G)) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
using assms(1) apply(subst GenDS, simp)+
apply(clarsimp) using assms(2) by fastforce

lemma "Id \<le> wp (\<R>(\<lambda> s. g_orbit s \<phi> T f S G)) \<lceil>C\<rceil>"
unfolding g_orbit_def
apply(subst wp_orbit)
apply(simp)
oops

lemma DC:
assumes "\<forall>a\<in>S. (is_local_flow \<phi> f T a)" and "\<forall>s. (\<lambda> \<tau>. \<phi> \<tau> s) \<in> T \<rightarrow> S"
assumes "\<forall>s. (\<forall>x\<in>S. G x) \<longrightarrow> (\<forall>t\<in>T. C (\<phi> t s))"
shows "wp (\<R>(\<lambda> s. g_orbit s \<phi> T f S G)) \<lceil>Q\<rceil> = wp (\<R>(\<lambda> s. g_orbit s \<phi> T f S (\<lambda> s. G s \<and> C s))) \<lceil>Q\<rceil>"
using assms(1) apply(subst GenDS, simp)+ apply(thin_tac "\<forall>a\<in>S. is_local_flow \<phi> f T a")+
apply(clarsimp) apply(rule iffI)
using assms(3) apply blast
using assms(3) apply simp
apply(rule impI) apply(erule(1) impE)
oops

term "ad_fun (\<lambda> s. orbit s (\<phi>::real \<Rightarrow> real^'a \<Rightarrow> real^'a) T True)\<^sup>\<bullet>"
term "is_local_flow (\<phi>::real \<Rightarrow> real^'a \<Rightarrow> real^'a) f {0..t} S"
term "\<R> (\<lambda> s. orbit s (\<phi>::real \<Rightarrow> 'a::banach \<Rightarrow> 'a) T True)"

no_notation rel_antidomain_kleene_algebra.fbox ("wp")
notation nd_fun.fbox ("wp")

term "wp ((f::'a \<Rightarrow> 'a set)\<^sup>\<bullet>) ((\<F> \<lceil>P::'a pred\<rceil>)\<^sup>\<bullet>)"
term "\<lambda>f. (ad_fun (f\<^sub>\<bullet>))\<^sup>\<bullet>"
term "\<lambda>f g. (f\<^sub>\<bullet> \<oplus> g\<^sub>\<bullet>)\<^sup>\<bullet>"
term "x::'a nd_fun"


declare[[show_types,show_sorts]]

(*
locale flow = unique_on_bounded_closed +
fixes \<phi> :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
assumes action1: "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
and action2:"\<phi> 0 s = s"
begin

typedef myTypeT = "T" (* \<longleftarrow> not allowed by isabelle... *)

lemma 
assumes "\<forall> s \<in> S. \<phi> 0 s = s \<and> ((\<lambda> \<tau>. \<phi> \<tau> s) has_vderiv_on (\<lambda>\<tau>. f \<tau> (\<phi> \<tau> s)))T"
shows "\<forall> t1 t2. \<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
oops

end

definition is_local_flow :: "(real \<Rightarrow> (real^'a \<Rightarrow> real^'a)) \<Rightarrow> (real^'a \<Rightarrow> real^'a) \<Rightarrow> 
real set \<Rightarrow> (real^'a) set \<Rightarrow> bool" where
"is_local_flow \<phi> f T S \<equiv> \<forall> s \<in> S. \<phi> 0 s = s \<and> ((\<lambda> \<tau>. \<phi> \<tau> s) has_vderiv_on (\<lambda>\<tau>. f (\<phi> \<tau> s)))T"

definition "is_global_flow \<phi> f = is_local_flow \<phi> f UNIV UNIV"

definition "lipschitz2 f L \<equiv> 0 \<le> L \<and> (\<forall> x y. dist (f x) (f y) \<le> L * dist x y)"

class flow =
fixes \<phi> :: "real \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'a"
assumes action1: "\<phi> (t1 + t2) s = \<phi> t1 (\<phi> t2 s)"
and action2:"\<phi> 0 s = s"

instance vec:: (type, finite) scaleR
using class.Real_Vector_Spaces.scaleR.of_class.intro by simp

lemma "(scaleR r x)$i = scaleR r (x$i)"
oops

instance vec:: (ab_group_add, finite) real_vector
apply(standard)
(*by(standard) (vector mult.commute)*)
oops*)



end