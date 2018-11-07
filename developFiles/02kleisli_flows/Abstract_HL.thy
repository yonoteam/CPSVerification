theory Abstract_HL
  imports Main Kleisli "../afpModified/VC_KAD"

begin

no_notation Antidomain_Semiring.antidomain_left_monoid_class.am_add_op (infixl "\<oplus>" 65)
        and Range_Semiring.antirange_semiring_class.ars_r ("r")

text \<open>Now comes the most important thing so far: 
the proof that "non-deterministic" functions form antidomain Kleene algebra.
A subtype is needed for the instantiation statements.\<close>

text \<open>Most of the work goes into replaying facts about enrichted Kleisli categories 
(for the powerset functor) in the single-typed setting. This includes the isomorphism
between homogeneous relations and single-typed set-valued functions.\<close>

typedef 'a nd_fun = "{f::'a \<Rightarrow> 'a set. f \<in> UNIV}"
  by simp

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100)
notation Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

setup_lifting type_definition_nd_fun

text \<open>Definitions are lifted to gain access to the Kleisli categories.\<close>

lift_definition r2fnd :: "'a rel \<Rightarrow> 'a nd_fun" ("\<F>\<^sup>\<bullet>") is "\<lambda>R. (\<F> R)\<^sup>\<bullet>".

lift_definition f2rnd :: "'a nd_fun \<Rightarrow> 'a rel" ("\<R>\<^sup>\<bullet>") is "\<lambda>f. \<R> (f\<^sub>\<bullet>)".

declare Rep_nd_fun_inverse [simp]

lemma r2fnd_prop: "\<F>\<^sup>\<bullet> R = (\<F> R)\<^sup>\<bullet>"
  by (simp add: r2fnd.abs_eq)

lemma f2rnd_prop: "\<R>\<^sup>\<bullet> f = \<R> (f\<^sub>\<bullet>)"
  by (simp add: f2rnd.abs_eq)

lemma r2f2r_inv: "\<F>\<^sup>\<bullet> \<circ> \<R>\<^sup>\<bullet> = id"
  by (transfer, rule ext, simp add: pointfree_idE)

lemma f2r2f_inv: "\<R>\<^sup>\<bullet> \<circ> \<F>\<^sup>\<bullet> = id"
  by (transfer, rule ext, simp add: r2f_def f2r_def Abs_nd_fun_inverse)

instantiation nd_fun :: (type) monoid_mult
begin

lift_definition one_nd_fun :: "'a nd_fun" is "(\<eta>)\<^sup>\<bullet>".

lift_definition times_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is
  "\<lambda>f g. ((f\<^sub>\<bullet>) \<circ>\<^sub>K (g\<^sub>\<bullet>))\<^sup>\<bullet>". 

instance
  by standard (transfer, simp add: Abs_nd_fun_inverse Kcomp_assoc)+

end
(**************************************************************************************************)
interpretation nd_fun: monoid_mult "\<eta>\<^sup>\<bullet>" "\<lambda>f g. ((f\<^sub>\<bullet>) \<circ>\<^sub>K (g\<^sub>\<bullet>))\<^sup>\<bullet>"
by standard (simp add: Abs_nd_fun_inverse Kcomp_assoc)+
(**************************************************************************************************)

lemma r2f_comp_hom: "\<F>\<^sup>\<bullet> (R ; S) = (\<F>\<^sup>\<bullet> R) \<cdot> (\<F>\<^sup>\<bullet> S)"
  by (transfer, simp add: Abs_nd_fun_inverse r2f_hom1)

lemma f2r_comp_hom: "\<R>\<^sup>\<bullet> (f \<cdot> g) = (\<R>\<^sup>\<bullet> f) ; (\<R>\<^sup>\<bullet> g)"
  by (transfer, simp add: Abs_nd_fun_inverse f2r_hom1)

lemma r2f_one_hom [simp]: "\<F>\<^sup>\<bullet> Id = \<eta>\<^sup>\<bullet>"
  by (transfer, simp)

lemma f2r_one_hom [simp]: "\<R>\<^sup>\<bullet> 1 = Id"
  by (transfer, simp add:  Abs_nd_fun_inverse) 

lemma Abs_comp_hom: "(f \<circ>\<^sub>K g)\<^sup>\<bullet> = f\<^sup>\<bullet> \<cdot>  g\<^sup>\<bullet>"
  by (transfer, simp add: Abs_nd_fun_inverse)

lemma Rep_comp_hom: "(f \<cdot> g)\<^sub>\<bullet>  = f\<^sub>\<bullet> \<circ>\<^sub>K g\<^sub>\<bullet>"
  by (simp add: Abs_nd_fun_inverse times_nd_fun.abs_eq)
 
instantiation nd_fun :: (type) dioid_one_zero
begin 

lift_definition plus_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is
  "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet>".

lift_definition zero_nd_fun :: "'a::type nd_fun" is "(\<zeta>)\<^sup>\<bullet>".

lift_definition less_eq_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> bool" is "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g".

lift_definition less_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> bool" is "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g \<and> f \<noteq> g".

instance
apply standard
subgoal by (transfer, simp add: Abs_nd_fun_inverse plus_fun_assoc)
subgoal by (transfer, simp add: plus_fun_comm)
subgoal by (transfer, metis Abs_comp_hom Rep_comp_hom Rep_nd_fun_inverse fun_distr)
subgoal by (transfer, simp)
subgoal by (transfer, simp)
subgoal by (transfer, simp add: Abs_nd_fun_inverse)
subgoal by (transfer, simp add: Abs_nd_fun_inverse)
subgoal by (transfer, simp add: Abs_nd_fun_inverse)
subgoal by (transfer, simp)
subgoal by (transfer, simp)
by (transfer, simp add: Abs_nd_fun_inverse fun_distl fun_distr)+

end

(**************************************************************************************************)
interpretation nd_fun: dioid_one_zero "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet>" "\<lambda>f g. ((f\<^sub>\<bullet>) \<circ>\<^sub>K (g\<^sub>\<bullet>))\<^sup>\<bullet>"
"\<eta>\<^sup>\<bullet>" "\<zeta>\<^sup>\<bullet>" "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g" "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g \<and> f \<noteq> g"
apply standard apply (simp_all add: Abs_nd_fun_inverse)
subgoal by (simp add: plus_fun_assoc)
subgoal by (simp add: plus_fun_comm)
subgoal by (simp add: fun_distr)
apply (simp add: fun_distl)
done
(**************************************************************************************************)

lemma r2f_un_hom: "\<F>\<^sup>\<bullet> (R \<union> S) = (\<F>\<^sup>\<bullet> S) + (\<F>\<^sup>\<bullet> R)"
  by (transfer, simp add: Abs_nd_fun_inverse r2f_un_hom)

lemma f2r_plus_hom: "\<R>\<^sup>\<bullet> (f + g) = (\<R>\<^sup>\<bullet> g) \<union> (\<R>\<^sup>\<bullet> f)"
  by (transfer, simp add: Abs_nd_fun_inverse f2r_plus_hom)

lemma r2f_zero_hom: "\<F>\<^sup>\<bullet> {} = 0"
apply transfer
  by (transfer, simp add: r2f_zero_hom)

lemma f2r_zero_hom: "\<R>\<^sup>\<bullet> 0 = {}"
  by (transfer, simp add: Abs_nd_fun_inverse f2r_zero_hom)

lemma Abs_plus_hom: "(f \<oplus> g)\<^sup>\<bullet> = f\<^sup>\<bullet> + g\<^sup>\<bullet>"
  by (transfer, simp add: Abs_nd_fun_inverse)

lemma Rep_plus_hom: "(f + g)\<^sub>\<bullet> = f\<^sub>\<bullet> \<oplus> g\<^sub>\<bullet>"
  by (simp add: Abs_nd_fun_inverse plus_nd_fun.abs_eq)

lift_definition Plus_nd :: "'a nd_fun set \<Rightarrow> 'a nd_fun" is "\<lambda>F. (Plus {f\<^sub>\<bullet> |f. f \<in> F})\<^sup>\<bullet>". 

lemma "Plus_nd F = (\<lambda>x. \<Union>{(f\<^sub>\<bullet>) x |f. f \<in> F})\<^sup>\<bullet>" 
  apply (simp add: Plus_nd_def Plus_def)
  apply transfer
  by simp

lemma r2f_Un_hom: "\<F>\<^sup>\<bullet> (\<Union>R) = Plus_nd {\<F>\<^sup>\<bullet> r |r. r \<in> R}"
  apply (transfer, simp add: r2f_Un_hom)
  by (metis Abs_nd_fun_inverse Collect_mem_eq UNIV_I)

lemma f2r_Plus_hom: "\<R>\<^sup>\<bullet> (Plus_nd F) = \<Union>{\<R>\<^sup>\<bullet> f |f. f \<in> F}"
  by (auto simp: Plus_nd_def f2rnd_prop f2r_def Plus_def Abs_nd_fun_inverse)

text \<open>The following facts prepare for an instance proof for quantales. 
It could be given at a later stage.\<close>

lemma fun_distl_Plus_nd: "f \<cdot> (Plus_nd G) = Plus_nd {f \<cdot> g |g. g \<in> G}"
  apply (simp add: Plus_nd_def times_nd_fun_def Abs_nd_fun_inverse fun_distl_Plus)
  by (metis Rep_comp_hom Rep_nd_fun_inverse)

lemma fun_distr_Plus_nd: "(Plus_nd F) \<cdot> g = Plus_nd {f \<cdot> g |f. f \<in> F}"
  apply (simp add: Plus_nd_def times_nd_fun_def Abs_nd_fun_inverse fun_distr_Plus)
  by (metis (no_types, lifting) Rep_comp_hom Rep_nd_fun_inverse)

text \<open>Now we prepare for the star.\<close>

lemma r2f_pow: "\<F>\<^sup>\<bullet> (R ^^ i) = (\<F>\<^sup>\<bullet> R) ^ i"
  apply (induct i)
  apply (simp add: one_nd_fun_def)
  by (metis power_class.power.simps(2) r2f_comp_hom relpow.simps(2) relpow_commute)

lemma f2r_pow: "\<R>\<^sup>\<bullet> (f ^ i) = (\<R>\<^sup>\<bullet> f) ^^ i"
  by (induct i, simp_all add: f2r_comp_hom relpow_commute)

text \<open>The following statement requires the single-sorted settng.\<close>

instantiation nd_fun :: (type) kleene_algebra
begin 

definition "star_nd_fun f = Plus_nd {f ^ i |i. True}" 

lemma r2f_star_hom: "\<F>\<^sup>\<bullet> (rtrancl R) = (\<F>\<^sup>\<bullet> R)\<^sup>\<star>"
proof-
  have "\<F>\<^sup>\<bullet> (rtrancl R) = \<F>\<^sup>\<bullet> (\<Union>i. R ^^ i)"
    by (simp add: rtrancl_is_UN_relpow)
  also have "... = \<F>\<^sup>\<bullet> (\<Union>{R ^^ i |i::nat. True})"
    by (simp add: full_SetCompr_eq)
  also have "... = Plus_nd {(\<F>\<^sup>\<bullet> R) ^ i |i::nat. True}"
    by (simp add: r2f_Un_hom, metis r2f_pow)
  finally show ?thesis
    by (simp add: star_nd_fun_def)
qed

lemma f2r_star_hom: "\<R>\<^sup>\<bullet> (f\<^sup>\<star>) = rtrancl (\<R>\<^sup>\<bullet> f)"
  by (metis f2r2f_inv pointfree_idE r2f2r_inv r2f_star_hom)

lemma fun_star_unfoldl_eq: "(1::'a nd_fun) + f \<cdot> f\<^sup>\<star> = f\<^sup>\<star>"
proof -
  have "(\<R>\<^sup>\<bullet> f)\<^sup>* = Id \<union> \<R>\<^sup>\<bullet> f ; \<R>\<^sup>\<bullet> (f\<^sup>\<star>)"
    by (metis (no_types) Abstract_HL.f2r_star_hom r_comp_rtrancl_eq rtrancl_unfold)
  hence "(\<R>\<^sup>\<bullet> f)\<^sup>* = \<R>\<^sup>\<bullet> (id (\<eta>\<^sup>\<bullet>) + f \<cdot> f\<^sup>\<star>)"
    by (metis (no_types) Abstract_HL.f2r_plus_hom f2r_comp_hom f2r_one_hom inf_sup_aci(5) one_nd_fun_def)
  thus ?thesis
  by (metis (no_types) Abstract_HL.f2r_star_hom one_nd_fun_def pointfree_idE r2f2r_inv)
qed
 
lemma fun_star_unfoldl: "(1::'a nd_fun) + f \<cdot> f\<^sup>\<star> \<le> f\<^sup>\<star>"
  by (simp add: fun_star_unfoldl_eq)

lemma fun_star_unfoldr_eq: "(1::'a nd_fun) + f\<^sup>\<star> \<cdot> f = f\<^sup>\<star>"
proof -
  have "\<R>\<^sup>\<bullet> (f\<^sup>\<star> \<cdot> f) \<union> \<R>\<^sup>\<bullet> (id (\<eta>\<^sup>\<bullet>)) = (\<R>\<^sup>\<bullet> (f\<^sup>\<star>) ; \<R>\<^sup>\<bullet> f)\<^sup>="
    by (metis (no_types) f2r_comp_hom f2r_one_hom one_nd_fun_def)
  hence "\<R>\<^sup>\<bullet> ((id (\<eta>\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> (f\<^sup>\<star> \<cdot> f)\<^sub>\<bullet>)\<^sup>\<bullet>) = (\<R>\<^sup>\<bullet> f)\<^sup>*"
    by (metis Abstract_HL.f2r_plus_hom Abstract_HL.f2r_star_hom inf_sup_aci(5) 
      plus_nd_fun.abs_eq rtrancl_unfold)
  hence "1 + f\<^sup>\<star> \<cdot> f = \<F>\<^sup>\<bullet> ((\<R>\<^sup>\<bullet> f)\<^sup>*)"
    by (metis one_nd_fun_def plus_nd_fun.abs_eq pointfree_idE r2f2r_inv)
  thus ?thesis 
    by (metis (no_types) Abstract_HL.f2r_star_hom pointfree_idE r2f2r_inv)
qed

lemma fun_star_unfoldr: "(1::'a nd_fun) + f\<^sup>\<star> \<cdot> f \<le> f\<^sup>\<star>"
  by (simp add: fun_star_unfoldr_eq)

lemma f2r_leq: "f \<le> g \<longleftrightarrow> \<R>\<^sup>\<bullet> f \<subseteq> \<R>\<^sup>\<bullet> g"
  by (transfer, metis Kleisli.f2r_plus_hom Rep_nd_fun_inverse Rep_plus_hom f2r_inj sup.order_iff)

lemma r2f_leq: "R \<subseteq> S \<longleftrightarrow> \<F>\<^sup>\<bullet> R \<le> \<F>\<^sup>\<bullet> S"
  by (transfer, metis Abs_nd_fun_inverse CollectI UNIV_I le_le_fun r2f_leq)

lemma fun_star_inductl: "(h::'a nd_fun) + f \<cdot> g \<le> g \<Longrightarrow> f\<^sup>\<star> \<cdot>  h \<le> g"
  apply(simp add: Abstract_HL.f2r_leq Abstract_HL.f2r_plus_hom f2r_comp_hom f2r_star_hom)
  by (meson dual_order.trans rel_antidomain_kleene_algebra.dual.mult_isor 
    rel_kleene_algebra.star_inductl_var_equiv)

lemma fun_star_inductr: "(h::'a nd_fun) + g \<cdot> f \<le> g \<Longrightarrow> h \<cdot> f\<^sup>\<star> \<le> g"
  apply (simp add: Abstract_HL.f2r_leq Abstract_HL.f2r_plus_hom f2r_comp_hom f2r_star_hom)
  by (simp add: rel_antidomain_kleene_algebra.dual.star_inductl)
  
  
instance
apply standard
apply (simp add: fun_star_unfoldl_eq)
apply (simp add: Abstract_HL.fun_star_inductl)
by (simp add: Abstract_HL.fun_star_inductr)

end

(**************************************************************************************************)
interpretation nd_fun: kleene_algebra "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet>" "\<lambda>f g. ((f\<^sub>\<bullet>) \<circ>\<^sub>K (g\<^sub>\<bullet>))\<^sup>\<bullet>" "\<eta>\<^sup>\<bullet>" "\<zeta>\<^sup>\<bullet>"
"\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g" "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g \<and> f \<noteq> g" "\<lambda> f. Plus_nd {f ^ i |i. True}"
apply unfold_locales (*apply (simp_all add: Rep_comp_hom Abs_comp_hom Abs_nd_fun_inverse)*)
subgoal using fun_star_unfoldl_eq by (metis Rep_comp_hom Rep_nd_fun_inverse Rep_plus_hom 
  nd_fun.join.sup_idem one_nd_fun.abs_eq star_nd_fun_def)
proof-
  fix z x y :: "'a nd_fun"
  assume "(((z\<^sub>\<bullet> \<oplus> ((x\<^sub>\<bullet> \<circ>\<^sub>K y\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y"
  moreover have "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y" using fun_star_inductl by simp
  ultimately have "((((x\<^sup>\<star>)\<^sub>\<bullet> \<circ>\<^sub>K z\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y"
  by (metis (mono_tags, lifting) less_eq_nd_fun.transfer plus_nd_fun.transfer times_nd_fun.transfer)
  thus "(((Plus_nd {x ^ i |i. True}\<^sub>\<bullet> \<circ>\<^sub>K z\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y" by (simp add: star_nd_fun_def) 
next
  fix z x y :: "'a nd_fun"
  assume "(((z\<^sub>\<bullet> \<oplus> ((y\<^sub>\<bullet> \<circ>\<^sub>K x\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y"
  also have "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y" using fun_star_inductr by simp
  ultimately have "(((z\<^sub>\<bullet> \<circ>\<^sub>K (x\<^sup>\<star>)\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y"
  by (metis (mono_tags, lifting) less_eq_nd_fun.transfer plus_nd_fun.transfer times_nd_fun.transfer)
  thus "(((z\<^sub>\<bullet> \<circ>\<^sub>K Plus_nd {x ^ i |i. True}\<^sub>\<bullet>)\<^sup>\<bullet>)\<^sub>\<bullet> \<oplus> y\<^sub>\<bullet>)\<^sup>\<bullet> = y" by (simp add: star_nd_fun_def) 
qed
(**************************************************************************************************)

instantiation nd_fun :: (type) antidomain_kleene_algebra
begin

lift_definition antidomain_op_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is "\<lambda>f. (ad_fun (f\<^sub>\<bullet>))\<^sup>\<bullet>".

lemma f2r_ad_hom: "\<R>\<^sup>\<bullet> (ad f) = ad_rel (\<R>\<^sup>\<bullet> f)"
apply(transfer)
by (transfer, simp add: f2r_ad_fun_hom Abs_nd_fun_inverse)


lemma r2f_rel_ad_hom: "\<F>\<^sup>\<bullet> (ad_rel R) = ad (\<F>\<^sup>\<bullet> R)"
  by (transfer, simp add: r2f_ad_rel_hom Abs_nd_fun_inverse)

instance
  by standard (transfer, simp add: Abs_nd_fun_inverse)+

end

text \<open>This shows that state transformers form antidomain Kleene algebras.\<close>

interpretation nd_fun: antidomain_kleene_algebra "\<lambda>f. (ad_fun (f\<^sub>\<bullet>))\<^sup>\<bullet>"
"\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet>" "\<lambda>f g. ((f\<^sub>\<bullet>) \<circ>\<^sub>K (g\<^sub>\<bullet>))\<^sup>\<bullet>" "\<eta>\<^sup>\<bullet>" "\<zeta>\<^sup>\<bullet>"
"\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g" "\<lambda>f g. ((f\<^sub>\<bullet>) \<oplus> (g\<^sub>\<bullet>))\<^sup>\<bullet> = g \<and> f \<noteq> g" "\<lambda>f. Plus_nd {f ^ i |i. True}"
by standard (simp_all add: Rep_comp_hom Abs_comp_hom Abs_nd_fun_inverse)

end


