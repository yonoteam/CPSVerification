theory cat2ndfun
  imports "../hs_prelims" "Transformer_Semantics.Kleisli_Quantale" "KAD.Modal_Kleene_Algebra"
                        
begin


section{* Hybrid System Verification *}

\<comment> \<open>We start by deleting some conflicting notation and introducing some new.\<close>
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Range_Semiring.antirange_semiring_class.ars_r ("r")
        and Isotone_Transformers.bqtran ("\<lfloor>_\<rfloor>")

type_synonym 'a pred = "'a \<Rightarrow> bool"
notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

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

lemma eq_p2ndf_iff:"(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (P = Q)"
proof(safe)
  assume "\<lceil>P\<rceil> = \<lceil>Q\<rceil>"
  hence "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> \<and> \<lceil>Q\<rceil> \<le> \<lceil>P\<rceil>" by simp
  then have "(\<forall>s. P s \<longrightarrow> Q s) \<and> (\<forall>s. Q s \<longrightarrow> P s)" by simp
  thus "P = Q" by auto
qed

lemma p2ndf_le_eta[simp]:"\<lceil>P\<rceil> \<le> \<eta>\<^sup>\<bullet>"
  by(transfer, simp add: le_fun_def, clarify)

lemma ads_d_p2ndf[simp]:"d \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  unfolding ads_d_def antidomain_op_nd_fun_def by(rule nd_fun_ext, auto)

lemma ad_p2ndf[simp]:"ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding antidomain_op_nd_fun_def by(rule nd_fun_ext, auto)

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

lemma wp_nd_fun2:"wp F \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. y \<in> ((F\<^sub>\<bullet>) x) \<longrightarrow> P y\<rceil>"
  apply(simp add: fbox_def antidomain_op_nd_fun_def)
  by(rule nd_fun_ext, auto simp: Rep_comp_hom kcomp_prop)

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

lemma wp_trafo: "\<lfloor>wp F \<lceil>Q\<rceil>\<rfloor> s = (\<forall>s'. s' \<in> (F\<^sub>\<bullet>) s \<longrightarrow> Q s')"  
  apply(subgoal_tac "F = (F\<^sub>\<bullet>)\<^sup>\<bullet>")
  apply(rule ssubst[of F "(F\<^sub>\<bullet>)\<^sup>\<bullet>"], simp)
  apply(subst wp_nd_fun)
  by(simp_all add: f2r_def)

\<comment> \<open>Another characterization of the wp operator in terms of the forward box operator.\<close>
lemma ffb_is_wp:"fb\<^sub>\<F> (F\<^sub>\<bullet>) {x. P x} = {s. \<lfloor>wp F \<lceil>P\<rceil>\<rfloor> s}"
  unfolding ffb_def unfolding map_dual_def klift_def kop_def fbox_def
  unfolding r2f_def f2r_def apply clarsimp
  unfolding antidomain_op_nd_fun_def unfolding dual_set_def 
  unfolding times_nd_fun_def kcomp_def by force

lemma wp_is_ffb:"wp F \<lceil>P\<rceil> = (\<lambda>x. {x} \<inter> fb\<^sub>\<F> (F\<^sub>\<bullet>) {s. P s})\<^sup>\<bullet>"
  apply(rule nd_fun_ext, simp)
  apply(subgoal_tac "F = (F\<^sub>\<bullet>)\<^sup>\<bullet>")
   apply(rule ssubst[of F "(F\<^sub>\<bullet>)\<^sup>\<bullet>"], simp)
  apply(subst wp_nd_fun)
   apply(subst ffb_is_wp)
   apply(subst wp_trafo)
  by auto

lemma wp_is_ffb2:"wp F P = (\<lambda>x. {x} \<inter> fb\<^sub>\<F> (F\<^sub>\<bullet>) {s. \<lfloor>P\<rfloor> s})\<^sup>\<bullet>"
  apply(rule nd_fun_ext, simp)
  unfolding ffb_def unfolding map_dual_def klift_def kop_def fbox_def
  unfolding r2f_def f2r_def apply clarsimp
  unfolding antidomain_op_nd_fun_def unfolding dual_set_def 
  unfolding times_nd_fun_def apply auto
  unfolding kcomp_prop apply auto
  by (metis (full_types, lifting) Int_Collect UnCI empty_not_insert ex_in_conv image_eqI)


abbreviation vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b" ("_(2[_ :== _])" [70, 65] 61) where 
"x[i :== a] \<equiv> (\<chi> j. (if j = i then a else (x $ j)))"

abbreviation assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2[_ ::== _])" [70, 65] 61) where 
"[x ::== expr]\<equiv> (\<lambda>s. {s[x :== expr s]})\<^sup>\<bullet>" 

lemma wp_assign[simp]: "wp ([x ::== expr]) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s[x :== expr s])\<rceil>"
  by(subst wp_nd_fun, rule nd_fun_ext, simp)

definition (in antidomain_kleene_algebra) cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" 
("if _ then _ else _ fi" [64,64,64] 63) where "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" 
("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> cond \<lceil>P\<rceil> X Y"

lemma ffb_if_then_else:
  assumes "\<lceil>\<lambda>s. P s \<and> T s\<rceil> \<le> wp X \<lceil>Q\<rceil>"
    and "\<lceil>\<lambda>s. P s \<and> \<not> T s\<rceil> \<le> wp Y \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (IF T THEN X ELSE Y FI) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun2)
  apply(subst (asm) wp_nd_fun2)+
  unfolding cond_def apply(clarsimp, transfer)
  by(auto simp: kcomp_prop)

lemma (in antidomain_kleene_algebra) fbox_starI: 
assumes "d p \<le> d i" and "d i \<le> |x] i" and "d i \<le> d q"
shows "d p \<le> |x\<^sup>\<star>] q"
  by (meson assms local.dual_order.trans local.fbox_iso local.fbox_star_induct_var)

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

lemma wp_starI:
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

lemma ffb_starI:
assumes "{x. P x} \<le> {x. I x}" and "{x. I x} \<le> fb\<^sub>\<F> (F\<^sub>\<bullet>) {x. I x}" and "{x. I x} \<le> {x. Q x}"
shows "{x. P x} \<le> fb\<^sub>\<F> ((qstar F)\<^sub>\<bullet>) {x. Q x}"
proof-
  from assms(1,3) have "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<and> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>" by auto
  also from assms(2) have "\<lceil>I\<rceil> \<le> wp F \<lceil>I\<rceil>" by(subst wp_is_ffb, transfer, auto simp: le_fun_def)
  ultimately have "\<lceil>P\<rceil> \<le> wp (qstar F) \<lceil>Q\<rceil>" using wp_starI by blast
  from this show ?thesis by(subst (asm) wp_is_ffb, transfer, auto simp: le_fun_def)
qed

subsection{* Verification by providing solutions *}

abbreviation "orbital f T S t0 x0 \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T}"
abbreviation "g_orbital f T S t0 x0 G \<equiv> 
  {x t |t x. t \<in> T \<and> (x solves_ode f)T S \<and> x t0 = x0 \<and> x0 \<in> S \<and> t0 \<in> T \<and> (\<forall> r \<in> {t0--t}. G (x r))}"

abbreviation 
g_evolution ::"(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a pred \<Rightarrow> 'a nd_fun" 
("(1{[x\<acute>=_]_ _ @ _ & _})") where "{[x\<acute>=f]T S @ t0 & G} \<equiv> (\<lambda> s. g_orbital f T S t0 s G)\<^sup>\<bullet>"

context picard_ivp
begin

lemma orbital_collapses: 
  assumes ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "orbital f T S t0 s = {\<phi> t s| t. t \<in> T}"
  apply safe apply(rule_tac x="t" in exI, simp)
   apply(rule_tac x="xa" and s="xa t0" in unique_solution, simp_all add: assms)
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI)
  using assms init_time by auto

lemma g_orbital_collapses: 
  assumes ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s" and "s \<in> S"
  shows "g_orbital f T S t0 s G = {\<phi> t s| t. t \<in> T \<and> (\<forall> r \<in> {t0--t}. G (\<phi> r s))}"
  apply safe apply(rule_tac x="t" in exI, simp) 
  using assms unique_solution apply(metis closed_segment_subset_domainI)
  apply(rule_tac x="t" in exI, rule_tac x="\<lambda>t. \<phi> t s" in exI) 
  using assms init_time by auto

lemma wp_orbit:
  assumes ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "wp ((\<lambda> s. orbital f T S t0 s)\<^sup>\<bullet>) \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_nd_fun, subst eq_p2ndf_iff) apply(rule ext, safe)
   apply(erule_tac x="\<phi> t s" in allE, erule impE, simp)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t s" in exI)
  using ivp init_time apply(simp, simp)
  apply(subgoal_tac "\<phi> t (x t0) = x t")
   apply(erule_tac x="t" in ballE, simp, simp)
  by(rule_tac y="x" and s="x t0" in unique_solution, simp_all add: assms)

lemma wp_g_orbit:
  assumes ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> = \<lceil>\<lambda> s. \<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {t0--t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  apply(subst wp_nd_fun, subst eq_p2ndf_iff) apply(rule ext, safe)
   apply(erule_tac x="\<phi> t s" in allE, erule impE, simp)
    apply(rule_tac x="t" in exI, rule_tac x="\<lambda> t. \<phi> t s" in exI)
  apply(simp add: ivp init_time, simp)
  apply(subgoal_tac "\<forall>r\<in>{t0--t}. \<phi> r (x t0) = x r")
   apply(erule_tac x="t" in ballE, safe)
    apply(erule_tac x="r" in ballE)+ apply simp_all
  apply(erule_tac x="t" in ballE)+ apply simp_all
  apply(rule_tac y="x" and s="x t0" in unique_solution, simp_all add: assms)
  using subsegment by blast 

end

lemma dSolution:
  assumes "picard_ivp f T S L t0" and ivp:"\<forall>s \<in> S. ((\<lambda>t. \<phi> t s) solves_ode f)T S \<and> \<phi> t0 s = s"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t \<in> T. s \<in> S \<longrightarrow> (\<forall> r \<in> {t0..t}.G (\<phi> r s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst picard_ivp.wp_g_orbit, auto)
  by (simp add: Starlike.closed_segment_eq_real_ivl)

text{* This last theorem allows us to compute weakest liberal preconditions for known systems of ODEs: *}
corollary line_DS: "0 \<le> t \<Longrightarrow> wp {[x\<acute>=\<lambda>t s. c]{0..t} UNIV @ 0 & G} \<lceil>Q\<rceil> = 
    \<lceil>\<lambda> x. \<forall> \<tau> \<in> {0..t}. (\<forall>r\<in>{0--\<tau>}. G (x + r *\<^sub>R c)) \<longrightarrow> Q (x + \<tau> *\<^sub>R c)\<rceil>"
  apply(subst picard_ivp.wp_g_orbit[of "\<lambda> t s. c" _ _ "1/(t + 1)" _ "(\<lambda> t x. x + t *\<^sub>R c)"])
  using constant_is_picard_ivp apply blast
  using line_solves_constant by auto

subsection{* Verification with differential invariants *}

text{* We derive the domain specific rules of differential dynamic logic (dL). In each subsubsection, 
we first derive the dL axioms (named below with two capital letters and ``D'' being the first one). 
This is done mainly to prove that there are minimal requirements in Isabelle to get the dL calculus. 
Then we prove the inference rules which are used in verification proofs.*}

subsubsection{* Differential Weakening *}
        
theorem DW:
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  apply(subst wp_nd_fun)+
  apply(rule nd_fun_ext)
  by auto

theorem dWeakening: 
assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
  using assms apply(subst wp_nd_fun)
  by(auto simp: le_fun_def)

subsubsection{* Differential Cut *}

lemma wp_g_orbit_etaD:
  assumes "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>" and "\<forall> r\<in>{t0--t}. x r \<in> g_orbital f T S t0 a G"
  shows "\<forall>r\<in>{t0--t}. C (x r)"
proof
  fix r assume "r \<in> {t0--t}"
  then have "x r \<in> g_orbital f T S t0 a G" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (g_orbital f T S t0 a G) \<longrightarrow> C y" 
    using assms(1) wp_nd_fun_etaD by fastforce
  ultimately show "C (x r)" by blast
qed

theorem DC:
  assumes "t0 \<in> T" and "interval T"
    and "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil> = \<eta>\<^sup>\<bullet>"
  shows "wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil> = wp ({[x\<acute>=f]T S @ t0 & \<lambda>s. G s \<and> C s}) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule nd_fun_ext, rule subset_antisym, simp_all)
  fix a
  show "g_orbital f T S t0 a G \<subseteq> g_orbital f T S t0 a (\<lambda>s. G s \<and> C s)"
  proof
    fix b assume "b \<in> g_orbital f T S t0 a G" 
    then obtain t::real and x where "t \<in> T" and x_solves:"(x solves_ode f) T S" and 
    "x t0 = a" and guard_x:"(\<forall>r\<in>{t0--t}. G (x r))" and "a \<in> S" and "b = x t"
      using assms(1) unfolding f2r_def by blast
    from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
      using assms(1) by (metis contra_subsetD ends_in_segment(1) subset_segment(1))
    also have "\<forall>r\<in>{t0--t}. r \<in> T"
      using assms(1,2) \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
    ultimately have "\<forall> r\<in>{t0--t}. x r \<in> g_orbital f T S t0 a G"
      using x_solves \<open>x t0 = a\<close> \<open>a \<in> S\<close> unfolding f2r_def by blast 
    from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_g_orbit_etaD assms(3) by blast
    thus "b \<in> g_orbital f T S t0 a (\<lambda> s. G s \<and> C s)" unfolding f2r_def
      using guard_x \<open>a \<in> S\<close> \<open>b = x t\<close> \<open>t \<in> T\<close> \<open>x t0 = a\<close> x_solves \<open>\<forall>r\<in>{t0--t}. r \<in> T\<close> by fastforce 
  qed
next show "\<And> a. g_orbital f T S t0 a (\<lambda> s. G s \<and> C s) \<subseteq> g_orbital f T S t0 a G" by auto
qed

theorem dCut:
  assumes "t0 \<in> T" and "interval T"
    and wp_C:"\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>C\<rceil>"
    and wp_Q:"\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>Q\<rceil>"
proof(subst wp_nd_fun, clarsimp)
  fix t::real and x::"real \<Rightarrow> 'a" assume "P (x t0)" and "t \<in> T"  and "x t0 \<in> S"
and x_solves:"(x solves_ode f)T S " and guard_x:"(\<forall> r \<in> {t0--t}. G (x r))"
  from guard_x have "\<forall>r\<in>{t0--t}.\<forall> \<tau>\<in>{t0--r}. G (x \<tau>)"
    using \<open>t0 \<in> T\<close> by (metis contra_subsetD ends_in_segment(1) subset_segment(1)) 
  also have "\<forall>r\<in>{t0--t}. r \<in> T"
    using \<open>t0 \<in> T\<close> \<open>interval T\<close> \<open>t \<in> T\<close> interval.closed_segment_subset_domain by blast
  ultimately have "\<forall>r\<in>{t0--t}. x r \<in> g_orbital f T S t0 (x t0) G"
    using x_solves \<open>x t0 \<in> S\<close> by blast
  from this have "\<forall>r\<in>{t0--t}. C (x r)" using wp_C \<open>P (x t0)\<close> by(subst (asm) wp_nd_fun, simp)
  hence "x t \<in> g_orbital f T S t0 (x t0) (\<lambda> s. G s \<and> C s)"
    using guard_x  \<open>t \<in> T\<close>  x_solves \<open>x t0 \<in> S\<close> \<open>\<forall>r\<in>{t0--t}. r \<in> T\<close> by fastforce
  from this \<open>P (x t0)\<close> and wp_Q show "Q (x t)"
    by(subst (asm) wp_nd_fun, simp)
qed

corollary dCut_interval:
  assumes "t0 \<le> t" and "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>C\<rceil>" 
    and "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & (\<lambda> s. G s \<and> C s)}) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="C" in dCut)
  using assms by(simp_all add: interval_def)

subsubsection{* Differential Invariant *}(* MODIFICATIONS REQUIRED: remove inf T*)

lemma DI_sufficiency:
  assumes "picard_ivp f T S L t0"
  shows "wp {[x\<acute>=f]T S @ t0 & G} \<lceil>Q\<rceil> \<le> wp \<lceil>G\<rceil> \<lceil>\<lambda>s. s \<in> S \<longrightarrow> Q s\<rceil>"
  apply(subst wp_nd_fun, subst wp_nd_fun, clarsimp)
  apply(erule_tac x="s" in allE, erule impE, rule_tac x="t0" in exI, simp_all)
  using assms picard_ivp.fixed_point_solves picard_ivp.init_time by metis

lemma 
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<lceil>G\<rceil> \<le> \<lceil>I'\<rceil>" and "t \<ge> 0"
    and "\<forall> x. (x solves_ode f){0..t} S \<longrightarrow> I (x 0) \<longrightarrow>
 (\<forall> t \<ge> 0. (\<forall>r\<in>{0--t}. I' (x r)) \<longrightarrow> (I (x t)))"
  shows "\<lceil>I\<rceil> \<le> wp ({[x\<acute>=f]{0..t} S @ 0 & G}) \<lceil>I\<rceil>"
  using assms apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff) apply clarify
  apply(erule_tac x="x" in allE)
  apply(erule impE, simp)+
  apply(erule_tac x="ta" in allE)
  by simp

definition pderivative :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> (real \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 
'a set \<Rightarrow> bool" ("(_)/ is'_pderivative'_of (_)/ with'_respect'_to (_) (_) (_)" [70, 65] 61) where
"I' is_pderivative_of I with_respect_to f T S \<equiv> bdd_below T \<and> (\<forall> x. (x solves_ode f)T S \<longrightarrow> 
I (x (Inf T)) \<longrightarrow> (\<forall> t \<in> T. (\<forall>r\<in>{(Inf T)--t}. I' (x r)) \<longrightarrow> (I (x t))))"

lemma dInvariant:
  assumes "\<lceil>G\<rceil> \<le> \<lceil>I'\<rceil>" and "I' is_pderivative_of I with_respect_to f T S"
  shows "\<lceil>I\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>I\<rceil>"
  using assms unfolding pderivative_def apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff)
  by clarsimp

lemma dInvariant':
  assumes "I' is_pderivative_of I with_respect_to f T S"
    and "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>G\<rceil> \<le> \<lceil>I'\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>Q\<rceil>"
  using assms unfolding pderivative_def apply(subst wp_nd_fun)
  apply(subst le_p2ndf_iff)
  by clarsimp

lemma invariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode f)T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s = 0"])
  using assms apply(simp, simp add: pderivative_def)
proof(clarify)
  fix x and t 
  assume x_ivp:"(x solves_ode f) T S" "\<theta> (x (Inf T)) = 0"  
    and tHyp:"t \<in> T" and eq0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) = 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R 0)) 
    (at r within {(Inf T)--t})" using eq0 by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R 0) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  thus "\<theta> (x t) = 0" 
    using x_ivp(2) by (metis right_minus_eq scale_zero_right)
qed

corollary invariant_eq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply simp
  apply(rule invariant_eq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_eq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode f) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s = 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s = 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s = 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s = 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s = 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
   apply(rule_tac \<nu>="\<nu>" in invariant_eq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode f)T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp add: pderivative_def)
proof(clarify)
  fix x and t
  assume x_ivp:"\<theta> (x (Inf T)) \<ge> 0" "(x solves_ode f) T S" 
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<ge> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(2) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T)) " by force 
  thus "0 \<le> \<theta> (x t)" by (simp add: \<open>Inf T \<le> t\<close> ge0 x_ivp(1))
qed

corollary invariant_geq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_geq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_geq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode f) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<ge> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<ge> 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_geq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode f)T S \<longrightarrow> (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp add: pderivative_def)
proof(clarify)
  fix x and t
  assume x_ivp:"\<theta> (x (Inf T)) \<le> 0" "(x solves_ode f) T S" 
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<le> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(2) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T))" by force 
  thus "\<theta> (x t) \<le> 0" using \<open>(Inf T) \<le> t\<close> ge0 x_ivp(1)
    by (metis add_decreasing2 ge_iff_diff_ge_0 split_scaleR_neg_le)
qed

corollary invariant_leq_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_leq_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_leq_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode f) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s \<le> 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s \<le> 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_leq_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode f)T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<ge> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<ge> 0"])
  using assms apply(simp, simp add: pderivative_def)
proof(clarify)
  fix x and t
  assume x_ivp:"(x solves_ode f) T S" "\<theta> (x (Inf T)) > 0"
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<ge> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  from this obtain r where 
    "r \<in> {(Inf T)--t} \<and> \<theta> (x t)= (t - Inf T) *\<^sub>R \<nu> (x r) + \<theta> (x (Inf T)) " by force 
  thus "0 < \<theta> (x t)"  
    by (metis \<open>(Inf T) \<le> t\<close> ge0 x_ivp(2) Groups.add_ac(2) add_mono_thms_linordered_field(3) 
        ge_iff_diff_ge_0 monoid_add_class.add_0_right scaleR_nonneg_nonneg)
qed

corollary invariant_above_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_above_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_above_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real" and \<nu>::"'a \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode f) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s > 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<ge> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. \<theta> s > 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s > 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s > 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_above_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls  by auto

lemma invariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes nuHyp:"\<forall> x. (x solves_ode f)T S \<longrightarrow>  (\<forall> t \<in> T. \<forall> r \<in> {(Inf T)--t}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {(Inf T)--t}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. (\<nu> s) \<le> 0\<rceil>" and "bdd_below T"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]T S @ (Inf T) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(rule dInvariant [of _ "\<lambda> s. \<nu> s \<le> 0"])
  using assms apply(simp, simp add: pderivative_def)
proof(clarify)
  fix x and t
  assume x_ivp:"(x solves_ode f) T S" "\<theta> (x (Inf T)) < 0"
    and tHyp:"t \<in> T" and ge0:"\<forall>r\<in>{Inf T--t}. \<nu> (x r) \<le> 0"
  hence "(Inf T) \<le> t" by (simp add: \<open>bdd_below T\<close> cInf_lower) 
  have "\<forall> r \<in> {(Inf T)--t}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) 
    (at r within {(Inf T)--t})" using nuHyp x_ivp(1) and tHyp by auto
  then have "\<exists>r\<in>{(Inf T)--t}. \<theta> (x t)- \<theta> (x (Inf T)) = (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r))) (t - (Inf T))" 
    by(rule_tac closed_segment_mvt, auto simp: \<open>(Inf T) \<le> t\<close>)
  thus "\<theta> (x t) < 0"  using \<open>(Inf T) \<le> t\<close> ge0 x_ivp(2)
    by (metis add_mono_thms_linordered_field(3) diff_gt_0_iff_gt ge_iff_diff_ge_0 linorder_not_le 
        monoid_add_class.add_0_left monoid_add_class.add_0_right split_scaleR_neg_le) 
qed

corollary invariant_below_0_interval:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall> x. (x solves_ode f){t0..t} S \<longrightarrow> (\<forall> \<tau> \<in> {t0..t}. \<forall> r \<in> {t0..\<tau>}. 
  ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R (\<nu> (x r)))) (at r within {t0..\<tau>}))"
    and "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>"
  apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ (Inf {t0..t}) & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
   apply(subgoal_tac "Inf {t0..t} = t0", simp)
  using \<open>t0 \<le> t\<close> apply(simp add: closed_segment_eq_real_ivl)
  apply(rule invariant_below_0[of _ "{t0..t}" _ _ \<nu>])
  using assms by(auto simp: closed_segment_eq_real_ivl)

theorem dInvariant_below_0:
  fixes \<theta>::"'a::banach \<Rightarrow> real"
  assumes "\<forall>x. (x solves_ode f) {t0..t} S \<longrightarrow> 
  (\<forall>\<tau>\<in>{t0..t}. \<forall>r\<in>{t0..\<tau>}. ((\<lambda>\<tau>. \<theta> (x \<tau>)) has_derivative (\<lambda>\<tau>. \<tau> *\<^sub>R \<nu> (x r))) (at r within {t0..\<tau>}))"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. \<theta> s < 0\<rceil>" "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> \<lceil>Q\<rceil>" "\<lceil>G\<rceil> \<le> \<lceil>\<lambda>s. \<nu> s \<le> 0\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  using \<open>t0 \<le> t\<close> apply(rule_tac C="\<lambda>s. \<theta> s < 0" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. \<theta> s < 0\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. \<theta> s < 0\<rceil>")
  using impls apply(subst (asm) wp_nd_fun, subst wp_nd_fun) apply auto[1]
  apply(rule_tac \<nu>="\<nu>" in invariant_below_0_interval)
  using assms(1,4,5) apply(simp, simp, simp)
  apply(rule dWeakening) using impls by auto

lemma invariant_meet:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>"
  using assms by(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun, subst wp_nd_fun, simp, blast)

theorem dInvariant_meet:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<and> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<and> I2 s\<rceil>")
  using impls apply(transfer, simp add: le_fun_def) apply auto[1]
    apply(rule invariant_meet)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by simp

lemma invariant_join:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I1\<rceil>"
    and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>I2\<rceil>"
  shows "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> wp ({[x\<acute>=f]T S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>"
  using assms by(subst (asm) wp_nd_fun, subst (asm) wp_nd_fun, subst wp_nd_fun, simp)

theorem dInvariant_join:
  assumes "\<lceil>I1\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I1\<rceil>" and "\<lceil>I2\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>I2\<rceil>"
    and impls:"\<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>" "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> \<lceil>Q\<rceil>" and "t0 \<le> t"
  shows "\<lceil>P\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>Q\<rceil>"
  apply(rule_tac C="\<lambda>s. I1 s \<or> I2 s" in dCut_interval, simp add: \<open>t0 \<le> t\<close>)
   apply(subgoal_tac "\<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil> \<le> wp ({[x\<acute>=f]{t0..t} S @ t0 & G}) \<lceil>\<lambda>s. I1 s \<or> I2 s\<rceil>")
  using impls apply(transfer, simp add: le_fun_def) apply auto[1]
    apply(rule invariant_join)
  using assms(1,2,5) apply(simp, simp)
  apply(rule dWeakening)
  using impls by auto

end