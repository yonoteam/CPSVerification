(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open>PID Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory PID_Examples
  imports "../HS_VC_Spartan"

begin

abbreviation "time_counter_vars \<equiv> {''t'', ''time'', ''counter''}"

typedef time_counter = time_counter_vars
  morphisms to_str to_var
  by blast

notation to_var ("\<downharpoonright>\<^sub>V") 

lemma card_time_counter: "CARD(time_counter) = 3"
  using type_definition.card type_definition_time_counter by fastforce

instance time_counter::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV time_counter_vars])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

lemma time_counter_univ: "(UNIV::time_counter set) = {\<downharpoonright>\<^sub>V''t'', \<downharpoonright>\<^sub>V''time'' , \<downharpoonright>\<^sub>V''counter''}"
  by auto (metis to_str to_str_inverse insertE singletonD) 

lemma time_counter_exhaust: "x = \<downharpoonright>\<^sub>V''t'' \<or> x = \<downharpoonright>\<^sub>V''time'' \<or> x = \<downharpoonright>\<^sub>V''counter''"
  using time_counter_univ by auto

lemma time_counter_sum:
  fixes f :: "time_counter \<Rightarrow> ('a::banach)"
  shows "(\<Sum>(i::time_counter)\<in>UNIV. f i) = f (\<downharpoonright>\<^sub>V''t'') + f (\<downharpoonright>\<^sub>V''time'') + f (\<downharpoonright>\<^sub>V''counter'')"
  unfolding time_counter_univ by (simp add: to_var_inject)

abbreviation val_time_counter :: "real^time_counter \<Rightarrow> string \<Rightarrow> real" (infixl "\<restriction>\<^sub>V" 90)
  where "s\<restriction>\<^sub>Vstring \<equiv> s $ (to_var string)"

lemma time_counter_induct: "P (\<downharpoonright>\<^sub>V''t'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''time'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''counter'') \<Longrightarrow> \<forall>i. P i"
  using time_counter_exhaust by metis

abbreviation time_counter_vec_field :: "real^time_counter \<Rightarrow> real^time_counter" ("f")
  where "f s \<equiv> (\<chi> i. if i = \<downharpoonright>\<^sub>V''t'' then 1 else 0)"

abbreviation time_counter_flow :: "real \<Rightarrow> real^time_counter \<Rightarrow> real^time_counter" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = \<downharpoonright>\<^sub>V''t'' then t + s\<restriction>\<^sub>V''t'' else s $ i)"

lemma local_lipschitz_time_counter_vec_field: "local_lipschitz UNIV UNIV (\<lambda>t. f)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=1 in exI)
  apply(clarsimp simp: norm_vec_def L2_set_def)
  unfolding time_counter_sum by (simp add: to_var_inject)

lemma local_flow_time_counter: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: vec_eq_iff local_lipschitz_time_counter_vec_field)
   apply(rule time_counter_induct, simp_all add: to_var_inject)
  using time_counter_exhaust by (auto intro!: poly_derivatives)

lemma time_loop_verif: "(\<lambda>s. s\<restriction>\<^sub>V''t''=0) \<le> |
   LOOP
    (IF (\<lambda>s. s\<restriction>\<^sub>V''t'' = 0.01) THEN 
      (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0))
    ELSE
      (x\<acute>= f & (\<lambda>s. s\<restriction>\<^sub>V''t'' \<le> 0.01)))
   INV (\<lambda>s. s\<restriction>\<^sub>V''t''\<le> 0.01)] 
  (\<lambda>s. s\<restriction>\<^sub>V''t'' \<le> 0.01)"
  apply(rule fbox_loopI)
    apply(clarsimp simp: to_var_inject)
   apply(clarsimp simp: to_var_inject)
   apply(clarsimp simp: to_var_inject)
  apply(subst local_flow.fbox_g_ode_subset[OF local_flow_time_counter])
  apply simp_all
  done

lemma counter_loop_verif: "(\<lambda>s. s\<restriction>\<^sub>V''counter''=0 \<and> s\<restriction>\<^sub>V''t''=0 \<and> s\<restriction>\<^sub>V''time''=0) \<le> |
   LOOP
    (IF (\<lambda>s. s\<restriction>\<^sub>V''t'' = 0.01) THEN 
      (\<downharpoonright>\<^sub>V''time'' ::= (\<lambda>s. s\<restriction>\<^sub>V''time'' + s\<restriction>\<^sub>V''t''));
      (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0));
      (\<downharpoonright>\<^sub>V''counter'' ::= (\<lambda>s. s\<restriction>\<^sub>V''counter'' + 1))
    ELSE
      (x\<acute>= f & (\<lambda>s. s\<restriction>\<^sub>V''t'' \<le> 0.01)))
   INV (\<lambda>s. s\<restriction>\<^sub>V''time'' = 0.01* s\<restriction>\<^sub>V''counter'' \<and> s\<restriction>\<^sub>V''t'' \<le> 0.01)] 
  (\<lambda>s. s\<restriction>\<^sub>V''time'' = 0.01* s\<restriction>\<^sub>V''counter'')"
  apply(rule fbox_loopI)
    apply(clarsimp simp: to_var_inject)
   apply(clarsimp simp: to_var_inject)
  apply(simp only: fbox_if_then_else, safe)
   apply(clarsimp simp: to_var_inject)
  apply(subst local_flow.fbox_g_ode_subset[OF local_flow_time_counter])
  apply(auto simp: to_var_inject)
  done

no_notation to_var ("\<downharpoonright>\<^sub>V") 
        and val_time_counter (infixl "\<restriction>\<^sub>V" 90)
        and time_counter_vec_field ("f")
        and time_counter_flow ("\<phi>")


subsection \<open> PI controller on kinematics \<close>

abbreviation "kin_PI_strs \<equiv> {''t'', ''r'', ''v'', ''T'', ''roll'', ''error'', 
  ''roll_rate'', ''error_sum'', ''veri_test'', ''counter''}"

typedef kin_PI_vars = kin_PI_strs
  morphisms to_str to_var
  by blast

notation to_var ("\<downharpoonright>\<^sub>V")

abbreviation "kin_PI_terms \<equiv> {\<downharpoonright>\<^sub>V''t'', \<downharpoonright>\<^sub>V''r'', \<downharpoonright>\<^sub>V''v'', \<downharpoonright>\<^sub>V''T'', \<downharpoonright>\<^sub>V''roll'', \<downharpoonright>\<^sub>V''error'', 
  \<downharpoonright>\<^sub>V''roll_rate'', \<downharpoonright>\<^sub>V''error_sum'', \<downharpoonright>\<^sub>V''veri_test'', \<downharpoonright>\<^sub>V''counter''}"

lemma number_of_program_vars: "CARD(kin_PI_vars) = 10"
  using type_definition.card type_definition_kin_PI_vars by fastforce

instance kin_PI_vars::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV kin_PI_strs])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

abbreviation val_kin_PI :: "real^kin_PI_vars \<Rightarrow> string \<Rightarrow> real" (infixl "\<restriction>\<^sub>V" 90)
  where "s\<restriction>\<^sub>Vstring \<equiv> s $ (to_var string)"

lemma kin_PI_vars_univ: "(UNIV::kin_PI_vars set) = kin_PI_terms"
  by auto (metis kin_PI_vars.to_str kin_PI_vars.to_str_inverse insertE singletonD) 

lemma kin_PI_vars_exhaust: "x = \<downharpoonright>\<^sub>V''t'' \<or> x = \<downharpoonright>\<^sub>V''r'' \<or> x = \<downharpoonright>\<^sub>V''v'' \<or> x = \<downharpoonright>\<^sub>V''T'' 
  \<or> x = \<downharpoonright>\<^sub>V''roll'' \<or> x = \<downharpoonright>\<^sub>V''roll_rate'' \<or> x = \<downharpoonright>\<^sub>V''error'' \<or> x = \<downharpoonright>\<^sub>V''error_sum'' 
  \<or> x = \<downharpoonright>\<^sub>V''veri_test'' \<or> x = \<downharpoonright>\<^sub>V''counter''"
  using kin_PI_vars_univ by auto

lemma kin_PI_vars_sum:
  fixes f :: "kin_PI_vars \<Rightarrow> ('a::banach)"
  shows "(\<Sum>i\<in>UNIV. f i) = f (\<downharpoonright>\<^sub>V''t'') + f (\<downharpoonright>\<^sub>V''r'') + f (\<downharpoonright>\<^sub>V''v'') + f (\<downharpoonright>\<^sub>V''T'') 
  + f (\<downharpoonright>\<^sub>V''roll'') + f (\<downharpoonright>\<^sub>V''roll_rate'') + f (\<downharpoonright>\<^sub>V''error'') + f (\<downharpoonright>\<^sub>V''error_sum'') 
  + f (\<downharpoonright>\<^sub>V''veri_test'') + f (\<downharpoonright>\<^sub>V''counter'')"
  unfolding kin_PI_vars_univ by (simp add: to_var_inject)

lemma kin_PI_vars_induct: "P (\<downharpoonright>\<^sub>V''t'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''r'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''v'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''T'') 
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''roll'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''roll_rate'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''error'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''error_sum'') 
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''veri_test'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''counter'') \<Longrightarrow> \<forall>i. P i"
  using kin_PI_vars_exhaust by metis

lemma kin_PI_vars_eq:
  "(s1 = s2) \<longleftrightarrow> (s1\<restriction>\<^sub>V''t'' = s2\<restriction>\<^sub>V''t'' \<and> s1\<restriction>\<^sub>V''r'' = s2\<restriction>\<^sub>V''r'' \<and> s1\<restriction>\<^sub>V''v'' = s2\<restriction>\<^sub>V''v'' \<and>
  s1\<restriction>\<^sub>V''T'' = s2\<restriction>\<^sub>V''T'' \<and> s1\<restriction>\<^sub>V''roll'' = s2\<restriction>\<^sub>V''roll'' \<and> s1\<restriction>\<^sub>V''roll_rate'' = s2\<restriction>\<^sub>V''roll_rate'' \<and>
  s1\<restriction>\<^sub>V''error'' = s2\<restriction>\<^sub>V''error'' \<and> s1\<restriction>\<^sub>V''error_sum'' = s2\<restriction>\<^sub>V''error_sum'' \<and> 
  s1\<restriction>\<^sub>V''veri_test'' = s2\<restriction>\<^sub>V''veri_test'' \<and> s1\<restriction>\<^sub>V''counter'' = s2\<restriction>\<^sub>V''counter'')"
  apply(clarsimp simp: vec_eq_iff, rule iffI, force)
  by (rule kin_PI_vars_induct, auto)

abbreviation kin_PI_vec_field :: "real^kin_PI_vars \<Rightarrow> real^kin_PI_vars" ("f")
  where "f s \<equiv> (\<chi> i. if i = \<downharpoonright>\<^sub>V''t'' then 1 else 
                    (if i = \<downharpoonright>\<^sub>V''r'' then s\<restriction>\<^sub>V''v'' else 
                    (if i = \<downharpoonright>\<^sub>V''v'' then s\<restriction>\<^sub>V''T'' else 0)))"

abbreviation kin_PI_flow :: "real \<Rightarrow> real^kin_PI_vars \<Rightarrow> real^kin_PI_vars" ("\<phi>")
  where "\<phi> t s \<equiv> 
  (\<chi> i. if i = \<downharpoonright>\<^sub>V''t'' then t + s\<restriction>\<^sub>V''t'' else 
       (if i = \<downharpoonright>\<^sub>V''r'' then (s\<restriction>\<^sub>V''T'')*t^2/2 + (s\<restriction>\<^sub>V''v'')*t + (s\<restriction>\<^sub>V''r'') else
       (if i = \<downharpoonright>\<^sub>V''v'' then (s\<restriction>\<^sub>V''T'')*t + (s\<restriction>\<^sub>V''v'') else s$i)))"

lemma local_lipschitz_kin_PI_vec_field: "local_lipschitz UNIV UNIV (\<lambda>t. f)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=1 in exI)
  apply(clarsimp simp: norm_vec_def L2_set_def)
  unfolding kin_PI_vars_sum by (simp add: to_var_inject)

lemma local_flow_kin_PI: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: vec_eq_iff local_lipschitz_kin_PI_vec_field)
  apply(rule kin_PI_vars_induct, simp_all add: to_var_inject)
  by (auto intro!: poly_derivatives)

lemma the_inv_real_Suc [simp]: "the_inv real (real m + 1) = Suc m"
  by (metis Groups.add_ac(2) Num.of_nat_simps(3) inj_def of_nat_eq_iff the_inv_f_f)

lemma "real \<circ> the_inv real = id"
  oops

lemma "the_inv real m = 0 \<Longrightarrow> m \<in> \<nat>"
proof(subgoal_tac "m = 0", simp)
  assume h0: "the_inv real m = 0"
  have "0 = real 0"
    by simp
  also have "... = real (the_inv real m)"
    using h0 arg_cong[of _ _ real] by simp
  also have "... = m"
    oops


lemma inNatsD:
  assumes "(n::real) \<in> \<nat>"
  shows "n = 0 \<or> n \<ge> 1"
    and "\<exists>k::nat. the_inv of_nat n = k \<and> ((k = 0) \<or> (\<exists>m. k = Suc m))"
proof-
  obtain n'::nat where obs: "n = real n'"
    using assms unfolding Nats_def by blast
  have "n' = 0 \<or> n' \<ge> 1"
    by auto
  thus "n = 0 \<or> n \<ge> 1"
    using obs by (simp add: real_of_nat_ge_one_iff)
  then show "\<exists>k::nat. the_inv of_nat n = k \<and> ((k = 0) \<or> (\<exists>m. k = Suc m))"
    using not0_implies_Suc by fastforce
qed


lemma PI_controller_invariants:
  shows "(\<lambda>s. s\<restriction>\<^sub>V''t''=0 \<and> s\<restriction>\<^sub>V''r''=0 \<and> s\<restriction>\<^sub>V''v''=0 \<and> s\<restriction>\<^sub>V''T''=1 \<and> s\<restriction>\<^sub>V''roll'' = 0 \<and> s\<restriction>\<^sub>V''roll_rate''=0 \<and> 
  s\<restriction>\<^sub>V''error'' = 0 \<and> s\<restriction>\<^sub>V''error_sum''=0 \<and> s\<restriction>\<^sub>V''veri_test''=0 \<and> s\<restriction>\<^sub>V''counter''=0) \<le> 
  |LOOP
    (IF (\<lambda>s. s\<restriction>\<^sub>V''t'' = dt) THEN 
      \<comment> \<open>CONTROL\<close>
        (\<downharpoonright>\<^sub>V''error'' ::= (\<lambda>s. s\<restriction>\<^sub>V''r'' - s\<restriction>\<^sub>V''roll''));
        (\<downharpoonright>\<^sub>V''error_sum'' ::= (\<lambda>s. s\<restriction>\<^sub>V''error_sum'' + s\<restriction>\<^sub>V''error''));
        (\<downharpoonright>\<^sub>V''T'' ::= (\<lambda>s. Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum''));
        (\<downharpoonright>\<^sub>V''roll'' ::= (\<lambda>s. s\<restriction>\<^sub>V''r''));
        (\<downharpoonright>\<^sub>V''roll_rate'' ::= (\<lambda>s. s\<restriction>\<^sub>V''v''));
        (\<downharpoonright>\<^sub>V''veri_test'' ::= (\<lambda>s. s\<restriction>\<^sub>V''veri_test'' + s\<restriction>\<^sub>V''error_sum''));
        (\<downharpoonright>\<^sub>V''counter'' ::= (\<lambda>s. s\<restriction>\<^sub>V''counter'' + 1));
        (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0))
     ELSE 
      \<comment> \<open>DYNAMICS\<close>
        (x\<acute>= f & (\<lambda>s. s\<restriction>\<^sub>V''t'' \<le> dt)))
   INV (\<lambda>s. (s\<restriction>\<^sub>V''counter'' \<ge> 1 \<longrightarrow> s\<restriction>\<^sub>V''T'' = Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum'') \<and>
  s\<restriction>\<^sub>V''counter'' \<in> \<nat> \<and> s\<restriction>\<^sub>V''v'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll_rate'' \<and>
  s\<restriction>\<^sub>V''r'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t''^2/2 + s\<restriction>\<^sub>V''roll_rate'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll'')] 
  (\<lambda>s. (s\<restriction>\<^sub>V''counter'' \<ge> 1 \<longrightarrow> s\<restriction>\<^sub>V''T'' = Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum'') \<and> 
    s\<restriction>\<^sub>V''counter'' \<in> \<nat> \<and> s\<restriction>\<^sub>V''v'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll_rate'' \<and>
    s\<restriction>\<^sub>V''r'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t''^2/2 + s\<restriction>\<^sub>V''roll_rate'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll'')"
  apply(rule fbox_loopI)
    apply (clarsimp simp: to_var_inject)
   apply (clarsimp simp: to_var_inject)
  apply(subst fbox_if_then_else, clarify, rule conjI)
   apply (clarsimp simp: to_var_inject power2_sum)
  apply(subst local_flow.fbox_g_ode_subset[OF local_flow_kin_PI], simp)
  apply(clarsimp simp: le_fun_def to_var_inject power2_sum)
   apply(force simp: field_simps)
  done

lemma PI_controller_invariants2: 
  assumes "Prop = -6" and "Integr = -0.1" and "dt = 0.01"
  shows "(\<lambda>s. s\<restriction>\<^sub>V''t''=0 \<and> s\<restriction>\<^sub>V''v'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll_rate'' \<and> s\<restriction>\<^sub>V''counter'' \<in> \<nat> \<and>
    s\<restriction>\<^sub>V''r'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t''^2/2 + s\<restriction>\<^sub>V''roll_rate'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll'' \<and>
    s\<restriction>\<^sub>V''T''= Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum'' \<and> s\<restriction>\<^sub>V''error_sum'' - s\<restriction>\<^sub>V''error'' \<le> 2/10 \<and>
    s\<restriction>\<^sub>V''roll_rate'' = Prop * dt * (s\<restriction>\<^sub>V''error_sum'' - s\<restriction>\<^sub>V''error'') + Integr * dt^2 * (s\<restriction>\<^sub>V''veri_test'' - s\<restriction>\<^sub>V''error_sum'')) \<le> 
  |LOOP
    (IF (\<lambda>s. s\<restriction>\<^sub>V''t'' = dt) THEN 
      \<comment> \<open>CONTROL\<close>
        (\<downharpoonright>\<^sub>V''error'' ::= (\<lambda>s. s\<restriction>\<^sub>V''r'' - s\<restriction>\<^sub>V''roll''));
        (\<downharpoonright>\<^sub>V''error_sum'' ::= (\<lambda>s. s\<restriction>\<^sub>V''error_sum'' + s\<restriction>\<^sub>V''error''));
        (\<downharpoonright>\<^sub>V''T'' ::= (\<lambda>s. Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum''));
        (\<downharpoonright>\<^sub>V''roll'' ::= (\<lambda>s. s\<restriction>\<^sub>V''r''));
        (\<downharpoonright>\<^sub>V''roll_rate'' ::= (\<lambda>s. s\<restriction>\<^sub>V''v''));
        (\<downharpoonright>\<^sub>V''veri_test'' ::= (\<lambda>s. s\<restriction>\<^sub>V''veri_test'' + s\<restriction>\<^sub>V''error_sum''));
        (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0))
     ELSE 
      \<comment> \<open>DYNAMICS\<close>
        (x\<acute>= f & (\<lambda>s. 0 \<le> s\<restriction>\<^sub>V''t'' \<and> s\<restriction>\<^sub>V''t'' \<le> dt)))
   INV (\<lambda>s. s\<restriction>\<^sub>V''T'' = Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum'' \<and>
    s\<restriction>\<^sub>V''roll_rate'' = Prop * dt * (s\<restriction>\<^sub>V''error_sum'' - s\<restriction>\<^sub>V''error'') 
      + Integr * dt^2 * (s\<restriction>\<^sub>V''veri_test'' - s\<restriction>\<^sub>V''error_sum'') \<and>
    s\<restriction>\<^sub>V''counter'' \<in> \<nat> \<and> s\<restriction>\<^sub>V''v'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll_rate'' \<and>
    s\<restriction>\<^sub>V''r'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t''^2/2 + s\<restriction>\<^sub>V''roll_rate'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll'')] 
  (\<lambda>s. s\<restriction>\<^sub>V''T'' = Prop * s\<restriction>\<^sub>V''error'' + Integr * dt * s\<restriction>\<^sub>V''error_sum'' \<and> 
    s\<restriction>\<^sub>V''counter'' \<in> \<nat> \<and> s\<restriction>\<^sub>V''v'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll_rate'' \<and>
    s\<restriction>\<^sub>V''r'' = s\<restriction>\<^sub>V''T'' * s\<restriction>\<^sub>V''t''^2/2 + s\<restriction>\<^sub>V''roll_rate'' * s\<restriction>\<^sub>V''t'' + s\<restriction>\<^sub>V''roll'')"
  apply(rule fbox_loopI)
    apply (clarsimp simp: to_var_inject)
   apply (clarsimp simp: to_var_inject)
  apply(subst fbox_if_then_else, clarify, rule conjI)
   apply (force simp: to_var_inject power2_eq_square field_simps)
  apply(subst local_flow.fbox_g_ode_subset[OF local_flow_kin_PI], simp)
  apply(clarsimp simp: le_fun_def to_var_inject power2_sum)
   apply(force simp: field_simps)
  done



end