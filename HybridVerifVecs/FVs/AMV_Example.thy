(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> AMV verification \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our
verification components.\<close>

theory AMV_Example
  imports 
    "../HS_VC_Spartan" 
    Triangle.Angles

begin

definition "no_modfs X i \<equiv> \<forall>k. (\<lambda>s. s$i = k) \<le> |X] (\<lambda>s. s$i = k)"

lemma no_modfs_inv:
  "no_modfs X i \<Longrightarrow> (\<lambda>s. Q (s$i)) \<le> |X] (\<lambda>s. Q (s$i))"
  unfolding fbox_def no_modfs_def by (clarsimp simp: le_fun_def)

subsubsection \<open> Type of variables \<close>

(* Continuous Variables
  AMV's position vector: (x, y)
  AMV's velocity vector: (vx, vy)
  AMV's acceleration vector: (ax, ay)
  angle of AMV's velocity vector with horizontal: phi \<in> [-\<pi>,\<pi>]
  speed of AMV's: speed
  time: t
  [Therefore:
    s^2 = vx^2 + vy^2
    (vx, vy) = (speed * cos phi, speed * sgn phi * sin phi)  *)
abbreviation "amv_cstrs \<equiv> {''x'', ''y'', ''vx'', ''vy'', ''ax'', ''ay'', 
  ''phi'', ''speed'', ''t''}"

(* Discrete Variables 
  Speed Set Point: sSP
  Heading Set Point: hSP (radians)
  Longitudinal Acceleration Force: fl (colinear with velocity vector)
  Radial Acceleration Force: fr (perpendicular to fl)
  AMV's mode: mode
    operator control          - OCM
    main operating mode       - MOM
    high caution mode         - HCM
    collision avoidance mode  - CAM *)
abbreviation "amv_dstrs \<equiv> {''sSP'', ''hSP'', ''fl'', ''fr'', ''mode''}" 

(* all variables *)
abbreviation "amv_strs \<equiv> {''x'', ''y'', ''vx'', ''vy'', ''ax'', ''ay'', 
  ''phi'', ''speed'', ''t'', ''sSP'', ''hSP'', ''fl'', ''fr'', ''mode''}"

(* type of variables *)
typedef AMV = amv_strs
  morphisms to_str to_var
  by blast

notation to_var ("\<downharpoonright>\<^sub>V")

abbreviation "amv_terms \<equiv> {\<downharpoonright>\<^sub>V''x'', \<downharpoonright>\<^sub>V''y'', \<downharpoonright>\<^sub>V''vx'', \<downharpoonright>\<^sub>V''vy'', \<downharpoonright>\<^sub>V''ax'', \<downharpoonright>\<^sub>V''ay'', 
  \<downharpoonright>\<^sub>V''phi'', \<downharpoonright>\<^sub>V''speed'', \<downharpoonright>\<^sub>V''t'', \<downharpoonright>\<^sub>V''sSP'', \<downharpoonright>\<^sub>V''hSP'', \<downharpoonright>\<^sub>V''fl'', \<downharpoonright>\<^sub>V''fr'', \<downharpoonright>\<^sub>V''mode''}"

lemma number_of_program_vars: "CARD(AMV) = 14"
  using type_definition.card type_definition_AMV by fastforce

instance AMV::finite
  apply(standard, subst bij_betw_finite[of to_str UNIV amv_strs])
   apply(rule bij_betwI')
     apply (simp add: to_str_inject)
  using to_str apply blast
   apply (metis to_var_inverse UNIV_I)
  by simp

abbreviation val_AMV :: "real^AMV \<Rightarrow> string \<Rightarrow> real" (infixl "\<restriction>\<^sub>V" 90)
  where "s\<restriction>\<^sub>Vstring \<equiv> s $ (to_var string)"

lemma AMV_univ: "(UNIV::AMV set) = amv_terms"
  by auto (metis AMV.to_str AMV.to_str_inverse insertE singletonD) 

lemma AMV_exhaust: "x = \<downharpoonright>\<^sub>V''x'' \<or> x = \<downharpoonright>\<^sub>V''y'' \<or> x = \<downharpoonright>\<^sub>V''vx'' \<or> x = \<downharpoonright>\<^sub>V''vy'' 
  \<or> x = \<downharpoonright>\<^sub>V''ax'' \<or> x = \<downharpoonright>\<^sub>V''ay'' \<or> x = \<downharpoonright>\<^sub>V''phi'' \<or> x = \<downharpoonright>\<^sub>V''speed'' 
  \<or> x = \<downharpoonright>\<^sub>V''t'' \<or> x=\<downharpoonright>\<^sub>V''sSP'' \<or> x=\<downharpoonright>\<^sub>V''hSP'' \<or> x=\<downharpoonright>\<^sub>V''fl'' \<or> x=\<downharpoonright>\<^sub>V''fr'' \<or> x=\<downharpoonright>\<^sub>V''mode''"
  using AMV_univ by auto

lemma AMV_sum:
  fixes f :: "AMV \<Rightarrow> ('a::banach)"
  shows "(\<Sum>i\<in>UNIV. f i) = f (\<downharpoonright>\<^sub>V''x'') + f (\<downharpoonright>\<^sub>V''y'') + f (\<downharpoonright>\<^sub>V''vx'') + f (\<downharpoonright>\<^sub>V''vy'') 
  + f (\<downharpoonright>\<^sub>V''ax'') + f (\<downharpoonright>\<^sub>V''ay'') + f (\<downharpoonright>\<^sub>V''phi'') + f (\<downharpoonright>\<^sub>V''speed'') + f (\<downharpoonright>\<^sub>V''t'')
  + f (\<downharpoonright>\<^sub>V''sSP'') + f (\<downharpoonright>\<^sub>V''hSP'') + f (\<downharpoonright>\<^sub>V''fl'') + f (\<downharpoonright>\<^sub>V''fr'') + f (\<downharpoonright>\<^sub>V''mode'')"
  unfolding AMV_univ by (simp add: to_var_inject)

lemma AMV_induct: "P (\<downharpoonright>\<^sub>V''x'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''y'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''vx'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''vy'') 
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''ax'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''ay'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''phi'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''speed'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''t'')
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''sSP'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''hSP'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''fl'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''fr'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''mode'')
  \<Longrightarrow> \<forall>i. P i"
  using AMV_exhaust by metis

lemma AMV_eq:
  "(s1 = s2) \<longleftrightarrow> (s1\<restriction>\<^sub>V''x'' = s2\<restriction>\<^sub>V''x'' \<and> s1\<restriction>\<^sub>V''y'' = s2\<restriction>\<^sub>V''y'' \<and> s1\<restriction>\<^sub>V''vx'' = s2\<restriction>\<^sub>V''vx'' \<and>
  s1\<restriction>\<^sub>V''vy'' = s2\<restriction>\<^sub>V''vy'' \<and> s1\<restriction>\<^sub>V''ax'' = s2\<restriction>\<^sub>V''ax'' \<and> s1\<restriction>\<^sub>V''ay'' = s2\<restriction>\<^sub>V''ay'' \<and>
  s1\<restriction>\<^sub>V''phi'' = s2\<restriction>\<^sub>V''phi'' \<and> s1\<restriction>\<^sub>V''speed'' = s2\<restriction>\<^sub>V''speed'' \<and> s1\<restriction>\<^sub>V''t'' = s2\<restriction>\<^sub>V''t'' \<and>
  s1\<restriction>\<^sub>V''sSP'' = s2\<restriction>\<^sub>V''sSP'' \<and> s1\<restriction>\<^sub>V''hSP'' = s2\<restriction>\<^sub>V''hSP'' \<and> 
  s1\<restriction>\<^sub>V''fl'' = s2\<restriction>\<^sub>V''fl'' \<and> s1\<restriction>\<^sub>V''fr'' = s2\<restriction>\<^sub>V''fr'' \<and> s1\<restriction>\<^sub>V''mode'' = s2\<restriction>\<^sub>V''mode'')"
  apply(clarsimp simp: vec_eq_iff, rule iffI, force)
  by (rule AMV_induct, auto)

subsubsection \<open> Formalisation of continuous dynamics \<close>

(* abbreviation "\<omega> \<equiv> U(arccos((v + a) \<bullet> v / (\<parallel>v + a\<parallel> * \<parallel>v\<parallel>)) \<triangleleft> \<not> \<parallel>v\<parallel> = 0 \<triangleright> 0)" *)
abbreviation pos :: "real^AMV \<Rightarrow> real^2"
  where "pos s \<equiv> (\<chi> i. if i=1 then s\<restriction>\<^sub>V''x'' else s\<restriction>\<^sub>V''y'')"

abbreviation vel :: "real^AMV \<Rightarrow> real^2"
  where "vel s \<equiv> (\<chi> i. if i=1 then s\<restriction>\<^sub>V''vx'' else s\<restriction>\<^sub>V''vy'')"

abbreviation acc :: "real^AMV \<Rightarrow> real^2"
  where "acc s \<equiv> (\<chi> i. if i=1 then s\<restriction>\<^sub>V''ax'' else s\<restriction>\<^sub>V''ay'')"

abbreviation "omega s \<equiv> (
  if \<parallel>vel s\<parallel> \<noteq> 0 then 
    arccos((vel s + acc s) \<bullet> vel s / ((\<parallel>vel s + acc s\<parallel>) * (\<parallel>vel s\<parallel>))) 
  else 0)"


(* [ p \<mapsto>\<^sub>s v
  , v \<mapsto>\<^sub>s a
  , a \<mapsto>\<^sub>s 0
  , \<phi> \<mapsto>\<^sub>s \<omega>
  , s \<mapsto>\<^sub>s (v \<bullet> a) / s \<triangleleft> \<not> s = 0 \<triangleright> \<parallel>a\<parallel> 
  , t \<mapsto>\<^sub>s 1 
  , old \<mapsto>\<^sub>s 0 ] *)
abbreviation f_amv :: "real^AMV \<Rightarrow> real^AMV" ("f")
  where "f s \<equiv> (\<chi> i. 
    if i=\<downharpoonright>\<^sub>V''x'' then s\<restriction>\<^sub>V''vx'' else (
    if i=\<downharpoonright>\<^sub>V''y'' then s\<restriction>\<^sub>V''vy'' else (
    if i=\<downharpoonright>\<^sub>V''vx'' then s\<restriction>\<^sub>V''ax'' else (
    if i=\<downharpoonright>\<^sub>V''vy'' then s\<restriction>\<^sub>V''ay'' else (
    if i=\<downharpoonright>\<^sub>V''phi'' then omega s else (
    if i=\<downharpoonright>\<^sub>V''speed'' then (
      if s\<restriction>\<^sub>V''speed'' \<noteq> 0 then 
        (vel s \<bullet> acc s) / s\<restriction>\<^sub>V''speed'' 
      else 
        \<parallel>acc s\<parallel>) else (
    if i=\<downharpoonright>\<^sub>V''t'' then 1 else 0)))))))"

(* abbreviation "ax\<^sub>A\<^sub>V \<equiv> U(&\<^bold>c:t < \<epsilon> \<and> 
    &\<^bold>c:s *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>),cos(&\<^bold>c:\<phi>)]\<^bold>] = &\<^bold>c:v \<and> 
    0 \<le> &\<^bold>c:s \<and> &\<^bold>c:s \<le> S)" *)
abbreviation amv_guard :: "real \<Rightarrow> real \<Rightarrow> real^AMV \<Rightarrow> bool" ("G")
  where "G \<epsilon> S s \<equiv> s\<restriction>\<^sub>V''t'' < \<epsilon> \<and> 
    s\<restriction>\<^sub>V''speed'' *\<^sub>R (\<chi> i. if i=1 then sin (s\<restriction>\<^sub>V''phi'') else cos (s\<restriction>\<^sub>V''phi'')) = vel s \<and>
    0 \<le> s\<restriction>\<^sub>V''speed'' \<and> s\<restriction>\<^sub>V''speed'' \<le> S"

(* abbreviation "Dynamics \<equiv> \<^bold>c:t := 0 ;; ODE" *)
abbreviation "amv_dyn \<epsilon> S \<equiv> (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0)) ; (x\<acute>= f & (G \<epsilon> S))"


subsubsection \<open> Formalisation of discrete control \<close>

locale AMV =
  fixes \<epsilon> :: real \<comment> \<open> max. time for ODE \<close>
    and "e\<^sub>\<Phi>" :: real \<comment> \<open> angle hysteresis \<close>
    and "s\<^sub>\<epsilon>" :: real \<comment> \<open> speed setpoint limiter \<close>
    and "\<Phi>\<^sub>\<epsilon>" :: real \<comment> \<open> angle setpoint limiter\<close>
    and flmax :: real \<comment> \<open> maximum force capable by motor \<close>
    and frmax :: real \<comment> \<open> maximum rotational force capable by motor \<close>
    and "k\<^sub>l" :: real \<comment> \<open> proportionality controller constant for longitudinal force \<close>
    and "k\<^sub>r" :: real \<comment> \<open> proportionality controller constant for radial force \<close>
    and m :: real \<comment> \<open> mass of the AMV \<close>
    and S :: real \<comment> \<open> max. (controlling) speed of AMV \<close> (* as opposed to that by laws of physics *)
    and H :: real \<comment> \<open> min. (controlling) speed of AMV \<close>
    and HCM :: real \<comment> \<open> high caution mode \<close>
    and MOM :: real \<comment> \<open> main operating mode \<close>
    and OCM :: real \<comment> \<open> operator control mode \<close>
    and wp :: "real^2" \<comment> \<open> waypoint's position  \<close>
    and Obs :: "(real^2) set" \<comment> \<open> set of obstacles \<close>
  assumes "Obs = {(\<chi> i::2. (1::real))}"
    and "HCM = 1"
    and "MOM = 2"
    and "OCM = 3"
    and mass: "m > 0"
    and longF: "flmax > 0"
    and rotF: "frmax > 0"
begin

(* abbreviation "angOfVec \<equiv> vangle \<^bold>[[0::real,100]\<^bold>]"
   abbreviation "steerToWP \<equiv> rh := angOfVec(nextWP - &\<^bold>c:p)" *)
abbreviation "steerToWP \<equiv> (\<downharpoonright>\<^sub>V''hSP'' ::= (\<lambda>s. vangle (\<chi> i. if i=1 then 0 else 100) (wp - pos s)))"

lemma "vector [0,100] = (\<chi> i::2. if i=1 then (0::real) else 100)"
  apply(simp add: vec_eq_iff vector_def)
  using exhaust_2 by auto

(* abbreviation 
  "LRE \<equiv> ((mode = HCM) \<longrightarrow>\<^sub>r rs := 0.1 ;; steerToWP)
       \<sqinter> ((mode = OCM) \<longrightarrow>\<^sub>r II)
       \<sqinter> ((mode = MOM) \<longrightarrow>\<^sub>r 
             rs := 1 ;; 
             steerToWP ;; 
             if (\<exists> o. o \<in> obsReg \<and> \<parallel>&\<^bold>c:p - \<guillemotleft>o\<guillemotright>\<parallel> \<le> 7.5) then mode := HCM ;; rs := 0.1 fi
          )" *)

abbreviation "nearObj k s \<equiv> \<exists>ob \<in> Obs. \<parallel>pos s - ob\<parallel> \<le> k"
abbreviation "onCollCourse k s \<equiv> \<exists>ob \<in> Obs. \<parallel>pos s - ob\<parallel> \<le> k \<and> vangle (ob - pos s) (vel s) < e\<^sub>\<Phi>"

abbreviation "LRE k \<equiv> 
  IF (\<lambda>s. s\<restriction>\<^sub>V''mode'' = HCM) THEN 
    (\<downharpoonright>\<^sub>V''sSP'' ::= (\<lambda>s. H)) ; steerToWP
  ELSE (IF (\<lambda>s. s\<restriction>\<^sub>V''mode'' = MOM) THEN 
    (\<downharpoonright>\<^sub>V''sSP'' ::= (\<lambda>s. S)); steerToWP;
    (IF nearObj k THEN 
      (\<downharpoonright>\<^sub>V''mode'' ::= (\<lambda>s. HCM));(\<downharpoonright>\<^sub>V''sSP'' ::= (\<lambda>s. H)) 
    ELSE skip)
  ELSE skip)"

(*
abbreviation "AP \<equiv> 
  if \<parallel>rs - &\<^bold>c:s\<parallel> > s\<^sub>\<epsilon>
    then ft := sgn(rs - &\<^bold>c:s)*min(kp\<^sub>g\<^sub>v * \<parallel>rs - &\<^bold>c:s\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    else ft := 0 fi ;; 
  if \<parallel>rh - &\<^bold>c:\<phi>\<parallel> > \<phi>\<^sub>\<epsilon>
    then fl := sgn(rh - &\<^bold>c:\<phi>)*min(kp\<^sub>g\<^sub>r * \<parallel>rh - &\<^bold>c:\<phi>\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    else fl := 0 fi ;;
  f := fl *\<^sub>R \<^bold>[[cos(&\<^bold>c:\<phi>), sin(&\<^bold>c:\<phi>)]\<^bold>] 
     + ft *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>), cos(&\<^bold>c:\<phi>)]\<^bold>] ;;
  \<^bold>c:a := f /\<^sub>R m"
*)
abbreviation "AP \<equiv> 
  (IF (\<lambda>s. \<bar>s\<restriction>\<^sub>V''sSP'' - s\<restriction>\<^sub>V''speed''\<bar> > s\<^sub>\<epsilon>) THEN 
    (\<downharpoonright>\<^sub>V''fl'' ::= (\<lambda>s. sgn (s\<restriction>\<^sub>V''sSP'' - s\<restriction>\<^sub>V''speed'') * (min (k\<^sub>l * \<bar>s\<restriction>\<^sub>V''sSP'' - s\<restriction>\<^sub>V''speed''\<bar>) flmax))) 
  ELSE 
    (\<downharpoonright>\<^sub>V''fl'' ::= (\<lambda>s. 0)));
  (IF (\<lambda>s. \<bar>s\<restriction>\<^sub>V''hSP'' - s\<restriction>\<^sub>V''phi''\<bar> > \<Phi>\<^sub>\<epsilon>) THEN 
    (\<downharpoonright>\<^sub>V''fr'' ::= (\<lambda>s. sgn (s\<restriction>\<^sub>V''hSP'' - s\<restriction>\<^sub>V''phi'') * (min (k\<^sub>r * \<bar>s\<restriction>\<^sub>V''hSP'' - s\<restriction>\<^sub>V''phi''\<bar>) frmax))) 
  ELSE 
    (\<downharpoonright>\<^sub>V''fr'' ::= (\<lambda>s. 0)));
  (\<downharpoonright>\<^sub>V''ax'' ::= (\<lambda>s. (s\<restriction>\<^sub>V''fl'' * cos (s\<restriction>\<^sub>V''phi'') + s\<restriction>\<^sub>V''fr'' * sin (s\<restriction>\<^sub>V''phi''))/m));
  (\<downharpoonright>\<^sub>V''ay'' ::= (\<lambda>s. (s\<restriction>\<^sub>V''fl'' * sin (s\<restriction>\<^sub>V''phi'') + s\<restriction>\<^sub>V''fr'' * cos (s\<restriction>\<^sub>V''phi''))/m))"


(* abbreviation "AUV \<equiv> (LRE ;; AP ;; Dynamics)\<^sup>\<star>" *)
abbreviation "AUV \<equiv> (LRE 7.5; AP; amv_dyn \<epsilon> S)"

lemma LRE_no_modfs:
  shows LRE_no_modfs_t: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''t'')"
    and LRE_no_modfs_x: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''x'')"
    and LRE_no_modfs_y: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''y'')"
    and LRE_no_modfs_vx: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''vx'')"
    and LRE_no_modfs_vy: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''vy'')"
    and LRE_no_modfs_ax: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''ax'')"
    and LRE_no_modfs_ay: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''ay'')"
    and LRE_no_modfs_speed: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''speed'')"
    and LRE_no_modfs_phi: "no_modfs (LRE 7.5) (\<downharpoonright>\<^sub>V''phi'')"
  unfolding no_modfs_def by (auto simp: to_var_inject)

lemma AP_no_modfs:
  shows AP_no_modfs_t: "no_modfs AP (\<downharpoonright>\<^sub>V''t'')"
    and AP_no_modfs_x: "no_modfs AP (\<downharpoonright>\<^sub>V''x'')"
    and AP_no_modfs_y: "no_modfs AP (\<downharpoonright>\<^sub>V''y'')"
    and AP_no_modfs_vx: "no_modfs AP (\<downharpoonright>\<^sub>V''vx'')"
    and AP_no_modfs_vy: "no_modfs AP (\<downharpoonright>\<^sub>V''vy'')"
    and AP_no_modfs_speed: "no_modfs AP (\<downharpoonright>\<^sub>V''speed'')"
    and AP_no_modfs_phi: "no_modfs AP (\<downharpoonright>\<^sub>V''phi'')"
  unfolding no_modfs_def by (auto simp: to_var_inject)

lemma amv_dyn_no_modfs_sSP: "no_modfs (amv_dyn a b) (\<downharpoonright>\<^sub>V''sSP'')"
  unfolding no_modfs_def apply (rule allI)
  apply(rule_tac R="\<lambda>s. s\<restriction>\<^sub>V''sSP'' = k" in hoare_kcomp, simp_all add: to_var_inject)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: to_var_inject)

lemma amv_dyn_no_modfs_hSP: "no_modfs (amv_dyn a b) (\<downharpoonright>\<^sub>V''hSP'')"
  unfolding no_modfs_def apply (rule allI)
  apply(rule_tac R="\<lambda>s. s\<restriction>\<^sub>V''hSP'' = k" in hoare_kcomp, simp_all add: to_var_inject)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: to_var_inject)

lemma amv_dyn_no_modfs_fr: "no_modfs (amv_dyn a b) (\<downharpoonright>\<^sub>V''fr'')"
  unfolding no_modfs_def apply (rule allI)
  apply(rule_tac R="\<lambda>s. s\<restriction>\<^sub>V''fr'' = k" in hoare_kcomp, simp_all add: to_var_inject)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: to_var_inject)

lemma amv_dyn_no_modfs_fl: "no_modfs (amv_dyn a b) (\<downharpoonright>\<^sub>V''fl'')"
  unfolding no_modfs_def apply (rule allI)
  apply(rule_tac R="\<lambda>s. s\<restriction>\<^sub>V''fl'' = k" in hoare_kcomp, simp_all add: to_var_inject)
  by (auto intro!: diff_invariant_rules poly_derivatives simp: to_var_inject)

lemma "G \<epsilon> S \<le> |LRE 7.5] G \<epsilon> S"
  by (auto simp: to_var_inject vec_eq_iff)

lemma "(\<lambda>s. s\<restriction>\<^sub>V''t'' \<ge> 0) \<le> |x\<acute>= f & (G \<epsilon> S)] (\<lambda>s. s\<restriction>\<^sub>V''t'' \<ge> 0)"
  apply(simp, rule_tac \<nu>'="\<lambda>s. 0" and \<mu>'="\<lambda>s. 1" in diff_invariant_leq_rule)
  apply(auto intro!: poly_derivatives)
  by (erule_tac x="\<downharpoonright>\<^sub>V''t''" in allE, simp add: to_var_inject)

lemma "(\<lambda>s. s\<restriction>\<^sub>V''speed'' = \<parallel>vel s\<parallel>) \<le> |x\<acute>= f & (G \<epsilon> S)] (\<lambda>s. s\<restriction>\<^sub>V''speed'' = \<parallel>vel s\<parallel>)"
  apply(rule diff_weak_rule, clarsimp)
  apply(drule sym, simp, simp add: norm_vec_def L2_set_def)
  unfolding UNIV_2 by auto

lemma "(\<lambda>s. s\<restriction>\<^sub>V''sSP'' = s\<restriction>\<^sub>V''speed'' \<and> s\<restriction>\<^sub>V''hSP'' = s\<restriction>\<^sub>V''phi'') \<le> |AP] (\<lambda>s. acc s = 0)"
  by (auto simp: to_var_inject vec_eq_iff)

lemma "(\<lambda>s. s\<restriction>\<^sub>V''speed'' \<in> {s\<restriction>\<^sub>V''sSP'' - s\<^sub>\<epsilon> .. s\<restriction>\<^sub>V''sSP'' + s\<^sub>\<epsilon>} \<and> s\<restriction>\<^sub>V''hSP'' = s\<restriction>\<^sub>V''phi'') \<le> |AP] (\<lambda>s. acc s = 0)"
  apply (auto simp: to_var_inject vec_eq_iff)
  done

lemma "(\<lambda>s. s\<restriction>\<^sub>V''sSP'' < s\<restriction>\<^sub>V''speed'' - s\<^sub>\<epsilon> \<and> s\<restriction>\<^sub>V''hSP'' = s\<restriction>\<^sub>V''phi'') \<le> |AP] (\<lambda>s. \<parallel>acc s\<parallel> > 0)"
  using sin_zero_abs_cos_one mass longF rotF
  apply (auto simp: to_var_inject vec_eq_iff)
  using exhaust_2 apply fastforce



lemma "(\<lambda>s. acc s \<bullet> vel s = (\<parallel>acc s\<parallel>) * (\<parallel>vel s\<parallel>)) \<le> |amv_dyn a b] (\<lambda>s. acc s \<bullet> vel s = (\<parallel>acc s\<parallel>) * (\<parallel>vel s\<parallel>))"
  apply(rule_tac R="\<lambda>s. acc s \<bullet> vel s = (\<parallel>acc s\<parallel>) * (\<parallel>vel s\<parallel>)" in hoare_kcomp)
  apply(simp add: le_fun_def)
   apply(simp add: inner_vec_def norm_vec_def L2_set_def )

  oops


thm to_str_induct to_str_inject to_str_inverse
thm to_var_induct to_var_inject to_var_inverse

end

no_notation f_amv ("f")
        and amv_guard ("G")

end