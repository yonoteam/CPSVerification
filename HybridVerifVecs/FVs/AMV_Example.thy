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


subsubsection \<open> Type of variables \<close>

(* continuous variables *)
abbreviation "amv_cstrs \<equiv> {''x'', ''y'', ''vx'', ''vy'', ''ax'', ''ay'', 
  ''phi'', ''speed'', ''t''}"

(* discrete variables *)
abbreviation "amv_dstrs \<equiv> {''sSP'', ''hSP'', ''fx'', ''fy'', ''mode''}"

(* all variables *)
abbreviation "amv_strs \<equiv> {''x'', ''y'', ''vx'', ''vy'', ''ax'', ''ay'', 
  ''phi'', ''speed'', ''t'', ''sSP'', ''hSP'', ''fx'', ''fy'', ''mode''}"

(* type of variables *)
typedef AMV = amv_strs
  morphisms to_str to_var
  by blast

notation to_var ("\<downharpoonright>\<^sub>V")

abbreviation "amv_terms \<equiv> {\<downharpoonright>\<^sub>V''x'', \<downharpoonright>\<^sub>V''y'', \<downharpoonright>\<^sub>V''vx'', \<downharpoonright>\<^sub>V''vy'', \<downharpoonright>\<^sub>V''ax'', \<downharpoonright>\<^sub>V''ay'', 
  \<downharpoonright>\<^sub>V''phi'', \<downharpoonright>\<^sub>V''speed'', \<downharpoonright>\<^sub>V''t'', \<downharpoonright>\<^sub>V''sSP'', \<downharpoonright>\<^sub>V''hSP'', \<downharpoonright>\<^sub>V''fx'', \<downharpoonright>\<^sub>V''fy'', \<downharpoonright>\<^sub>V''mode''}"

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
  \<or> x = \<downharpoonright>\<^sub>V''t'' \<or> x=\<downharpoonright>\<^sub>V''sSP'' \<or> x=\<downharpoonright>\<^sub>V''hSP'' \<or> x=\<downharpoonright>\<^sub>V''fx'' \<or> x=\<downharpoonright>\<^sub>V''fy'' \<or> x=\<downharpoonright>\<^sub>V''mode''"
  using AMV_univ by auto

lemma AMV_sum:
  fixes f :: "AMV \<Rightarrow> ('a::banach)"
  shows "(\<Sum>i\<in>UNIV. f i) = f (\<downharpoonright>\<^sub>V''x'') + f (\<downharpoonright>\<^sub>V''y'') + f (\<downharpoonright>\<^sub>V''vx'') + f (\<downharpoonright>\<^sub>V''vy'') 
  + f (\<downharpoonright>\<^sub>V''ax'') + f (\<downharpoonright>\<^sub>V''ay'') + f (\<downharpoonright>\<^sub>V''phi'') + f (\<downharpoonright>\<^sub>V''speed'') + f (\<downharpoonright>\<^sub>V''t'')
  + f (\<downharpoonright>\<^sub>V''sSP'') + f (\<downharpoonright>\<^sub>V''hSP'') + f (\<downharpoonright>\<^sub>V''fx'') + f (\<downharpoonright>\<^sub>V''fy'') + f (\<downharpoonright>\<^sub>V''mode'')"
  unfolding AMV_univ by (simp add: to_var_inject)

lemma AMV_induct: "P (\<downharpoonright>\<^sub>V''x'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''y'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''vx'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''vy'') 
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''ax'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''ay'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''phi'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''speed'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''t'')
  \<Longrightarrow> P (\<downharpoonright>\<^sub>V''sSP'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''hSP'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''fx'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''fy'') \<Longrightarrow> P (\<downharpoonright>\<^sub>V''mode'')
  \<Longrightarrow> \<forall>i. P i"
  using AMV_exhaust by metis

lemma AMV_eq:
  "(s1 = s2) \<longleftrightarrow> (s1\<restriction>\<^sub>V''x'' = s2\<restriction>\<^sub>V''x'' \<and> s1\<restriction>\<^sub>V''y'' = s2\<restriction>\<^sub>V''y'' \<and> s1\<restriction>\<^sub>V''vx'' = s2\<restriction>\<^sub>V''vx'' \<and>
  s1\<restriction>\<^sub>V''vy'' = s2\<restriction>\<^sub>V''vy'' \<and> s1\<restriction>\<^sub>V''ax'' = s2\<restriction>\<^sub>V''ax'' \<and> s1\<restriction>\<^sub>V''ay'' = s2\<restriction>\<^sub>V''ay'' \<and>
  s1\<restriction>\<^sub>V''phi'' = s2\<restriction>\<^sub>V''phi'' \<and> s1\<restriction>\<^sub>V''speed'' = s2\<restriction>\<^sub>V''speed'' \<and> s1\<restriction>\<^sub>V''t'' = s2\<restriction>\<^sub>V''t'' \<and>
  s1\<restriction>\<^sub>V''sSP'' = s2\<restriction>\<^sub>V''sSP'' \<and> s1\<restriction>\<^sub>V''hSP'' = s2\<restriction>\<^sub>V''hSP'' \<and> 
  s1\<restriction>\<^sub>V''fx'' = s2\<restriction>\<^sub>V''fx'' \<and> s1\<restriction>\<^sub>V''fy'' = s2\<restriction>\<^sub>V''fy'' \<and> s1\<restriction>\<^sub>V''mode'' = s2\<restriction>\<^sub>V''mode'')"
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
abbreviation "amv_dyn \<epsilon> S  s \<equiv> (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. 0)) ; (x\<acute>= f & (G \<epsilon> S))"


subsubsection \<open> Formalisation of discrete control \<close>

locale AMV =
  fixes \<epsilon> :: real \<comment> \<open> max. time for ODE \<close>
    and S :: real \<comment> \<open> max. speed of AMV \<close>
    and H :: real \<comment> \<open> max. speed of AMV \<close>
    and HCM :: real \<comment> \<open> modes \<close>
    and MOM :: real
    and OCM :: real
    and wp :: "real^2" \<comment> \<open> waypoint's position  \<close>
    and Obs :: "(real^2) set" \<comment> \<open> set of obstacles \<close>
  assumes "Obs = {(\<chi> i::2. (1::real))}"
    and "HCM = 1"
    and "MOM = 2"
    and "OCM = 3"
begin

(* abbreviation "angOfVec \<equiv> vangle \<^bold>[[0::real,100]\<^bold>]"
   abbreviation "steerToWP \<equiv> rh := angOfVec(nextWP - &\<^bold>c:p)" *)
abbreviation "steerToWP \<equiv> (\<downharpoonright>\<^sub>V''t'' ::= (\<lambda>s. vangle (\<chi> i. if i=1 then 0 else 100) (wp - pos s)))"

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
abbreviation "LRE s \<equiv> if s\<restriction>\<^sub>V''mode'' = HCM then ((\<downharpoonright>\<^sub>V''sSP'' ::= (\<lambda>s. H)) ; steerToWP) s else {s}"


end


(* vangle *)
term vangle

no_notation f_amv ("f")
        and amv_guard ("G")



end