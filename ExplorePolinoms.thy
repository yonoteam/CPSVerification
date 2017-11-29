theory ExplorePolinoms
  imports 
Main
"HOL-Computational_Algebra.Polynomial"
"../afp-2017-10-18/thys/Polynomials/Polynomials"
"../afp-2017-10-18/thys/Polynomials/Show_Polynomials"

begin
text{* Checking two theories as candidates for our implementation of polynomials. The first one
"Polynomials" is in the AFP. The second one "Polynomial" is part of HOL-Computational-Algebra.
In the end I chose the AFP entry because it allows multiple variables. The other one just generates 
single variable polynomials. *}

(* P O L Y N O M I A L S *)

(* An attempt to start my own partial order in Isabelle. See comments below to know why. 
typedecl myLine
instance myLine :: linorder
  by intro_classes
consts x :: "myLine"
consts y :: "myLine"
consts z :: "myLine" *)

(* An environment: x\<^sub>1 \<mapsto> -1, x\<^sub>2 \<mapsto> 2, x\<^sub>3 \<mapsto> 3 *)
term "(\<lambda> s. if s = (1::int) then (-1::int) else (if s = (2::int) then (2::int) else 3))"
(* A monomial (list): x\<^sub>1\<cdot>x\<^sub>2\<^sup>2\<cdot>x\<^sub>3\<^sup>2 *)
term "[((1::int),1),(2,2),(3,2)]:: int monom_list"
value "shows_monom_list [((1::int),1),(2,2),(3,2)] ''''"
(* This function requires the domain of our environment to be a linear order. Choosing integers. *)
value "eval_monom_list
 (\<lambda> s. if s = (1::int) then (-1::int) else (if s = (2::int) then (2::int) else 3))
 [((1::int),1),(2,2),(3,2)]"
(* Not sure why they added the "inv" in the function below. I guess they are making reference to 
an "invariant". It tests three things:
  - All the powers are greater than or equal to 1.
  - All the variables are different.
  - The variables appear ordered. *)
thm monom_inv_def

(* The function below returns the amount of times the variable (snd argument)  appears in the
 monomial.*)
value "sum_var_list [((1::int),1),(2,2),(3,4)] 3"

(* In the end, a monomial ""is"" (see comment below on typedef's) an element of the
 following thing: *)
term "Collect monom_inv"
value "[((1::int),1),(2,2),(3,2)] \<in> Collect monom_inv"
term "Abs_monom [((1::int),1),(2,2),(3,2)]"
term "Rep_monom (x:: int monom)"
value "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)])"
term "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)])"

thm monom_inv_def
thm distinct_def

lemma "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)]) = [((1::int),1),(2,2),(3,2)]"
apply(rule  Polynomials.monom.Abs_monom_inverse)
apply(auto simp: monom_inv_def)
done
(* try *)

value "List.extract (\<lambda> list. fst list = [(2, 2), (3, 1)]) 
[([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2::nat)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)]"

declare [[show_types]]
declare [[show_sorts]]

(* P O L Y N O M I A L *)

(* Personal NOTE: The expression "\<forall>\<^sub>\<infinity> n. P n" means "almost all n satisfy P n" *)
(* With this commands I try to understand this part of the file Polynomial.thy: 
  lift_definition pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p. case_nat a (coeff p)" 
*)
thm case_nat_def
term "case_nat"
term "\<lambda> a p. case_nat a (coeff p)"
thm coeff_pCons
value "pCons (3::nat) [:0, 1, 2, 1, 0, 1:]" 
(* The last command shows a representation of polynomials in this theory. Not a good one. =/ *)

(* Personal NOTE: When writing type definitions, you input a set-comprehension scheme like this
"SetToInput = {x :: existingType. P x}" and Isabelle does many things in the background:
Firstly, it creates a new type "newType". 
Secondly, Isabelle axiomatizes two isomorphisms: 
  Abs :: existingType \<Rightarrow> newType (for abstraction, also thought of as constructor.)
  rep :: newType \<Rightarrow> existingType (for representation, also thought of as destructor.)
such that:
  (1) the image of rep is in SetToInput: \<forall> x. (rep x) \<in> SetToInput.
  (2) Abs is a left inverse for rep: \<forall> x. Abs (rep x) = x.
  (3) rep is a left inverse for Abs: \<forall> x \<in> SetToInput. rep (Abs x) = x.
In the example below, the "morphisms" directive just renames the canonical rep and Abs functions
to the names provided next.
Thirdly, it starts a proof for non-emptyness, that's why we need the "by proof" command in 
the example below.
EXAMPLE:
typedef (overloaded) 'a poly = "{f :: nat \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n. f n = 0}"
  morphisms coeff Abs_poly
  by (auto intro!: ALL_MOST)
*)
value "coeff [:3, 2, 4, (1::int), 5, 1:] (2::nat)"
value "poly_of_list ([0,1,2,1,0,1]::int list)"
value "poly_of_list ([]::int list)" 
(*\<partial> (0 + x + 2x\<^sup>2 + x\<^sup>3 + x\<^sup>5) = [:1, 4, 3, 0, 5:] *)
value "pderiv (poly_of_list ([0,1,2,1,0,1]::int list))"
(* Polynomial: 3 + 4x + x\<^sup>2 evaluated in 2 equals 15. *)
value "poly [:3, 4, (1::int):] 2"

end