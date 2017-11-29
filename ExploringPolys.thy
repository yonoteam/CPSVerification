theory ExploringPolys
  imports 
Main
"HOL-Computational_Algebra.Polynomial"
"derivPolysList"

begin
text{* Checking two theories as candidates for our implementation of polynomials. The first one
"Polynomials" is in the AFP. The second one "Polynomial" is part of HOL-Computational-Algebra.
In the end I chose the AFP entry because it allows multiple variables. The other one just generates 
single variable polynomials. *}

(* P O L Y N O M I A L S *)

(* An environment: x\<^sub>1 \<mapsto> -1, x\<^sub>2 \<mapsto> 2, x\<^sub>3 \<mapsto> 3 *)
term "(\<lambda> s. if s = (1::int) then (-1::int) else (if s = (2::int) then (2::int) else 3))"
(* A monomial (list): x\<^sub>1\<cdot>x\<^sub>2\<^sup>2\<cdot>x\<^sub>3\<^sup>2 *)
term "[((1::int),1),(2,2),(3,2)]:: int monom_list"
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

(* In the end, a monomial ""is"" an element of the following thing: *)
term "Collect monom_inv"
thm monom_inv_def
thm distinct_def
value "[((1::int),1),(2,2),(3,2)] \<in> Collect monom_inv"

(* Studying the behavior of Abs y Rep... *)
term "Abs_monom [((1::int),1),(2,2),(3,2)]"
term "Rep_monom (x:: int monom)"
value "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)])"
term "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)])"
lemma "Rep_monom (Abs_monom [((1::int),1),(2,2),(3,2)]) = [((1::int),1),(2,2),(3,2)]"
apply(rule  Polynomials.monom.Abs_monom_inverse)
apply(auto simp: monom_inv_def)
done
(* try *)

(* List.extract used to define addition of polynomials. *)
value "List.extract (\<lambda> list. fst list = [(2, 2), (3, 1)]) 
[([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2::nat)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)]"

(* Derivative on polynomials: syntactic version. The alternative is to define a finite partial order
and use the "show" theory accompanying "polynomials". *)
fun derivList :: "('v::linorder) \<Rightarrow> ('v monom_list \<times> 'a:: semiring_0)list \<Rightarrow> ('v monom_list \<times> 'a)list" where
"derivList x [] = []"|
"derivList x [(mon, coef)] = (if (derivCoeffMonomList x mon) = 0 then [] else 
[((if (IsNotVar x mon) then [] else downExp x mon),natScale (derivCoeffMonomList x mon) coef)])"|
"derivList x (headMonom # tailMonom) = (derivList x [headMonom]) @ (derivList x tailMonom)"

(* \<real>[x,y,z,w] \<ni> P(x,y,z,w) = 2 + w + 3xyz + 3x\<^sup>2 + y\<^sup>2z + 5z\<^sup>3. *)
term "[([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2::nat)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)]"
term "(deriv 1 [(Abs_monom [((1::int),1),(2,1),(3,1)],3::real)])::(int,real)poly"
(* \<partial> x P(x,y,z,w) = 3yz + 6x. *)
value "(derivList 1 [([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)])"
(* \<partial> y P(x,y,z,w) = 3xz + 2yz. *)
value "(derivList 2 [([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)])"
(* \<partial> z P(x,y,z,w) = 3xy + y\<^sup>2 + 15z\<^sup>2. *)
value "(derivList 3 [([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)])"
(* \<partial> w P(x,y,z,w) = 1. *)
value "(derivList 4 [([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)])"
(* \<partial> v P(x,y,z,w) = 0. *)
value "(derivList 5 [([],2),([((1::int),1),(2,1),(3,1)],3::real),([(1,2)],3),([(2,2),(3,1)],1),([(3,3)],5),([(4,1)],1)])"


(* P O L Y N O M I A L *)

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

value "coeff [:3, 2, 4, (1::int), 5, 1:] (2::nat)"
value "poly_of_list ([0,1,2,1,0,1]::int list)"
value "poly_of_list ([]::int list)" 
(*\<partial> (0 + x + 2x\<^sup>2 + x\<^sup>3 + x\<^sup>5) = [:1, 4, 3, 0, 5:] *)
value "pderiv (poly_of_list ([0,1,2,1,0,1]::int list))"
(* Polynomial: 3 + 4x + x\<^sup>2 evaluated in 2 equals 15. *)
value "poly [:3, 4, (1::int):] 2"

declare [[show_types]]
declare [[show_sorts]]

end