theory FirstAttempt
  imports 
Main
"../afp-2017-10-18/thys/Polynomials/Polynomials"

begin

context linorder
begin

text{* Useful definitions from the AFP entry on Polynomials. For specific examples see the 
document "ExplorePolinoms.thy" and the end of this file:
  · 'v monom_list = "('v \<times> nat)list" 
  · ('v,'a)poly = "('v monom \<times> 'a)list" 
  · 'v monom = Collect monom_inv
  · The function monom_inv, referred above tests three things:
      - That all the powers are greater than or equal to 1.
      - That all the variables are different.
      - That all variables appear ordered.
OBSERVATION: Because of the way monomials are built, we need to ensure that our derivatives
respect the function "monom_inv".
*}

(* This abbreviation tests if the first argument is a variable appearing in the monomial. *)
abbreviation IsNotVar :: "'v \<Rightarrow> 'v monom_list \<Rightarrow> bool"   where "IsNotVar x ml \<equiv> (x \<notin> fst ` set ml)"

(* This terms are here so I can explicitly see how some operations in the abbreviation above work.*)
value "snd ` set [(0::int,1::int),(2,3)] "
term "op `"

(* Operation on the exponents. Because of OBSERVATION above, we "delete" the variable if it appears
with exponent 1, otherwise we substract one from the exponent i.e. 
  - downExp x xy\<^sup>2z = y\<^sup>2z 
  - downExp x x\<^sup>4y\<^sup>2z = x\<^sup>3y\<^sup>2z *)
fun downExp :: "'v \<Rightarrow> 'v monom_list \<Rightarrow> 'v monom_list" where
"downExp x [] = []"|
"downExp x ((z,n) # tail) = (if x = z then (if n=1 then tail else (z,n-1) # tail) else (z,n) # downExp x tail)"

(* Operation in the coefficients. Separately, we return the coefficient. *)
fun derivCoeffMonomList :: "'v \<Rightarrow> 'v monom_list \<Rightarrow> nat" where
"derivCoeffMonomList x [] = 0"|
"derivCoeffMonomList x ((z,n) # tail) = (if x = z then n else derivCoeffMonomList x tail)"

(* The derivative on a monomList returns a pair of a coefficient and a monomList. *)
definition derivMonomList :: "'v \<Rightarrow> 'v monom_list \<Rightarrow> (nat \<times> 'v monom_list)" where
  "derivMonomList x ml = (if IsNotVar x ml then (0,[]) else (derivCoeffMonomList x ml,downExp x ml))"

(* \<partial> x 0 = 0 *)
lemma derivZeroMonomList [simp]: "derivMonomList x [] = (0,[])"
  by(simp add: derivMonomList_def)

(* \<partial> x x = 1 *)
lemma derivOfVar [simp]: "derivMonomList x [(x,1)] = (1,[])"
  by(simp add: derivMonomList_def)

(* \<partial> x x\<^sup>n = nx\<^sup>n\<^sup>-\<^sup>1} *)
lemma derivOfNthPow [simp]: "n > 1 \<Longrightarrow> derivMonomList x [(x,n)] = (n,[(x,n-1)])"
  apply(induct n, simp_all add: derivMonomList_def)
  done

(* \<partial> x ExprWithNoX = 0 *)
lemma derivOfConst [simp]: "IsNotVar x ml \<Longrightarrow> derivMonomList x ml = (0,[])"
  apply(simp add: derivMonomList_def)
  done

(* The empty list is a monomial. *)
lemma [simp]: "monom_inv [] = True"
  by (simp add: monom_inv_def)

(* Stucked with this proof. For now... Not sure if necessary. *)
lemma derivReturnsMonoms : "monom_inv list \<Longrightarrow> monom_inv (snd (derivMonomList x list))"
  oops

(* According to Isabelle, she needs this as a theorem to do the lifting to monomials. *)
lemma derivReturnsMonoms : "monom_inv list \<Longrightarrow> (x,n) \<in> set list \<Longrightarrow> monom_inv (downExp x list)"
  apply (induction list rule: downExp.induct)
   apply(simp)
  oops

(* Previous lemma necessary to do the lifting, and be able to define derivatives for polynomials. *)
lift_definition derivMonom :: "'v \<Rightarrow> 'v::linorder monom \<Rightarrow> (nat \<times>'v monom)" is derivMonomList
  apply(auto simp: derivMonomList_def)
  using linorder_class.monom_inv_def apply fastforce

(* Derivative on polynomials with respect to a variable, it still working it out... *)
fun deriv :: "'a \<Rightarrow> ('v,'a)poly \<Rightarrow> ('v,'a)poly" where
"deriv x [] = zero_poly"|
"deriv x [(m, coef)] = (if x \<notin> set (map fst ` m) then zero_poly else zero_poly)"

end

(* Some values to quickly check that our derivatives for monomials work as expected. *)
value "derivMonomList 1 ([]::(int \<times> nat)list)"
value "derivMonomList 1 [(1::int,1::nat)]"
value "derivMonomList 0 [(0::int,1::nat),(2,3)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,2)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,1)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,0)]"
(* Notice this last input does not satisfy "monom_inv". *)

end