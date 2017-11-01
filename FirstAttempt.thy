theory FirstAttempt
  imports 
Main
"../afp-2017-10-18/thys/Polynomials/Polynomials"
"HOL.Real"

begin

context linorder
begin
text{* Useful definitions from the AFP entry on Polynomials. For specific examples see the 
document "ExplorePolinoms.thy" and the end of this file:
  · 'v monom_list = "('v \<times> nat)list"  
  · 'v monom = Collect monom_inv
  · The function monom_inv, referred above tests three things:
      - That all the powers are greater than or equal to 1.
      - That all the variables are different.
      - That all variables appear ordered.
OBSERVATION: Because of the way monomials are built, we need to ensure that our derivatives
respect the function "monom_inv". This is what we do in this context.
*}

(* This abbreviation tests if the first argument is a variable appearing in the monomial. *)
abbreviation IsNotVar :: "'a \<Rightarrow> 'a monom_list \<Rightarrow> bool" 
  where "IsNotVar x ml \<equiv> (x \<notin> fst ` set ml)"

(* This terms are here so I can explicitly see how some operations in the abbreviation above work.*)
value "snd ` set [(0::int,1::int),(2,3)] "
term "op `"

(* Operation on the exponents. Because of OBSERVATION above, we "delete" the variable if it appears
with exponent 1, otherwise we substract one from the exponent i.e. 
  - downExp x xy\<^sup>2z = y\<^sup>2z 
  - downExp x x\<^sup>4y\<^sup>2z = x\<^sup>3y\<^sup>2z *)
fun downExp :: "'a \<Rightarrow> 'a monom_list \<Rightarrow> 'a monom_list" where
"downExp x [] = []"|
"downExp x ((z,n) # tail) = 
          (if x = z then (if n=1 then tail else (z,n-1) # tail) else (z,n) # downExp x tail)"

(* Operation in the coefficients. Separately, we return the coefficient. *)
fun derivCoeffMonomList :: "'a \<Rightarrow> 'a monom_list \<Rightarrow> nat" where
"derivCoeffMonomList x [] = 0"|
"derivCoeffMonomList x ((z,n) # tail) = (if x = z then n else derivCoeffMonomList x tail)"

(* The derivative on a monomList returns a pair of a coefficient and a monomList. *)
definition derivMonomList :: "'a \<Rightarrow> 'a monom_list \<Rightarrow> (nat \<times> 'a monom_list)" where
  "derivMonomList x ml = 
          (if IsNotVar x ml then (0,[]) else (derivCoeffMonomList x ml,downExp x ml))"

(* Some values to quickly check that our derivatives for monomials work as expected. *)
value "derivMonomList 1 ([]::(int \<times> nat)list)"
value "derivMonomList 1 [(1::int,1::nat)]"
value "derivMonomList 0 [(0::int,1::nat),(2,3)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,2)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,1)]"
value "derivMonomList 4 [(0::int,1::nat),(2,3),(4,0)]"
(* Notice this last input does not satisfy "monom_inv". *)

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

(* Monomials do not have variables to the zeroth power. *)
lemma noZeroExpInMonoms: "monom_inv (monlist) \<Longrightarrow> (x, 0) \<notin> set (monlist)"
proof
  assume a:"monom_inv (monlist)"
  from a have b:"\<forall>(x, n) \<in> set (monlist). 1 \<le> n" by(simp add: monom_inv_def)
  assume c: "(x, 0) \<in> set (monlist)" --"to get a contradiction"
  from c and b have d: "1 \<le> (0::nat)" by (force)
  thus False by linarith 
qed

text{* We begin a proof to see that the derivative operator on monomials respects the 
predicate "monom_inv". For this we show three things: 
  - That all variables appear ordered.
  - That all the variables are different.
  - That all the powers are greater than or equal to 1.
*}

(* Lemmas for the first condition. *)
lemma downExpRespectsSortedness: "sorted (map fst list) \<Longrightarrow> sorted (map fst (downExp x list))"
  apply(induction list, auto)
    apply (simp add: local.sorted_Cons)
    apply (smt downExp.elims fst_conv insert_iff list.simps(15) list.simps(9) 
local.sorted_Cons local.sorted_many_eq)
    apply (smt downExp.elims fst_conv insert_iff list.simps(15) list.simps(9) 
local.sorted_Cons local.sorted_many)
  done

lemma fstCondMonomInv: "\<forall> list. monom_inv (list) \<longrightarrow> sorted (map fst (downExp x list))"
  apply(auto simp: monom_inv_def)
  using downExpRespectsSortedness by blast

(* Lemmas for the second condition. *)
lemma[simp]: "IsNotVar x list \<Longrightarrow> downExp x list = list"
  apply(induction list rule: downExp.induct, auto)
  done
  
lemma downExpPreservesVars: "set (map fst (downExp x list)) \<subseteq> set (map fst list)"
  apply(induction list rule: downExp.induct, auto)
  done
  
lemma downExpRespectsDistinct: "distinct (map fst list) \<Longrightarrow> distinct (map fst (downExp x list))"
  apply(induction list rule: downExp.induct, simp)
  apply(simp)
  apply(rule impI)
  by (metis downExpPreservesVars list.set_map subsetCE)

lemma sndCondMonomInv: "\<forall> list. monom_inv (list) \<longrightarrow> distinct (map fst (downExp x list))"
  by (simp add: downExpRespectsDistinct local.monom_inv_def)
  
(* Lemmas for the third condition. *)
lemma downExpRespectsPows: "(\<forall> (var,num) \<in> set list. 1 \<le> num) \<Longrightarrow> (x,n) \<in> set list \<Longrightarrow>
 \<forall> (var,num) \<in> set (downExp x list). 1 \<le> num"
 apply(induction list rule: downExp.induct, simp)
 by (smt case_prod_conv diff_is_0_eq' downExp.simps(2) less_one 
     linorder_class.not_le list.set_intros(1) list.set_intros(2) 
     order_class.order.not_eq_order_implies_strict set_ConsD zero_less_diff)

lemma thrdCondMonomInv: "monom_inv (list) \<Longrightarrow> (x,n) \<in> set list \<Longrightarrow>
 (\<forall> (var,num) \<in> set (downExp x list). 1 \<le> num)"
 apply(simp add: monom_inv_def)
 by (metis (no_types, lifting) One_nat_def case_prodI2 downExpRespectsPows old.prod.case)
 
 
(* According to Isabelle, she needs this as a theorem to do the lifting to monomials. *)
theorem derivReturnsMonoms :
"\<forall> list. monom_inv list \<longrightarrow> (x,n) \<in> set list \<longrightarrow> monom_inv (downExp x list)"
proof
  fix list
  show "monom_inv list \<longrightarrow> (x,n) \<in> set list \<longrightarrow> monom_inv (downExp x list)"
    proof
    assume hip1:"monom_inv list"
    from this have sorted:"sorted (map fst (downExp x list))" by (auto simp: fstCondMonomInv)
    from hip1 have distinct:"distinct (map fst (downExp x list))" by (auto simp: sndCondMonomInv)
    show "(x, n) \<in> set list \<longrightarrow> monom_inv (downExp x list)"
      proof
      assume hip2:"(x,n) \<in> set list"
      from hip1 and hip2 have powers: "(\<forall> (var,num) \<in> set (downExp x list). 1 \<le> num)"
      using thrdCondMonomInv by blast
      from sorted distinct and powers show "monom_inv (downExp x list)" 
      by (auto simp: monom_inv_def)
      qed
    qed
qed
    
end

(* Previous lemma necessary to do the lifting. In turn, the lifting is necessary to define 
derivatives for polynomials. *)
lift_definition derivMonom :: "'a \<Rightarrow> 'a::linorder monom \<Rightarrow> (nat \<times>'a monom)" is derivMonomList
  apply(transfer, auto simp: derivMonomList_def)
  apply(simp add: derivReturnsMonoms)
  done

text{* Reminders for what comes next: 
  · ('v,'a)poly = "('v monom \<times> 'a)list"
  · derivMonom :: "'a \<Rightarrow> 'a monom \<Rightarrow> (nat \<times> 'a monom)" 
  · poly_inv p \<equiv> (\<forall> c \<in> snd ` set p. c \<noteq> 0) \<and> distinct (map fst p)" *}
  
(* Exploring the locales to find a function "\<cdot>: nat \<Rightarrow> ('a::monoid_add) \<Rightarrow> 'a" that returns an
element "x:'a" scaled as many times as "n:nat", i.e. it returns "n\<cdot>x=x+x+x+\<dots>+x".  *)
  print_locales
  thm ab_semigroup_add_class_def
  thm ab_semigroup_add_axioms
  thm plus_class_def

(* As suggested by Andreas Lochbihler, we use the compow function in Nat.thy to define our
scaling function. *)
  term "op ^^"
  term "compow 2 (2::int)"
  term "(2::int)^^2 "

  definition natScale :: "nat \<Rightarrow> ('a::semiring_0) \<Rightarrow> 'a" where
  "natScale n x = ((plus x) ^^ n) 0"
  
  value "natScale 6 (-3::real)" 

(* Derivative on polynomials with respect to a variable. *)
fun deriv :: "('v::linorder) \<Rightarrow> ('v,'a:: semiring_0)poly \<Rightarrow> ('v,'a)poly" where
"deriv x [] = zero_poly"|
"deriv x [(mon, coef)] = (if (fst (derivMonom x mon)) = 0 then zero_poly else [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)])"|
"deriv x (headMonom # tailMonom) = (deriv x [headMonom]) @ (deriv x tailMonom)"

(* Derivative on polynomials: syntactic version. *)
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

lemma "deriv x (poly_add p q) = poly_add (deriv x p) (deriv x q)"
apply(induction p rule: deriv.induct)
apply(simp add: poly_zero_add poly_add.simps(1))
apply(simp)
oops


lemma "set (deriv x (poly_add p q)) = set ((deriv x p) @ (deriv x q))"
apply(simp)
oops






declare [[show_types]]
declare [[show_sorts]]


end