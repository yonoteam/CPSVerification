theory SecondAttempt
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

(* This abbreviations test if the first argument is a variable appearing in the monomial. *)
abbreviation IsVar :: "'a \<Rightarrow> 'a monom_list \<Rightarrow> bool" 
  where "IsVar x ml \<equiv> (x \<in> fst ` set ml)"
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
 
text{* We begin a proof to see that the derivative operator on monomials respects the 
predicate "monom_inv". For this we show three things: 
  - That all variables appear ordered.
  - That all the variables are different.
  - That all the powers are greater than or equal to 1.
*}

(* Lemmas for the first condition. *)
lemma[simp]: "IsNotVar x list \<Longrightarrow> downExp x list = list"
  apply(induction list rule: downExp.induct, auto)
  done

lemma downExpPreservesVars: "set (map fst (downExp x list)) \<subseteq> set (map fst list)"
  apply(induction list rule: downExp.induct, auto)
  done

lemma lowerThanTail_IsLowerThan_DownExpTail:
  "(a, b) \<in> set (downExp x tail) \<longrightarrow> (\<forall>x\<in>set tail. z \<le> fst x) \<longrightarrow> z \<le> fst (a, b)"
  proof
  assume "(a, b) \<in> set (downExp x tail)"
  then have aInTail: "a \<in> set (map fst tail)"
  by (metis (no_types, lifting) downExpPreservesVars fst_conv image_eqI set_map subsetCE)
  show "(\<forall>x\<in>set tail. z \<le> fst x) \<longrightarrow> z \<le> fst (a, b)"
    proof
    assume "\<forall>x\<in>set tail. z \<le> fst x"
    from this and aInTail have  "z \<le> a" by auto 
    thus "z \<le> fst (a, b)" by auto
    qed
  qed
    
lemma downExpRespectsSortedness: "sorted (map fst list) \<Longrightarrow> sorted (map fst (downExp x list))"
  apply(induction list rule: downExp.induct,simp)
  apply(simp add: downExp.elims,rule conjI, clarify, rule conjI)
  apply(simp add: local.sorted_Cons)
  apply(simp add: local.sorted_Cons, clarify)
  using lowerThanTail_IsLowerThan_DownExpTail apply blast
  apply(clarsimp)
  by (meson downExpPreservesVars local.sorted_Cons subsetCE)

lemma fstCondMonomInv: "\<forall> list. monom_inv (list) \<longrightarrow> sorted (map fst (downExp x list))"
  apply(auto simp: monom_inv_def)
  using downExpRespectsSortedness by blast

(* Lemmas for the second condition. *)
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
 using diff_zero downExp.elims by auto

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
  
(* Still trying to define derivatives for polynomials. In this bit, I explore the locales to find 
a function "\<cdot>: nat \<Rightarrow> ('a::monoid_add) \<Rightarrow> 'a" that returns an element "x:'a" scaled as many times 
as "n:nat", i.e. it returns "n\<cdot>x=x+x+x+\<dots>+x". *)
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

lemma natScaleDef2:"natScale (Suc n) x = (natScale n x) + x"
proof-
  have "natScale (Suc n) x = ((plus x) ^^ (Suc n)) 0" by (simp add: natScale_def)
  also have "((plus x) ^^ (Suc n)) 0 = ((plus x) ^^ n) 0 + x" by (simp add: add.commute) 
  also have "natScale n x = ((plus x) ^^ n) 0" by (simp add: natScale_def) 
  ultimately show "natScale (Suc n) x = (natScale n x) + x" by simp
qed

lemma natScale_isHomomorphism: "natScale n (c+d) = natScale n c + natScale n d"
apply(induction n, simp add: natScale_def)
by (simp add: add.assoc add.left_commute natScaleDef2)

lemma natScale_preservesInverses:"c + d = 0 \<longrightarrow> natScale n c + natScale n d = 0"
apply(induction n, simp add: natScale_def)
by (simp add: add.commute add.left_commute natScaleDef2)

(* Derivative on polynomials with respect to a variable. *)
fun deriv :: "('v::linorder) \<Rightarrow> ('v,'a:: semiring_0)poly \<Rightarrow> ('v,'a)poly" where
"deriv x [] = zero_poly"|
"deriv x [(mon, coef)] = (if natScale (fst (derivMonom x mon)) coef = 0 then zero_poly 
  else [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)])"|
"deriv x (headMonom # tailMonom) = (deriv x [headMonom]) @ (deriv x tailMonom)"

(* This is our previous definition for the derivative of polynomials. We found 'an error'...
fun deriv :: "('v::linorder) \<Rightarrow> ('v,'a:: semiring_0)poly \<Rightarrow> ('v,'a)poly" where
    "deriv x [] = zero_poly"|
    "deriv x [(mon, coef)] = (if (fst (derivMonom x mon)) = 0 then zero_poly else 
    [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)])"|
    "deriv x (headMonom # tailMonom) = (deriv x [headMonom]) @ (deriv x tailMonom)"
*)

lemma derivDeletes1[simp]: "natScale (fst (derivMonom x mon)) coef = 0 \<longrightarrow> 
  deriv x ((mon, coef) # q) = deriv x q"
proof
  assume "natScale (fst (derivMonom x mon)) coef = 0"
  hence "deriv x [(mon,coef)] = zero_poly" by simp
  thus "deriv x ((mon, coef) # q) = deriv x q"
  by (metis append_Nil deriv.simps(1) deriv.simps(3) list.exhaust zero_poly_def)
qed

lemma derivDeletes2[simp]: "fst (derivMonom x mon) = 0 \<longrightarrow> deriv x ((mon, coef) # q) = deriv x q"
proof
  assume "fst (derivMonom x mon) = 0" 
  hence "natScale (fst (derivMonom x mon)) coef = 0" by (simp add: natScale_def)
  thus "deriv x ((mon, coef) # q) = deriv x q" by simp
qed

(* The following lemmas are necessary to prove that the derivative of a sum is the sum of the 
derivatives. We divide them by the goals that they help to solve. *)

(* At some point, I thought it was necessary to prove some form of injectivity for the 
derivative operator. However, the injectivity was required for other function, specifically for the
composition of "snd" and "derivMonom". This fact I discovered later, after doing many injectivity 
proofs. Thus, I ended up having more theorems than required. *)
lemma noCoincidence_Implies_AddOfPoly_IsAppend: 
"myMon \<notin> poly_monoms q \<longrightarrow> poly_add [(myMon, someCoef)] q = [(myMon, someCoef)] @ q"
  proof
    assume "myMon \<notin> fst ` set q"
    from this have "List.extract (\<lambda>mc. fst mc = myMon) q = None"
    using extract_None_iff by blast
    thus "poly_add [(myMon, someCoef)] q = [(myMon, someCoef)] @ q"
    by (simp add: poly_add.simps(1) poly_add.simps(2))
  qed

(* This lemma is necessary for the first case in the theorem immediately below. *)
lemma distinctImpliesUniqueHead:
"distinct (map fst (head # tail))  \<longrightarrow> head = (x,n) \<longrightarrow> (\<exists>!exp. (x, exp) \<in> set (head # tail))"
proof
  assume distinctHT:"distinct (map fst (head # tail))"
  show "head = (x,n) \<longrightarrow> (\<exists>!exp. (x, exp) \<in> set (head # tail))"
  proof
    assume headForm:"head = (x,n)"
    from this have "(x, n) \<in> set (head # tail)" by simp
    thus "(\<exists>!exp. (x, exp) \<in> set (head # tail))"
    proof
      fix exp
      assume "(x, exp) \<in> set (head # tail)"
      from this headForm distinctHT show "exp = n"
      using split_list_first by fastforce
    qed
  qed
qed

theorem monomialsHaveUniqueExponents:"monom_inv ml \<longrightarrow> IsVar x ml \<longrightarrow> (\<exists>! exp. (x,exp) \<in> set ml)"
proof(clarify, induction ml, simp, rename_tac head tail var n)
  fix head tail var n
  assume IH:"(\<And>a b. monom_inv tail \<Longrightarrow> (a, b) \<in> set tail \<Longrightarrow> x = fst (a, b) \<Longrightarrow> 
    \<exists>!exp. (fst (a, b), exp) \<in> set tail)"
  assume HTisMonom:"monom_inv (head # tail)" then 
  have distinctHT: "distinct (map fst (head # tail))" by (simp add: monom_inv_def)
  from HTisMonom have tailIsMonom:"monom_inv tail" using monom_inv_ConsD by blast 
  assume "(var, n) \<in> set (head # tail)" and "x=fst(var,n)" 
  hence xnInHT:"(x,n) \<in> set (head # tail)" by simp
  {assume "head = (x,n)" from this and distinctHT 
    have "\<exists>!exp. (x, exp) \<in> set (head # tail)" by (metis distinctImpliesUniqueHead)}
  moreover
  {assume "head \<noteq> (x,n)" from this and xnInHT have "(x,n)\<in> set tail" by auto 
    hence "\<exists>!exp. (x, exp) \<in> set tail" using IH tailIsMonom by auto 
    then have "\<exists>!exp. (x, exp) \<in> set (head # tail)"
    by (metis (no_types, lifting) \<open>(x, n) \<in> set tail\<close> distinct.simps(2) distinctHT fst_conv 
      list.set_intros(1) list.simps(9) map_of_eq_None_iff map_of_is_SomeI set_ConsD set_map xnInHT)}
  ultimately have "\<exists>!exp. (x, exp) \<in> set (head # tail)" by linarith
  thus "\<exists>!exp. (fst (var, n), exp) \<in> set (head # tail)" using \<open>x = fst (var, n)\<close> by auto
qed

thm distinct_def

lemma monomImpliesDistinct:"monom_inv monList \<longrightarrow> distinct monList"
proof
  assume "monom_inv monList"
  then have "distinct (map fst (monList))" by (simp add: monom_inv_def)
  thus "distinct monList" using distinct_map by blast 
qed

(* The function sum_var_list is the function that the team from the Executable Multivariate
Polynomials use to characterizes distinct monomials. Basically, two monomials are the same iff
the function "sum_var_list" applied on them coincides in all variables (see thm commands below). 
We needed some properties of this function to generate our injectivity results. *)
thm sum_var_list_def
thm sum_var_list_not
thm eq_monom_sum_var_list

lemma noVarInHeadImplies_sumVarListGoesToTail [simp]: 
"fst head \<noteq> x \<longrightarrow> sum_var_list (head # tail) x = sum_var_list tail x"
proof(clarify)
  assume "fst head \<noteq> x" then obtain y c where "head = (y,c) \<and> y\<noteq>x" using prod.exhaust_sel by blast
  hence "(case head of (y, c) \<Rightarrow> if x = y then c else 0) = (0::nat)" by auto 
  from this have sumVarSingleHead:"sum_var_list [head] x = 0" by (simp add: sum_var_list_def)
  have "sum_var_list (head # tail) x = sum_var_list [head] x + sum_var_list tail x" 
  by (simp add: sum_var_list_def) 
  from this and sumVarSingleHead show "sum_var_list (head # tail) x = sum_var_list tail x" by auto
qed

lemma sumVarListX_OnMonomsWithX:"monom_inv ml \<longrightarrow> (x, m) \<in> set ml \<longrightarrow> sum_var_list ml x = m"
proof(clarify, induction ml rule: list.induct, simp, rename_tac head tail)
  fix head tail
  assume IH:"monom_inv tail \<Longrightarrow> (x, m) \<in> set tail \<Longrightarrow> sum_var_list tail x = m"
  assume isMonom:"monom_inv (head # tail)" hence distinct: "distinct (map fst (head # tail))"
  by (simp add: monom_inv_def)
  assume xmInHT:"(x, m) \<in> set (head # tail)" 
  from this have "(x,m) \<in> set [head] \<or> (x, m) \<in> set tail" by auto
  moreover
  {assume "(x,m) \<in> set [head]" then have headForm:"head = (x,m)" by auto
    hence "(case head of (y, c) \<Rightarrow> if x = y then c else 0) = m" by auto 
    from this have sumVarListSingleHead:"sum_var_list [head] x = m" by (simp add: sum_var_list_def)
    from distinct and headForm have "IsNotVar x tail" by simp 
    hence "sum_var_list tail x = 0" by (simp add: sum_var_list_not) 
    then have "sum_var_list (head # tail) x = m" by (simp add: headForm sum_var_list_def)}
  moreover
  {assume pairInTail:"(x, m) \<in> set tail" from this and distinct have headNotX:"fst head \<noteq> x"
    by (metis distinct.simps(2) eq_fst_iff isMonom map_of_Cons_code(2) map_of_eq_Some_iff 
      monomImpliesDistinct monom_inv_ConsD monom_inv_def xmInHT)
    from isMonom have "monom_inv tail" using monom_inv_ConsD by blast
    then have "sum_var_list tail x = m" by (simp add: IH pairInTail)
    from this have "sum_var_list (head # tail) x = m" by (simp add: headNotX)}
  ultimately show "sum_var_list (head # tail) x = m" by auto
qed

lemma derivCoeffOfMonomWithVar: "monom_inv ml \<longrightarrow> (x, m) \<in> set ml \<longrightarrow> derivCoeffMonomList x ml = m"
proof(clarify, induction ml, simp, rename_tac head tail)
  fix head tail
  assume IH:"monom_inv tail \<Longrightarrow> (x, m) \<in> set tail \<Longrightarrow> derivCoeffMonomList x tail = m" 
  assume headTailIsMonom:"monom_inv (head # tail)" from this have 
  tailIsMonom:"monom_inv tail" using monom_inv_ConsD by blast 
  from headTailIsMonom have inTailNotInHead:"(x,m) \<in> set tail \<longrightarrow> (x,m)\<noteq>head"
  by (meson distinct.simps(2) monomImpliesDistinct)
  assume xmInHeadTail:"(x, m) \<in> set (head # tail)"
  from this have "(x,m) \<in> set [head] \<or> (x, m) \<in> set tail" by auto
  moreover
  {assume "(x,m) \<in> set [head]" from this have "derivCoeffMonomList x (head # tail) = m" by auto}
  moreover
  {assume xmInTail:"(x, m) \<in> set tail" then have "(x,m)\<noteq>head" by (simp add: inTailNotInHead)
    obtain y n where headForm:"head = (y,n)" by fastforce
    from this xmInHeadTail xmInTail and headTailIsMonom have "y \<noteq> x"
    by (metis \<open>(x, m) \<noteq> head\<close> distinctImpliesUniqueHead list.set_intros(1) monom_inv_def) 
    from this and headForm have 
    eq1:"derivCoeffMonomList x (head # tail) = derivCoeffMonomList x tail" by auto
    from IH tailIsMonom and xmInTail have "derivCoeffMonomList x tail = m" by simp
    hence "derivCoeffMonomList x (head # tail) = m" using eq1 by simp}
  ultimately show "derivCoeffMonomList x (head # tail) = m" by auto
qed

(* downExp was one of the candidate functions to be injective (under some appropriate conditions).
I thought this because I incorrectly assumed "snd derivMonom x= downExp x".*)
lemma downExp_X_doesNotAffectOtherVars:
"x \<noteq> y \<longrightarrow> (y,k) \<in> set (ml::'a:: linorder monom_list) \<longrightarrow> (y,k) \<in> set (downExp x ml)"
proof(clarify, induction ml, simp, rename_tac head tail)
  fix head tail
  assume IH:"x \<noteq> y \<Longrightarrow> (y, k) \<in> set tail \<Longrightarrow> (y, k) \<in> set (downExp x tail)"
  assume "x \<noteq> y" and ykInHT:"(y,k) \<in> set (head # tail)"
  from this have "(y,k) \<in> set [head] \<or> (y, k) \<in> set tail" by auto
  moreover
  {assume ykInHead:"(y,k) \<in> set [head]" from this and \<open>x\<noteq>y\<close> have 
    "downExp x (head # tail) = head # downExp x tail" by auto 
    hence "(y, k) \<in> set (downExp x (head # tail))" using IH \<open>x \<noteq> y\<close> ykInHT by auto}
  moreover
  {assume ykInTail:"(y, k) \<in> set tail" 
    from this \<open>x\<noteq>y\<close> and IH have "(y, k) \<in> set (downExp x tail)" by simp
    hence "(y, k) \<in> set (downExp x (head # tail))" 
    by (metis downExp.simps(2) list.set_intros(2) prod.exhaust_sel ykInTail)}
  ultimately show "(y, k) \<in> set (downExp x (head # tail))" by auto
qed


lemma downExpIgnoresVars:(* This could be generalized without assuming the first condition. *)
"x\<noteq>y \<longrightarrow> (y,k) \<notin> set (ml::'a:: linorder monom_list) \<longrightarrow> (y,k) \<notin> set (downExp x ml)"
proof(induction ml, simp, rename_tac head tail)
  fix head tail
  assume IH:"x \<noteq> y \<longrightarrow> (y, k) \<notin> set tail \<longrightarrow> (y, k) \<notin> set (downExp x tail)"
  show "x \<noteq> y \<longrightarrow> (y, k) \<notin> set (head # tail) \<longrightarrow> (y, k) \<notin> set (downExp x (head # tail))"
  proof(clarify)
    assume "x\<noteq>y" and ykNotInList:"(y, k) \<notin> set (head # tail)"
    from this have ykNotInTail:"(y, k) \<notin> set tail" by simp
    then have "(y, k) \<notin> set (downExp x tail)" using \<open>x \<noteq> y\<close> IH by simp
    assume forContradiction:"(y, k) \<in> set (downExp x (head # tail))"
    {assume "x = fst head" then have "(y, k) \<notin> set (downExp x (head # tail))"
      by (metis ykNotInTail \<open>x \<noteq> y\<close> downExp.simps(2) eq_fst_iff set_ConsD)}
    moreover
    {assume "x \<noteq> fst head" then have "(y, k) \<notin> set (downExp x (head # tail))"
      by (metis IH ykNotInList \<open>x \<noteq> y\<close> downExp.simps(2) insert_iff list.set(2) prod.exhaust_sel)}
    ultimately show "False" using forContradiction by auto
  qed
qed

lemma downExpOverallBehavior:"monom_inv ml \<Longrightarrow> (x,n) \<in> set ml \<Longrightarrow> (x,n-1) \<in> set (downExp x ml) \<or> 
  IsNotVar x (downExp x ml)"
proof(induction ml, simp, rename_tac head tail)
  fix head tail
  assume IH:"monom_inv tail \<Longrightarrow> (x,n) \<in> set tail \<Longrightarrow> 
    (x,n-1) \<in> set (downExp x tail) \<or> IsNotVar x (downExp x tail)"
  assume "monom_inv (head # tail)" and "(x, n) \<in> set (head # tail)"
  from this have condsForCases:"monom_inv tail \<and> n \<noteq> 0" 
  by (meson monom_inv_ConsD noZeroExpInMonoms)
  have "(x,n) \<in> set [head] \<or> (x,n) \<in> set tail" using \<open>(x, n) \<in> set (head # tail)\<close> by auto 
  moreover
  {assume "(x,n) \<in> set [head]" then have "head = (x,n)" by simp
    from this and \<open>monom_inv (head # tail)\<close> have "(x,n) \<notin> set tail"
    by (meson distinct.simps(2) monomImpliesDistinct) 
    from condsForCases have "n = 1 \<or> n>1" by auto
    moreover
    {assume "n=1" then have "IsNotVar x (downExp x (head # tail))"
      using \<open>(x,n) \<notin> set tail\<close> \<open>head = (x, n)\<close> \<open>monom_inv (head # tail)\<close> monom_inv_def by force 
      hence "(x,n-1) \<in> set (downExp x (head # tail)) \<or> 
        IsNotVar x (downExp x (head # tail))" by simp}
    moreover
    {assume "n>1" then have "(x,n-1) \<in> set (downExp x (head # tail))" 
      by (simp add: \<open>head = (x, n)\<close>) 
      hence "(x,n-1) \<in> set (downExp x (head # tail)) \<or> 
        IsNotVar x (downExp x (head # tail))" by simp}
    ultimately have "(x,n-1) \<in> set (downExp x (head # tail)) \<or> 
      IsNotVar x (downExp x (head # tail))" by blast}
  moreover
  {assume "(x,n) \<in> set tail" from this IH and condsForCases have
    "(x,n-1) \<in> set (downExp x tail) \<or> IsNotVar x (downExp x tail)" by simp
    moreover
    {assume "(x,n-1) \<in> set (downExp x tail)"
      have "downExp x (head # tail) = head # downExp x tail"
      by (metis (no_types, lifting) \<open>(x, n) \<in> set (head # tail)\<close> \<open>(x, n) \<in> set tail\<close> 
        \<open>monom_inv (head # tail)\<close> case_prodE derivCoeffOfMonomWithVar distinct.simps(2) 
        downExp.simps(2) list.set_intros(1) monomImpliesDistinct monom_inv_def) 
      from this and \<open>(x,n-1) \<in> set (downExp x tail)\<close> have 
      "(x,n-1) \<in> set (downExp x (head # tail)) \<or> IsNotVar x (downExp x (head # tail))" by simp}
    moreover
    {assume "IsNotVar x (downExp x tail)" 
      from \<open>(x,n) \<in> set tail\<close> and \<open>monom_inv (head # tail)\<close> have "x \<noteq> fst head"
      by (metis \<open>(x, n) \<in> set (head # tail)\<close> condsForCases distinct.simps(2) eq_fst_iff 
        map_of_Cons_code(2) map_of_eq_Some_iff monomImpliesDistinct monom_inv_def) 
      from this and \<open>IsNotVar x (downExp x tail)\<close> have 
      "IsNotVar x (downExp x (head # tail))"
      by (metis downExp.simps(2) map_of_Cons_code(2) map_of_eq_None_iff prod.exhaust_sel)
      hence "(x,n-1) \<in> set (downExp x (head # tail)) \<or> IsNotVar x (downExp x (head # tail))" 
      by simp}
    ultimately have "(x,n-1) \<in> set (downExp x (head # tail)) \<or> IsNotVar x (downExp x (head # tail))"
    by auto}
  ultimately show "(x,n-1) \<in> set (downExp x (head # tail)) \<or> IsNotVar x (downExp x (head # tail))"
  by auto
qed

lemma varElimAfterDownExp_impliesExpIsOne:
"monom_inv ml \<Longrightarrow> IsNotVar x (downExp x ml) \<Longrightarrow> (x,m) \<in> set ml \<Longrightarrow> m = 1"
proof(induction ml, simp, rename_tac head tail)
  fix head tail
  assume IH:"monom_inv tail \<Longrightarrow> IsNotVar x (downExp x tail) \<Longrightarrow> (x, m) \<in> set tail \<Longrightarrow> m = 1"
  assume HTisMonom:"monom_inv (head # tail)" and notVar:"IsNotVar x (downExp x (head # tail))"
  then have tailIsMonom:"monom_inv tail" using monom_inv_ConsD by blast 
  assume "(x, m) \<in> set (head # tail)"
  from this have "(x,m) \<in> set [head] \<or> (x,m) \<in> set tail" by simp
  moreover
  {assume "(x,m) \<in> set [head]" then have "head = (x,m)" by simp
    hence "downExp x (head # tail) = tail \<or> downExp x (head # tail) = (x,m-1) # tail" by simp
    from this and notVar have "downExp x (head # tail) = tail" by auto
    from this and \<open>head = (x,m)\<close> have "m=1" using not_Cons_self by fastforce}
  moreover
  {assume "(x,m) \<in> set tail" from this and HTisMonom have "x \<noteq> fst head"
    by (metis \<open>(x, m) \<in> set (head # tail)\<close> \<open>monom_inv tail\<close> distinct.simps(2) eq_fst_iff 
      map_of_Cons_code(2) map_of_eq_Some_iff monomImpliesDistinct monom_inv_def)
    then have "downExp x (head # tail) = head # downExp x tail" 
    by (metis downExp.simps(2) prod.exhaust_sel) 
    from this and notVar have "IsNotVar x (downExp x tail)" by simp 
    from this IH tailIsMonom and \<open>(x, m) \<in> set (tail)\<close> have "m =1" by simp}
  ultimately show "m=1" by auto
qed

theorem downExpIsInjection: "\<lbrakk>monom_inv (ml1::'a:: linorder monom_list); 
monom_inv ml2;(x,m) \<in> set ml1; (x,n) \<in> set ml2; m \<noteq> n \<rbrakk> \<Longrightarrow> downExp x ml1 \<noteq> downExp x ml2"
proof-
  (* Results for ml1 *)
    assume m1IsMonom: "monom_inv ml1" and xmInM1:"(x, m) \<in> set ml1"
    then have resultsForM1:"(x,m-1) \<in> set (downExp x ml1) \<or> IsNotVar x (downExp x ml1)"
    using downExpOverallBehavior by blast
  (* Results for ml2 *)
    assume xnInM2:"(x, n) \<in> set ml2" and m2IsMonom: "monom_inv ml2"
    hence resultsForM2:"(x,n-1) \<in> set (downExp x ml2) \<or> IsNotVar x (downExp x ml2)"
    using downExpOverallBehavior by blast
  (* Different exponents *)
    assume "m \<noteq> n"
    from this m1IsMonom m2IsMonom resultsForM1 and resultsForM2 show "downExp x ml1 \<noteq> downExp x ml2" 
    using  varElimAfterDownExp_impliesExpIsOne
    by (metis derivCoeffOfMonomWithVar derivReturnsMonoms diff_is_0_eq eq_diff_iff  
      nat_le_linear noZeroExpInMonoms xmInM1 xnInM2)
qed

(* This lemma uses the first two results from the downExp section. In this case I wanted to prove
that (under certain conditions) derivMonom is injective. For this, I proved it first for its 
analogous derivMonomList. *)
lemma derivMonomList_IsInjection: "\<lbrakk>IsVar x ml1; IsVar x ml2; monom_inv ml1; monom_inv ml2;
ml1 \<noteq> ml2 \<rbrakk> \<Longrightarrow> derivMonomList x ml1 \<noteq> derivMonomList x ml2"
proof(transfer)
  fix x ml1 ml2
  assume xInMonom1:"IsVar x (ml1:: ('a \<times> nat) list)" 
  and xInMonom2: "IsVar x (ml2:: ('a \<times> nat) list)"
  assume m1IsMonom: "monom_inv ml1" and m2IsMonom: "monom_inv ml2"
  -- "Results for ml1."
    from xInMonom1 obtain m where "(x,m) \<in> set ml1" by auto 
    then have "\<forall> num. (x,num)\<in> set ml1 \<longrightarrow> num = m"
    using m1IsMonom monomialsHaveUniqueExponents xInMonom1 by blast 
    hence sumVarM1:"sum_var_list ml1 x = m" 
    using \<open>(x, m) \<in> set ml1\<close> m1IsMonom sumVarListX_OnMonomsWithX by blast 
  -- "Results for ml2."
    from xInMonom2 obtain n where "(x,n) \<in> set ml2" by auto 
    hence "\<forall> num. (x,num)\<in> set ml2 \<longrightarrow> num = n"
    using m2IsMonom monomialsHaveUniqueExponents xInMonom2 by blast
    then have sumVarM2:"sum_var_list ml2 x = n"
    using \<open>(x, n) \<in> set ml2\<close> m2IsMonom sumVarListX_OnMonomsWithX by blast 
  assume differentMonoms: "ml1 \<noteq> ml2"
  then obtain y where resultsSumVar:"sum_var_list ml1 y \<noteq> sum_var_list ml2 y"
  using eq_monom_sum_var_list m1IsMonom m2IsMonom by blast 
  {assume "x=y" then have mNotEqN:"m \<noteq> n" using resultsSumVar sumVarM1 sumVarM2 by auto
    have derivMonom1:"fst (derivMonomList x ml1) = m"
    by(simp add:\<open>(x, m) \<in> set ml1\<close> derivCoeffOfMonomWithVar derivMonomList_def m1IsMonom xInMonom1)
    have "fst (derivMonomList x ml2) = n"
    by(simp add:\<open>(x, n) \<in> set ml2\<close> derivCoeffOfMonomWithVar derivMonomList_def m2IsMonom xInMonom2)
    from this mNotEqN and derivMonom1 have "derivMonomList x ml1 \<noteq> derivMonomList x ml2" by auto}
  moreover
  {assume diffVars:"x\<noteq>y" 
    from resultsSumVar m1IsMonom and m2IsMonom obtain k where 
    ykPair:"((y,k) \<in> set ml1 \<and> (y,k) \<notin> set ml2)  \<or> ((y,k) \<in> set ml2 \<and> (y,k) \<notin> set ml1)"
    by (metis monomialsHaveUniqueExponents sumVarListX_OnMonomsWithX sum_var_list_not)
    from this and diffVars have "((y,k) \<in> set (downExp x ml1) \<and> (y,k) \<notin> set (downExp x ml2))
      \<or> ((y,k) \<in> set (downExp x ml2) \<and> (y,k) \<notin> set (downExp x ml1))" 
    using downExpIgnoresVars downExp_X_doesNotAffectOtherVars by blast 
    then have "derivMonomList x ml1 \<noteq> derivMonomList x ml2"
    by (metis derivMonomList_def prod.inject xInMonom1 xInMonom2)}
  ultimately show "derivMonomList x ml1 \<noteq> derivMonomList x ml2" by auto
qed

theorem derivMonomIsInjection: 
  "IsVar x (Rep_monom monom1) \<Longrightarrow> monom1 \<noteq> monom2 \<Longrightarrow> derivMonom x monom1 \<noteq> derivMonom x monom2"
  proof-
    assume "IsVar x (Rep_monom monom1)"
    assume "monom1 \<noteq> (monom2::'a monom)"
    then obtain ml1 ml2 where mlsDef:"Rep_monom monom1 = ml1 \<and> Rep_monom monom2 = ml2 \<and> ml1 \<noteq> ml2"
    using Rep_monom_inject by blast
    from this have mlsAreMonoms:"monom_inv ml1 \<and> monom_inv ml2 \<and> IsVar x ml1"
    using Rep_monom \<open>IsVar x (Rep_monom monom1)\<close> by blast
    {assume "IsVar x ml2"
      from this have "derivMonomList x ml1 \<noteq> derivMonomList x ml2"
      by (simp add: mlsDef mlsAreMonoms derivMonomList_IsInjection)}
    moreover
    {assume "IsNotVar x ml2"
      then have "derivMonomList x ml2 = (0,[])" by simp
      from this and  \<open>IsVar x (Rep_monom monom1)\<close> have 
      "derivMonomList x ml1 \<noteq> derivMonomList x ml2"
      by(metis Pair_inject derivCoeffOfMonomWithVar derivMonomList_def mlsAreMonoms 
        monomialsHaveUniqueExponents noZeroExpInMonoms)}
    ultimately have "derivMonomList x ml1 \<noteq> derivMonomList x ml2" by blast 
    thus "derivMonom x monom1 \<noteq> derivMonom x monom2" by (metis derivMonom.rep_eq mlsDef)
  qed

(* The real function that required to be injective was "derivMonom x" followed by "snd". However, 
its injectivity only covers cases where the exponent is greater than 1. *)
lemma sndOfDerivMonomIsInjection: "1 < fst (derivMonom x monom1) \<Longrightarrow> monom1 \<noteq> monom2 \<Longrightarrow> 
  snd (derivMonom x monom1) \<noteq> snd (derivMonom x monom2)"
  proof-
  assume moreThanOne:"1 < fst (derivMonom x monom1)"
  have "fst (derivMonom x monom1) = fst (derivMonomList x (Rep_monom monom1))"
  by (metis derivMonom.rep_eq fst_map_prod id_def)
  hence "fst (derivMonomList x (Rep_monom monom1)) > 1" using moreThanOne by (simp)
  then have xInMonom1:"IsVar x (Rep_monom monom1)" using neq_iff by fastforce 
  from this have "IsVar x (Rep_monom monom1)" by blast 
  then obtain m where mDef:"(x,m) \<in> set (Rep_monom monom1) \<and> m >1"
  by (metis Rep_monom \<open>1 < fst (derivMonomList x (Rep_monom monom1))\<close> derivCoeffOfMonomWithVar 
    derivMonomList_def fst_conv mem_Collect_eq monomialsHaveUniqueExponents) 
  assume "monom1 \<noteq> (monom2::'a monom)"
  then obtain ml1 ml2 where mlsDef:"Rep_monom monom1 = ml1 \<and> Rep_monom monom2 = ml2 \<and> ml1 \<noteq> ml2"
  using Rep_monom_inject by blast
  from this have mlsAreMonoms:"monom_inv ml1 \<and> monom_inv ml2 \<and> IsVar x ml1"
  using Rep_monom \<open>IsVar x (Rep_monom monom1)\<close> by blast
  from this obtain n where "(x,n) \<in> set ml1" by auto 
  {assume "IsVar x ml2"
    from this have "downExp x ml1 \<noteq> downExp x ml2"
    by (metis derivCoeffOfMonomWithVar derivMonomList_IsInjection derivMonomList_def 
      downExpIsInjection mlsAreMonoms mlsDef monomialsHaveUniqueExponents)
    from this have "snd (derivMonomList x ml1) \<noteq> snd (derivMonomList x ml2)"
    by (simp add: \<open>IsVar x ml2\<close> derivMonomList_def mlsAreMonoms)}
  moreover
  {assume "IsNotVar x ml2"
    then have "derivMonomList x ml2 = (0,[])" by simp
    from mlsAreMonoms have "ml1 \<noteq> []" by auto 
    from this mDef and mlsAreMonoms have 
    "snd (derivMonomList x ml1) \<noteq> snd (derivMonomList x ml2)"
    by (metis \<open>derivMonomList x ml2 = (0, [])\<close> derivMonomList_def empty_iff empty_set image_empty 
      mlsDef neq_iff snd_conv varElimAfterDownExp_impliesExpIsOne)}
  ultimately have "snd (derivMonomList x ml1) \<noteq> snd (derivMonomList x ml2)" by blast 
  thus "snd (derivMonom x monom1) \<noteq> snd (derivMonom x monom2)"
  by (metis derivMonom.rep_eq mlsDef snd_map_prod)
qed

lemma monomsInDerivative_ComeFromMonomsInOriginal:
"\<forall> m. m \<in> poly_monoms (deriv x q) \<longrightarrow> 
  (\<exists> n. n \<in> poly_monoms q \<and> m = (snd (derivMonom x n)) \<and> IsVar x (Rep_monom n))"
proof(induction q, simp add: zero_poly_def, rename_tac head tail)
  fix head::"'a monom \<times> 'b"
  fix tail::"('a monom \<times> 'b) list"
  assume IH: "\<forall>m. m \<in> poly_monoms (deriv x tail) \<longrightarrow> 
    (\<exists>n. n \<in> poly_monoms tail \<and> m = snd (derivMonom x n) \<and> IsVar x (Rep_monom n))"
  show "\<forall>m. m \<in> poly_monoms (deriv x (head # tail)) \<longrightarrow> 
    (\<exists>n. n \<in> poly_monoms (head # tail) \<and> m = snd (derivMonom x n) \<and> IsVar x (Rep_monom n)) "
  proof
    fix m
    show "m \<in> poly_monoms (deriv x (head # tail)) \<longrightarrow> 
      (\<exists>n. n \<in> poly_monoms (head # tail) \<and> m = snd (derivMonom x n) \<and> IsVar x (Rep_monom n))"
    proof
      assume "m \<in> poly_monoms (deriv x (head # tail))" hence
      "m \<in> poly_monoms ((deriv x [head]) @ (deriv x tail))"
      by (metis append_self_conv deriv.simps(1) deriv.simps(3) neq_Nil_conv zero_poly_def) 
      then have "m \<in> poly_monoms (deriv x [head]) \<or> m \<in> poly_monoms (deriv x tail)" by auto
      moreover
      {assume fstOption: "m \<in> poly_monoms (deriv x [head])"
        from this obtain n c where "head = (n, c)" by fastforce 
        hence derivHead:"deriv x [head] = [(snd (derivMonom x n),natScale (fst(derivMonom x n)) c)]"
        by (metis deriv.simps(2) empty_iff empty_set fstOption image_empty zero_poly_def) 
        from this and fstOption have whoIsM:"m = (snd (derivMonom x n))" by auto
        hence nInHead:"n \<in> poly_monoms [head]" using \<open>head = (n, c)\<close> by simp
        from derivHead have "fst (derivMonom x n) > 0"
        by (metis (full_types) \<open>head = (n, c)\<close> deriv.simps(1) derivDeletes2 empty_iff empty_is_image 
          empty_set fstOption gr0I zero_poly_def)
        hence "fst (derivMonomList x (Rep_monom n)) > 0"
        by (metis derivMonom.rep_eq eq_id_iff fst_map_prod) 
        hence "IsVar x (Rep_monom n)"
        by (metis derivOfConst fstI less_not_refl2) 
        then have "\<exists>n. n \<in> poly_monoms (head # tail) \<and> m = snd (derivMonom x n) \<and> 
          IsVar x (Rep_monom n)" 
        using whoIsM and nInHead by auto}
      moreover
      {assume sndOption:"m \<in> poly_monoms (deriv x tail)" from this and IH have
        "(\<exists>n. n \<in> poly_monoms tail \<and> m = snd (derivMonom x n) \<and> IsVar x (Rep_monom n))" by simp
        then have "\<exists>n. n \<in> poly_monoms (head # tail) \<and> m = snd (derivMonom x n) \<and> 
          IsVar x (Rep_monom n)" by auto}
      ultimately show "\<exists>n. n \<in> poly_monoms (head # tail) \<and> m = snd (derivMonom x n) \<and> 
        IsVar x (Rep_monom n)" by auto
    qed
  qed
  qed

lemma nonZeroDerivMonomX_Implies_XinTheAntideriv: 
  "fst (derivMonom x mon) > 0 \<Longrightarrow> IsVar x (Rep_monom mon)"
proof-
assume notZero:"fst (derivMonom x mon) > 0"
  have "fst (derivMonom x mon) = fst (derivMonomList x (Rep_monom mon))"
  by (metis derivMonom.rep_eq fst_map_prod id_def)
  hence "fst (derivMonomList x (Rep_monom mon)) \<noteq> 0" using notZero by simp
  thus xInMon:"IsVar x (Rep_monom mon)" using neq_iff by fastforce 
qed

theorem derivRespectsMonoms: "0 < fst (derivMonom x mon) \<Longrightarrow> mon \<notin> poly_monoms q \<Longrightarrow> 
  (snd (derivMonom x mon)) \<notin> poly_monoms (deriv x q)"
proof
  assume notZero:"0 < fst (derivMonom x mon)"
  then have xInMon:"IsVar x (Rep_monom mon)" using nonZeroDerivMonomX_Implies_XinTheAntideriv by blast
  assume "mon \<notin> poly_monoms q" from this have "\<forall> m. m \<in> poly_monoms q \<longrightarrow> mon \<noteq> m" by auto
  then have monomsInQDifferInDerivsFromMon:"\<forall> m. m\<in>poly_monoms q\<longrightarrow>derivMonom x mon\<noteq>derivMonom x m"
  by (simp add: derivMonomIsInjection xInMon)
  assume forContradiction:"snd (derivMonom x mon) \<in> poly_monoms (deriv x q)"
  have "\<forall> m. m \<in> poly_monoms (deriv x q) \<longrightarrow> (\<exists> n. n \<in> poly_monoms q \<and> m = (snd (derivMonom x n))\<and>
    IsVar x (Rep_monom n))"
  by (simp add: monomsInDerivative_ComeFromMonomsInOriginal)
  from this and forContradiction obtain n where nDef:"n \<in> poly_monoms q \<and> 
  snd (derivMonom x mon) = (snd (derivMonom x n)) \<and> IsVar x (Rep_monom n)" by presburger 
  from notZero have "1 = fst (derivMonom x mon) \<or> 1 < fst (derivMonom x mon)" by linarith
  moreover
  {assume "1 < fst (derivMonom x mon)" from this and nDef have 
    "mon = n" using sndOfDerivMonomIsInjection by blast
    from this nDef and monomsInQDifferInDerivsFromMon have "False" by blast}
  moreover
  {assume "1 = fst (derivMonom x mon)" from this have "1 = fst (derivMonomList x (Rep_monom mon))"
    by (metis apsnd_def derivMonom.rep_eq fst_apsnd)
    from this have "derivCoeffMonomList x (Rep_monom mon) = 1"
    by (simp add: derivMonomList_def xInMon) 
    hence "(x,1) \<in> set (Rep_monom mon)" using Rep_monom derivCoeffOfMonomWithVar xInMon by fastforce
    then have eq1:"(snd (derivMonomList x (Rep_monom mon))) = removeAll (x,1) (Rep_monom mon)"
    by (metis (no_types, lifting) Rep_monom Rep_monom_inject \<open>\<forall>m. m \<in> poly_monoms q \<longrightarrow> mon \<noteq> m\<close> 
      derivCoeffOfMonomWithVar derivMonom.rep_eq derivMonomList_IsInjection derivMonomList_def 
      downExpIsInjection eq_fst_iff eq_snd_iff image_iff mem_Collect_eq nDef snd_map_prod) 
    from nDef have "snd (derivMonomList x (Rep_monom mon)) = (snd (derivMonomList x (Rep_monom n)))"
    by (metis derivMonom.rep_eq snd_map_prod)
    hence "(snd(derivMonomList x (Rep_monom n)))=removeAll (x,1) (Rep_monom mon)" using eq1 by simp
    from this have downExpN:"downExp x (Rep_monom n) = removeAll (x,1) (Rep_monom mon)"
    by (simp add: derivMonomList_def nDef)
    from eq1 have downExpMon:"downExp x (Rep_monom mon) = removeAll (x,1) (Rep_monom mon)"
    by (simp add: derivMonomList_def xInMon)
    from nDef and xInMon have dfrntDownExps:"downExp x (Rep_monom mon) \<noteq> downExp x (Rep_monom n)"
    by (metis Rep_monom Rep_monom_inverse \<open>mon \<notin> poly_monoms q\<close> derivCoeffOfMonomWithVar 
      derivMonomList_IsInjection derivMonomList_def downExpIsInjection mem_Collect_eq 
      monomialsHaveUniqueExponents)
    from this downExpN and downExpMon have "False" by simp}
  ultimately show "False" by auto
  qed
  
lemma derivOnMonomPoly: "0 \<noteq> natScale (fst (derivMonom x mon)) coef \<longrightarrow> deriv x ((mon, coef) # q) =
(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef) # deriv x q"
proof
assume notZero:"0 \<noteq> natScale (fst (derivMonom x mon)) coef" from this have derivOfMonCoef:
"deriv x [(mon, coef)] = [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef)]" by simp
also have "deriv x ((mon, coef) # q) = (deriv x [(mon, coef)]) @ (deriv x q)"
by (metis append_Nil2 deriv.simps(1) deriv.simps(3) neq_Nil_conv zero_poly_def)
from this and derivOfMonCoef have
"deriv x ((mon, coef) # q) = 
[(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef)] @ (deriv x q)" by simp 
then show "deriv x ((mon, coef) # q) = 
(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef) # deriv x q" by auto
qed 
  
lemma derivOnAppend: "deriv x (p @ q) = (deriv x p) @ (deriv x q)"
  apply(induction p rule: deriv.induct)
  apply(auto simp: zero_poly_def)
  apply(simp add: derivOnMonomPoly)
  done


lemma listExtractFstCoord: "x \<in> fst ` set (list :: ('a \<times> 'b) list) \<Longrightarrow> 
\<exists> p1 p2 y. List.extract (\<lambda>pair. fst pair = x) list = Some (p1, (x, y), p2) \<and> x \<notin> fst ` set p1"
proof(induction list, simp, rename_tac head tail)
  fix head::"'a \<times> 'b"
  fix tail::"('a \<times> 'b) list"
  assume IH:"x \<in> fst ` set tail \<Longrightarrow> 
    \<exists>p1 p2 y. List.extract (\<lambda>pair. fst pair = x) tail = Some (p1, (x, y), p2) \<and> x \<notin> fst ` set p1"
  assume xInList:"x \<in> fst ` set (head # tail)"
  {assume "x = fst head" then obtain y where "head = (x,y)" using prod.exhaust_sel by blast 
    then have "List.extract (\<lambda>pair. fst pair = x) (head # tail) = Some ([],(x,y),tail)"
    by (metis (mono_tags, lifting) \<open>x = fst head\<close> extract_Cons_code)
    hence "\<exists>p1 p2 y. List.extract (\<lambda>pair. fst pair = x) (head # tail) = Some (p1, (x, y), p2) \<and> 
      x \<notin> fst ` set p1" by simp}
  moreover
  {assume "x \<noteq> fst head" from this xInList and IH obtain listP1 p2 y where 
    indConclusion:"List.extract (\<lambda>pair. fst pair = x) tail = Some (listP1, (x, y), p2) \<and> 
      x \<notin> fst ` set listP1" by auto
    from this and \<open>x \<noteq> fst head\<close> have xtrctRslt:"List.extract (\<lambda>pair. fst pair = x) (head # tail) = 
      Some (head # listP1,(x,y),p2)" by (simp add: extract_Cons_code)
    from indConclusion and \<open>x \<noteq> fst head\<close> have "x \<notin> fst ` set (head # listP1)" by simp
    hence "\<exists>p1 p2 y. List.extract (\<lambda>pair. fst pair = x) (head # tail) = Some (p1, (x, y), p2) \<and> 
      x \<notin> fst ` set p1" using xtrctRslt by simp}
  ultimately show "\<exists>p1 p2 y. List.extract (\<lambda>pair. fst pair = x) (head # tail) = 
    Some (p1, (x, y), p2) \<and> x \<notin> fst ` set p1" by auto
qed

lemma listExtractOnAppendWithInstance:"list = part1 @ [(x,y)] @ part2 \<Longrightarrow> x \<notin> fst ` set part1 \<Longrightarrow> 
  List.extract (\<lambda>pair. fst pair = x) list = Some (part1, (x, y), part2)"
proof-
  assume listShape:"list = part1 @ [(x,y)] @ part2" and "x \<notin> fst ` set part1"
  from this have extrPart1:"List.extract (\<lambda>pair. fst pair = x) part1 = None"
  using extract_None_iff by blast
  from listShape have "list = part1 @ (x,y) # part2" by simp from this and extrPart1 
  have "List.extract (\<lambda>pair. fst pair = x) (part1 @ [(x,y)]) = Some (part1, (x, y), [])" 
  by (metis (mono_tags, lifting) extract_None_iff extract_Some_iff fst_conv)
  thus "List.extract (\<lambda>pair. fst pair = x) list = Some (part1, (x, y), part2)"
  by (metis \<open>list = part1 @ (x, y) # part2\<close> extract_Some_iff) 
qed
  
text{* Reminders for what comes next: 
  · ('v,'a)poly = "('v monom \<times> 'a)list"
  · derivMonom :: "'a \<Rightarrow> 'a monom \<Rightarrow> (nat \<times> 'a monom)" 
  · poly_inv p \<equiv> (\<forall> c \<in> snd ` set p. c \<noteq> 0) \<and> distinct (map fst p)" 
  · fun deriv :: "('v::linorder) \<Rightarrow> ('v,'a:: semiring_0)poly \<Rightarrow> ('v,'a)poly" where
    "deriv x [] = zero_poly"|
    "deriv x [(mon, coef)] = (if natScale (fst (derivMonom x mon)) coef = 0 then zero_poly 
      else [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)])"|
    "deriv x (headMonom # tailMonom) = (deriv x [headMonom]) @ (deriv x tailMonom)"
  · definition natScale :: "nat \<Rightarrow> ('a::semiring_0) \<Rightarrow> 'a" where
    "natScale n x = ((plus x) ^^ n) 0 
*}

declare poly_add.simps[simp]

lemma additivityOf_derivX:
"set (deriv x (poly_add [(mon, coef)] q)) = set (poly_add (deriv x [(mon, coef)]) (deriv x q))"
proof(cases "mon \<in> poly_monoms q")
  case False
  then have nonExtract:"List.extract (\<lambda>pair. fst pair = mon) q = None" 
  using extract_None_iff by blast 
  from this have "poly_add [(mon, coef)] q = (mon, coef) # q" by simp
  hence eq1:"deriv x (poly_add [(mon, coef)] q) = (deriv x [(mon,coef)]) @ (deriv x q)"
  by (metis False derivOnAppend noCoincidence_Implies_AddOfPoly_IsAppend)
  {assume "natScale (fst (derivMonom x mon)) coef = 0" then have 
    "deriv x [(mon, coef)] = zero_poly" by simp hence
    "poly_add (deriv x [(mon, coef)]) (deriv x q) = deriv x q" by (simp add: zero_poly_def)
    from this and eq1 have "deriv x (poly_add [(mon, coef)] q) = poly_add (deriv x [(mon, coef)]) (deriv x q)"
    using \<open>deriv x [(mon, coef)] = zero_poly\<close> zero_poly_def by auto
    hence ?thesis by simp}
  moreover
  {assume "natScale (fst (derivMonom x mon)) coef \<noteq> 0" then have
    derivXSingleShape: "deriv x [(mon, coef)] = 
      [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)]" by simp
    from this and nonExtract have "(snd (derivMonom x mon)) \<notin> poly_monoms (deriv x q)"
    by (metis False deriv.simps(1) derivDeletes2 derivRespectsMonoms gr0I 
      not_Cons_self2 zero_poly_def)
    hence "List.extract (\<lambda>pair. fst pair = snd (derivMonom x mon)) (deriv x q) = None"
    using extract_None_iff image_iff by fastforce
    from this and derivXSingleShape have "poly_add (deriv x [(mon, coef)]) (deriv x q) = 
      (deriv x [(mon,coef)]) @ (deriv x q)" by simp
    from this and eq1 have ?thesis by simp}
  ultimately show ?thesis by blast
next
  case True
  then obtain p1 p2 cnst where cnstAndpsDef:"List.extract (\<lambda>pair. fst pair = mon) q = 
    Some (p1, (mon, cnst), p2) \<and> mon \<notin> poly_monoms p1" using listExtractFstCoord by force 
  from this have qShape:"q = p1 @ [(mon,cnst)] @ p2" using extract_SomeE by fastforce 
  hence derivQShape:"deriv x q = (deriv x p1) @ (deriv x [(mon,cnst)]) @ (deriv x p2)" 
  by (metis derivOnAppend) 
  {assume "coef + cnst = 0"
    from this and cnstAndpsDef have "poly_add [(mon, coef)] q = p1 @ p2" by simp
    hence eq1:"deriv x (poly_add [(mon, coef)] q) = (deriv x p1) @ (deriv x p2)" 
    by (simp add: derivOnAppend)
    {assume scaleCoefIsZero:"natScale (fst (derivMonom x mon)) coef = 0" then have 
      "deriv x [(mon, coef)] = zero_poly" by simp from this have 
      eq2:"poly_add (deriv x [(mon, coef)]) (deriv x q) = 
        (deriv x p1) @ (deriv x [(mon,cnst)]) @ (deriv x p2)" 
      by (simp add: derivQShape zero_poly_def)
      from \<open>coef + cnst = 0\<close> have 
      "natScale (fst (derivMonom x mon)) coef + natScale (fst (derivMonom x mon)) cnst = 0"
      using natScale_preservesInverses by blast
      then have "natScale (fst (derivMonom x mon)) cnst = 0" by (simp add: scaleCoefIsZero)
      hence "deriv x [(mon,cnst)] = zero_poly" by simp
      from this eq1 and eq2 have ?thesis by (simp add: zero_poly_def)}
    moreover
    {assume scaleCoefNotZero:"natScale (fst (derivMonom x mon)) coef \<noteq> 0" from this have
      "deriv x [(mon, coef)] = [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) coef)]" 
      by simp from this have "fst (derivMonom x mon) > 0"
      by (metis deriv.simps(1) derivDeletes2 gr0I list.discI zero_poly_def) 
      from this and cnstAndpsDef 
      have notInDerivP1:"snd (derivMonom x mon) \<notin> poly_monoms (deriv x p1)" 
      by (simp add: derivRespectsMonoms)
      from \<open>coef + cnst = 0\<close> have 
      eq0: "natScale (fst (derivMonom x mon)) coef + natScale (fst (derivMonom x mon)) cnst = 0"
      using natScale_preservesInverses by blast
      then have "natScale (fst (derivMonom x mon)) cnst \<noteq> 0" using scaleCoefNotZero by auto 
      hence "deriv x [(mon,cnst)] = 
        [(snd (derivMonom x mon),natScale (fst (derivMonom x mon)) cnst)]" by simp
      from this and derivQShape have 
      "List.extract (\<lambda>pair. fst pair = snd (derivMonom x mon)) (deriv x q) =
      Some ((deriv x p1),
        (snd (derivMonom x mon),natScale(fst (derivMonom x mon)) cnst),
        (deriv x p2))"
      by (simp add: notInDerivP1 listExtractOnAppendWithInstance) 
      hence "poly_add (deriv x [(mon, coef)]) (deriv x q) = (deriv x p1) @ (deriv x p2)" using eq0
      \<open>deriv x [(mon, coef)] = [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef)]\<close> 
      by auto then have ?thesis using eq1 by simp}
    ultimately have ?thesis by auto}
  moreover
  {assume "coef + cnst \<noteq> 0" from this and cnstAndpsDef 
    have "poly_add [(mon, coef)] q = (mon,coef+cnst) # (p1 @ p2)" by simp
    hence eq1:"deriv x (poly_add [(mon, coef)] q) = 
      (deriv x [(mon, coef+cnst)]) @ (deriv x p1) @ (deriv x p2)" 
    by (metis append_Cons append_Nil derivOnAppend) 
    {assume natScaleSumZero:"natScale (fst (derivMonom x mon)) (coef + cnst) = 0" from this have 
      derivXCoefCnst:"deriv x [(mon, coef+cnst)] = zero_poly" by simp 
      {assume natScaleCoef0:"natScale (fst (derivMonom x mon)) coef = 0" then have 
        derivXwithCoef:"deriv x [(mon, coef)] = zero_poly" by simp hence
        eq2:"poly_add (deriv x [(mon, coef)]) (deriv x q) = deriv x q" by (simp add: zero_poly_def)
        from natScaleSumZero and natScaleCoef0 have "natScale (fst (derivMonom x mon)) cnst = 0"
        by (simp add: natScale_isHomomorphism)
        hence "deriv x [(mon, cnst)] = zero_poly" by simp
        then have ?thesis using eq1 eq2 derivXCoefCnst derivQShape by (simp add: zero_poly_def)}
      moreover
      {assume natScaleCoefNot0:"natScale (fst (derivMonom x mon)) coef \<noteq> 0" then have
        derivXSingleShape:"deriv x [(mon, coef)] = 
          [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef)]" by simp
        from this and cnstAndpsDef have notInP1:"(snd (derivMonom x mon))\<notin>poly_monoms (deriv x p1)"
        by(metis deriv.simps(1) derivDeletes2 derivRespectsMonoms list.discI neq0_conv zero_poly_def)
        from natScaleCoefNot0 have "natScale (fst (derivMonom x mon)) cnst \<noteq> 0"
        by (metis add.comm_neutral natScaleSumZero natScale_isHomomorphism)
        hence "List.extract (\<lambda>pair. fst pair = snd (derivMonom x mon)) (deriv x q) =
          Some ((deriv x p1), (snd (derivMonom x mon),natScale(fst (derivMonom x mon)) cnst),
          (deriv x p2))" using notInP1 derivQShape by (simp add: listExtractOnAppendWithInstance) 
        from this and derivXSingleShape have "poly_add (deriv x [(mon, coef)]) (deriv x q) = 
          (if (natScale (fst (derivMonom x mon)) coef + natScale (fst (derivMonom x mon)) cnst = 0) 
          then poly_add [] ((deriv x p1) @ (deriv x p2)) 
          else (snd (derivMonom x mon), 
            natScale (fst (derivMonom x mon)) coef + natScale (fst (derivMonom x mon)) cnst) 
            # poly_add [] ((deriv x p1) @ (deriv x p2)))" by simp
        hence "poly_add (deriv x [(mon, coef)]) (deriv x q) = ((deriv x p1) @ (deriv x p2))"
        using natScaleSumZero by (simp add: natScale_isHomomorphism) 
        from this derivXCoefCnst and eq1 have ?thesis by (simp add: zero_poly_def)}
      ultimately have ?thesis by auto}
    moreover
    {assume natScaleSumZero:"natScale (fst (derivMonom x mon)) (coef + cnst) \<noteq> 0" from this have 
      derivXCoefCnst:"deriv x [(mon, coef+cnst)] = [(snd (derivMonom x mon), 
      natScale(fst (derivMonom x mon)) (coef + cnst))]" by simp
      {assume natScaleCoef0:"natScale (fst (derivMonom x mon)) coef = 0" then have 
        derivXwithCoef:"deriv x [(mon, coef)] = zero_poly" by simp hence
        eq2:"poly_add (deriv x [(mon, coef)]) (deriv x q) = deriv x q" by (simp add: zero_poly_def)
        from natScaleSumZero and natScaleCoef0 have "natScale (fst (derivMonom x mon)) cnst \<noteq> 0"
        by (simp add: natScale_isHomomorphism)
        from natScaleSumZero and natScaleCoef0 have "natScale (fst (derivMonom x mon)) coef = 0" 
        by blast
        hence "deriv x [(mon, cnst)] = deriv x [(mon, coef+cnst)]"
        by (simp add: natScale_isHomomorphism) 
        then have "set ((deriv x [(mon, coef+cnst)]) @ (deriv x p1) @ (deriv x p2)) = 
          set ((deriv x [(mon, cnst)]) @ (deriv x p1) @ (deriv x p2))" by simp
        also have "set ((deriv x p1) @ (deriv x [(mon, cnst)]) @ (deriv x p2)) = 
          set ((deriv x [(mon, cnst)]) @ (deriv x p1) @ (deriv x p2))" by auto
       (* Needed to add the "set" outer part because "poly_add" changes the order of polynomials. *)
        ultimately have "set ((deriv x [(mon, coef+cnst)]) @ (deriv x p1) @ (deriv x p2)) =
        set ((deriv x p1) @ (deriv x [(mon,cnst)]) @ (deriv x p2))" by simp
        from this have ?thesis using eq1 eq2 derivXCoefCnst derivQShape by (simp)}
      moreover
      {assume natScaleCoefNot0:"natScale (fst (derivMonom x mon)) coef \<noteq> 0" then have
        derivXSingleShape:"deriv x [(mon, coef)] = 
          [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) coef)]" by simp
        {assume "natScale (fst (derivMonom x mon)) cnst = 0"
          (* For this case we have: 
           * natScale (fst (derivMonom x mon)) cnst = 0 \<Longrightarrow>
           * deriv x [(mon, coef + cnst)] = deriv x [(mon, coef)] 
              \<and> deriv x [(mon,cnst)] = zero_poly \<Longrightarrow>
           * deriv x (poly_add [(mon, coef)] q)= (deriv x [(mon, coef)]) @(deriv x p1) @(deriv x p2)
              \<and> deriv x q = (deriv x p1) @ (deriv x p2) [using eq1 and derivQShape] \<Longrightarrow>
           * Thus the result depends on knowing whether "deriv x [(mon, coef)]" appears on 
              "(deriv x p2)" [because we are interested in: 
              poly_add (deriv x [(mon, coef)]) (deriv x q)]. Notice that if it is not there, the
              desired result follows. *) have ?thesis sorry}
        moreover
        {assume "natScale (fst (derivMonom x mon)) cnst \<noteq> 0"
          (* For this case we have: 
           * natScale (fst (derivMonom x mon)) cnst \<noteq> 0 \<Longrightarrow>
           * deriv x [(mon, coef + cnst)] = 
              [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) (coef + cnst))]
              \<and> deriv x [(mon,cnst)] = 
                [(snd (derivMonom x mon), natScale (fst (derivMonom x mon)) cnst)] \<Longrightarrow>
           * poly_add (deriv x [(mon, coef)]) (deriv x q) = 
              (snd (derivMonom x mon), natScale (fst (derivMonom x mon)) (coef + cnst)) # 
                ((deriv x p1) @ (deriv x p2))
           * Which is what we wanted. *) have ?thesis sorry}
        ultimately have ?thesis by blast}
      ultimately have ?thesis by auto}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

  value "set [0::nat,1,1,2::nat,0::nat] = set [0,2,0,1,1]"
  thm set_def

(* Needed to add the "set" outer part because "poly_add" changes the order of polynomials. *)
theorem "set (deriv x (poly_add p q)) = set (poly_add (deriv x p) (deriv x q))"
  apply(induction p rule: deriv.induct) (* 3 subgoals appear. *)
  apply(simp add: poly_zero_add) (* Goal 1 gone. *)
  apply(simp only: additivityOf_derivX) (* Goal 2 gone.*)
  apply(rename_tac head1 head2 tail)
  apply(clarsimp, auto)
  (* p1 and p2 stand for "part1" and "part2" of q divided by the monomial (monom, cnst). *)
  oops

declare poly_add.simps[simp del]

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

declare [[show_types]]
declare [[show_sorts]]


end