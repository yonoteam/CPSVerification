theory ExploringKADs
  imports 
Main
"HOL.Transcendental"
"../afp-2017-10-18/thys/Algebraic_VCs/AVC_KAD/VC_KAD"

begin

(* Getting to know a constant. *)
term "Id"
thm Id_def

(* Exploring the allowed syntax of real numbers in Isabelle. *)
value "2/(3::real)+1"

(* Learning about the update function. *)
term fun_upd
thm fun_upd_def
term "(\<lambda> s. s ''x'')"
value "((\<lambda> s. if s = ''x'' then (1::nat) else 0) (''x'' := 2)) ''1''"
term "\<lambda>s. 2 \<cdot> s ''x''"
term "''x'' ::= (\<lambda>s. 2 \<cdot> s ''x'')"

(* Trigonometric functions and pi available from HOL.Transcendental. *)
term pi
term "cos (2.3::real)"
term "cos pi"

lemma "cos pi = -1"

(* Exploring the behavior of stores, preds, rels and strings. *)
term "(\<lambda>s::int store. s ''x'' = a \<and> s ''y'' = b)"
value "(\<lambda>s::int store. s ''x'' = a \<and> s ''y'' = b) (\<lambda> x. if x = ''x'' then 1 else 0)"
term "(\<lambda>s. 2 \<cdot> s ''x'')" 

(* Exploring the "continuous" predicate in Isabelle. *)
lemma "continuous (at x within collect real) id"
by (simp add: id_def)

(* I keep forgetting in which direction Rep and Abs go... *)
term Rep_filter
term Abs_filter

(* For some reason the letter "r" is a constant. Investigate later. *)
term "{(x,y,r) | x y z. x = 1}"
term "r"

declare [[show_types]]
declare [[show_sorts]]

term "INF k. principal "
value "{.. (2::nat)}"

end