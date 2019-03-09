open Tree
open Buffer
open Printf
(* let overalAlpha = ref (Var("a"));;
let overalAssumpList = ref [];;(*give the variables*)

let putAlpha a = (overalAlpha := a);;
let putAssumpList a = (overalAssumpList := a);;
 *)

let get_ax2 exprA exprB exprC = Binop(Impl, Binop(Impl, exprA, exprB), Binop(Impl, Binop(Impl, exprA, Binop(Impl, exprB, exprC)), Binop(Impl, exprA, exprC)))

(* let assumption_hash_table = Hashtbl.create 1 
let right_tree_list_map = Hashtbl.create 1
let tree_ind_map = Hashtbl.create 1
let index_table = Hashtbl.create 1
let j = ref 0
let k = ref 0 *)

class deducer alpha assumptList dataList ic oc = 

	object(self)

	val part1 = (Binop(Impl, alpha, Binop(Impl, alpha, alpha)))
	val part2 = (get_ax2 alpha (Binop(Impl, alpha, alpha)) alpha)
	val part3 = (Binop(Impl, Binop(Impl, alpha, Binop(Impl, Binop(Impl, alpha, alpha), alpha)), Binop(Impl, alpha, alpha)))
	val part4 = (Binop(Impl, alpha, Binop(Impl, Binop(Impl, alpha, alpha), alpha)))
	val part5 = (Binop(Impl, alpha, alpha))
	val assumption_hash_table = (Hashtbl.create 1 )
	val right_tree_list_map = (Hashtbl.create 1)
	val tree_ind_map = (Hashtbl.create 1)
	val index_table = (Hashtbl.create 1)
	val j = ref 0
	val k = ref 0

	method get_tree expr = match expr with
	| "" -> raise End_of_file
	| _ -> (expr >> Lexing.from_string >> Parser.main Lexer.main)
	
	method get_norm_string_of_tree tt = 
	  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Negg -> "#" in
	  let buf = create 1000 in
	  let rec chk t = match t with
	    | Var v -> add_string buf v
	    | Neg t -> add_string buf "(!"; chk t; add_char buf ')'
	    | Binop (op,l,r) -> add_char buf '('; chk l; bprintf buf "%s" (s_op op); chk r; add_char buf ')'
	  in chk tt; 
	  contents buf
	
	method add_to_hshtb_assump lst id = match lst with
	| [] -> ()
	| head::tail -> Hashtbl.add assumption_hash_table (self#get_tree head) id;self#add_to_hshtb_assump tail (id + 1)

	method add_assumptions () = self#add_to_hshtb_assump assumptList 1

	(* ;;FIXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxxx *)

	method is_assumption expr = match (Hashtbl.mem assumption_hash_table expr) with
	| false -> false
	| _ -> true
	
	method get_1 (a, b) = a

	method get_2 (a, b) = b

	method check_if_modus_ponens expr = Hashtbl.mem right_tree_list_map expr

	method get_modus_ponens_numbs expr = 
		let lst = Hashtbl.find_all right_tree_list_map expr in
			let rec get_num_from_list cur = match cur with
			| [] -> (0, 0)
			| head::tail -> if Hashtbl.mem tree_ind_map (self#get_1 head) then (self#get_2 head, Hashtbl.find tree_ind_map (self#get_1 head)) else get_num_from_list tail
			in
				get_num_from_list lst
	
	method is_modus_ponens expr = match (self#check_if_modus_ponens expr) with
	| true -> (match (self#get_modus_ponens_numbs expr) with
				| (0, 0) -> false
				| (a, b) -> k := a;j := b; true)
	| _ -> false
	
	method get_first_param x = match x with
		| Binop(c, a, b) -> a
		| _ -> Var("NOTHING")

	method get_second_param x = match x with
		| Binop(c, a, b) -> b
		| _ -> Var("NOTHING")

	method get_upd_map my_expr cur_id = Hashtbl.add right_tree_list_map (self#get_second_param my_expr) ((self#get_first_param my_expr), cur_id)

	method get_axiom expr = match expr with
	| Binop(Impl, exprA1, Binop(Impl, exprB1, exprA2)) when exprA2 = exprA1 -> 1
	| Binop(Impl, Binop(Impl, exprA1, exprB1), Binop(Impl, Binop(Impl, exprA2, Binop(Impl, exprB2, exprC1)), Binop(Impl, exprA3, exprC2))) when exprA1 = exprA2 && exprA2 = exprA3 && exprB1 = exprB2 && exprC1 = exprC2 -> 2
	| Binop(Impl, exprA1, Binop(Impl, exprB1, Binop(Conj, exprA2, exprB2))) when exprA1 = exprA2 && exprB1 = exprB2 -> 3
	| Binop(Impl, Binop(Conj, exprA1, exprB1), exprA2) when exprA1 = exprA2 -> 4
	| Binop(Impl, Binop(Conj, exprA1, exprB1), exprB2) when exprB1 = exprB2 -> 5
	| Binop(Impl, exprA1, Binop(Disj, exprA2, exprB1)) when exprA1 = exprA2 -> 6
	| Binop(Impl, exprB1, Binop(Disj, exprA1, exprB2)) when exprB1 = exprB2 -> 7
	| Binop(Impl, Binop(Impl, exprA1, exprC1), Binop(Impl, Binop(Impl, exprB1, exprC2), Binop(Impl, Binop(Disj, exprA2, exprB2), exprC3))) when exprA1 = exprA2 && exprB1 = exprB2 && exprC1 = exprC2 && exprC2 = exprC3 -> 8
	| Binop(Impl, Binop(Impl, exprA1, exprB1), Binop(Impl, Binop(Impl, exprA2, Neg(exprB2)), Neg(exprA3))) when exprA1 = exprA2 && exprA2 = exprA3 && exprB1 = exprB2 -> 9
	| Binop(Impl, Neg(Neg(exprA1)), exprA2) when exprA1 = exprA2 -> 10
	| _ -> 0
	
	method is_axiom expr = 
	let a = self#get_axiom expr in
		match a with
		| 0 -> false
		| _ -> true

	method print_prove_alpha () = 
		fprintf oc "%s\n" (self#get_norm_string_of_tree part1);
		fprintf oc "%s\n" (self#get_norm_string_of_tree part2);
		fprintf oc "%s\n" (self#get_norm_string_of_tree part3);
		fprintf oc "%s\n" (self#get_norm_string_of_tree part4);
		fprintf oc "%s\n" (self#get_norm_string_of_tree part5)

	method start () = 
		try
			(* j := 0;
			k := 0;
			Hashtbl.clear assumption_hash_table;
			Hashtbl.clear right_tree_list_map;
			Hashtbl.clear tree_ind_map;
			Hashtbl.clear index_table; *)
			self#add_assumptions ();
			let rec solve cur_id =
				(* print_endline "CCCCCCC"; *)
				(* print_endline (string_of_int (List.length (dataList))); *)
				let my_expr = self#get_tree (List.nth dataList (cur_id - 1)) in
						(* print_endline ((self#get_norm_string_of_tree my_expr)^"CCCCCCCCCCC"); *)
						if (self#is_axiom my_expr || self#is_assumption my_expr) then
						(
							fprintf oc "%s\n%s\n%s\n" (self#get_norm_string_of_tree my_expr) (self#get_norm_string_of_tree (Binop(Impl, my_expr, Binop(Impl, alpha, my_expr)))) (self#get_norm_string_of_tree (Binop(Impl, alpha, my_expr)));
						)	
						else 
						(
							if (my_expr = alpha) then
								(self#print_prove_alpha ();)
							else
							(
								let nothing = self#is_modus_ponens my_expr in
									let dj = Hashtbl.find index_table (!j) in
										let p1 = get_ax2 alpha dj my_expr in
											let p2 = Binop(Impl, Binop(Impl, alpha, Binop(Impl, dj, my_expr)), Binop(Impl, alpha, my_expr)) in
												let p3 = Binop(Impl, alpha, my_expr) in
												 	fprintf oc "%s\n" (self#get_norm_string_of_tree p1);
													fprintf oc "%s\n" (self#get_norm_string_of_tree p2);
													fprintf oc "%s\n" (self#get_norm_string_of_tree p3);
							)
						);
						self#get_upd_map my_expr cur_id;
			       		Hashtbl.add tree_ind_map my_expr cur_id;
			       		Hashtbl.add index_table cur_id my_expr;
			    	solve (cur_id + 1);
			    in solve 1
		with Failure "nth" -> ()
	end;;