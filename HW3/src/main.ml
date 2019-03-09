open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

let the_part_to_be_proven = ref (Var("a"));;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let get_tree expr = match expr with
	| "" -> raise End_of_file
	| _ -> (expr >> Lexing.from_string >> Parser.main Lexer.main)
;;

let get_norm_string_of_tree tt = 
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Negg -> "#" in
  let buf = create 1000 in
  let rec chk t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; chk t; add_char buf ')'
    | Binop (op,l,r) -> add_char buf '('; chk l; bprintf buf "%s" (s_op op); chk r; add_char buf ')'
  in chk tt; 
  contents buf
;;

let read_file filename =
	let lines = ref [] in
	let chan = open_in filename in
	try
		while true do
	    	let l = input_line chan in
	      	lines := (get_tree l) :: !lines
    	done;
    	!lines
  	with End_of_file ->
   	close_in chan;
   	List.rev !lines
;;

let lemmas = Hashtbl.create 15;;

let get_name a b oper = match oper with
        | Conj -> "conj_" ^ string_of_bool a ^ string_of_bool b
        | Disj -> "disj_" ^ string_of_bool a ^ string_of_bool b
        | Impl -> "impl_" ^ string_of_bool a ^ string_of_bool b
        | Negg -> "not_" ^ string_of_bool a
;;

let add_helper val1 val2 oper = (read_file ("proofs/" ^ (get_name val1 val2 oper) ^ ".txt"));;

let just_add l oper = Hashtbl.add lemmas (Hashtbl.find l 0, Hashtbl.find l 1, oper) (add_helper (Hashtbl.find l 0) (Hashtbl.find l 1) oper);;

let add_lemmas lemmas = 
	let helping = Hashtbl.create 5 in
	let rec add_lemms id = match id with
		| 2 -> just_add helping Impl;just_add helping Conj;just_add helping Disj
		| _ -> Hashtbl.replace helping (id) false; add_lemms (id + 1); Hashtbl.replace helping (id) true; add_lemms (id + 1)
	in
	add_lemms 0;
	Hashtbl.add lemmas (false, false, Negg) (add_helper false false Negg);
	Hashtbl.add lemmas (true, false, Negg) (add_helper true false Negg)
;;

add_lemmas lemmas;;


let read_string () =
	 Str.global_replace (Str.regexp "[ \n\r\x0c\t]+") "" (ic >> input_line)
;;

let pred = read_string();;

let pred2 = Str.global_replace (Str.regexp "=") "-" pred;;

let get_pred pred = match (String.get pred 0) with
| '|' -> let lst = (Str.split (Str.regexp "|=") pred) in the_part_to_be_proven := get_tree (List.nth lst 0); ""
| _ -> let lst = (Str.split (Str.regexp "|=") pred) in the_part_to_be_proven := get_tree (List.nth lst 1); List.nth lst 0;;
;;


let split_by_comma = Str.split (Str.regexp ",");;

let rec get_tree_list lst = match lst with
| [] -> []
| head::tail -> (get_tree head)::(get_tree_list tail)
;;

let hypothesis = get_tree_list (split_by_comma (get_pred pred));;

let sz_of_hypothesis = List.length hypothesis;;

let rec deduction assumption expr = match assumption with
| [] -> expr
| head::tail -> head-->(deduction tail expr)
;;

let get_var_list expr = 
	let mp = (Hashtbl.create 5 : (string, int) Hashtbl.t) in
	let lst = ref [] in 
	let rec get_vars = function
		| Neg(a) -> get_vars a
		| Binop(_, a, b) -> get_vars a; get_vars b
		| Var(a) -> if not (Hashtbl.mem mp a) then begin Hashtbl.add mp a 1; lst := !lst @ [a]; end
	in
	get_vars expr;
	!lst
;;


let expr = deduction hypothesis !the_part_to_be_proven;;
let args_list = get_var_list expr;;

let rec replace_in_lemma a b expr = match expr with
	| Var "A" -> a
	| Var "B" -> b
	| Neg v -> Neg((replace_in_lemma a b v))
	| Binop(op, p1, p2) -> Binop(op, (replace_in_lemma a b p1), (replace_in_lemma a b p2))
;;

let get_lemma typ a b = (*typ is a tuple of (bool, bool, Operation) *)
	List.map (replace_in_lemma a b) (Hashtbl.find lemmas typ)
;;

let get_1 (a, b) = a;;
let get_2 (a, b) = b;;

let apply_oper a b oper = match oper with
	| Conj -> a && b
	| Disj -> a || b
	| Impl -> not (a && (not b))
	| Negg -> not a
;;



let rec print_list lst = match lst with
| [] -> ()
| head::[] -> print_endline head
| head::tail -> print_string (head^"\n"); print_list tail
;;

let rec print_tree_list lst = match lst with
| [] -> ()
| head::[] -> fprintf oc "%s\n" (get_norm_string_of_tree head)
| head::tail -> fprintf oc "%s\n" (get_norm_string_of_tree head); print_tree_list tail
;;

let arg_sz = (List.length args_list);;
let get_val a = match a with
	| true -> "И"
	| _ -> "Л"
;;
let var_value = (Hashtbl.create 5 : (string, bool) Hashtbl.t);;
let my_merge a b = ((get_1 b),(get_2 a)@(get_2 b));;
let rec print_wrong lst = match lst with
	| head::[] -> head ^ "=" ^ (get_val (Hashtbl.find var_value head))
	| head::tail -> head ^ "=" ^ (get_val (Hashtbl.find var_value head)) ^ ", " ^ (print_wrong tail)
;;
let rec prove expr = match expr with
	| Var a -> 	(
					let rs = (Hashtbl.find var_value a) in
						match rs with
						| false -> (* print_tree_list [(Neg(Var a))];print_endline ""; *)(rs, [(Neg(Var a))])
						| true -> (* print_tree_list [(Var a)];print_endline ""; *)(rs, [(Var a)])
				)
	| Neg a -> 	(
					let res = prove a in
					(* print_tree_list (get_lemma ((get_1 res), false, Negg) a (Var("nothing")));print_endline ""; *)
					((not (get_1 res)), 
						(get_2 res)@(get_lemma ((get_1 res), false, Negg) a (Var("nothing"))))
				)
	| Binop(op, l, r) -> 
				(
					let res1 = prove l in
					let res2 = prove r in
					(* print_tree_list (get_lemma ((get_1 res1), (get_1 res2), op) l r);print_endline "";  *)
					(apply_oper (get_1 res1) (get_1 res2) op, 
						(get_2 res1)@(get_2 res2)@(get_lemma ((get_1 res1), (get_1 res2), op) l r))
				)
;;

(*DEDUCTION PART HW2 START*)
let get_ax2 exprA exprB exprC = Binop(Impl, Binop(Impl, exprA, exprB), Binop(Impl, Binop(Impl, exprA, Binop(Impl, exprB, exprC)), Binop(Impl, exprA, exprC)));;

let alpha = ref (Var("A"));;
let part1 = ref (Binop(Impl, (!alpha), Binop(Impl, (!alpha), (!alpha))));;
let part2 = ref (get_ax2 (!alpha) (Binop(Impl, (!alpha), (!alpha))) (!alpha));;
let part3 = ref (Binop(Impl, Binop(Impl, (!alpha), Binop(Impl, Binop(Impl, (!alpha), (!alpha)), (!alpha))), Binop(Impl, (!alpha), (!alpha))));;
let part4 = ref (Binop(Impl, (!alpha), Binop(Impl, Binop(Impl, (!alpha), (!alpha)), (!alpha))));;
let part5 = ref (Binop(Impl, (!alpha), (!alpha)));;
let assumption_hash_table = (Hashtbl.create 1 );;
let right_tree_list_map = (Hashtbl.create 1);;
let tree_ind_map = (Hashtbl.create 1);;
let index_table = (Hashtbl.create 1);;
let j = ref 0;;
let k = ref 0;;
let result = ref [];;

let get_tree expr = match expr with
| "" -> raise End_of_file
| _ -> (expr >> Lexing.from_string >> Parser.main Lexer.main)
;;
let get_norm_string_of_tree tt = 
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Negg -> "#" in
  let buf = create 1000 in
  let rec chk t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; chk t; add_char buf ')'
    | Binop (op,l,r) -> add_char buf '('; chk l; bprintf buf "%s" (s_op op); chk r; add_char buf ')'
  in chk tt; 
  contents buf
;;
let rec add_to_hshtb_assump lst id = match lst with
| [] -> ()
| head::tail -> Hashtbl.add assumption_hash_table head id;add_to_hshtb_assump tail (id + 1)
;;
let add_assumptions assumptList = add_to_hshtb_assump assumptList 1;;

let is_assumption expr = match (Hashtbl.mem assumption_hash_table expr) with
| false -> false
| _ -> true
;;
let check_if_modus_ponens expr = Hashtbl.mem right_tree_list_map expr;;

let get_modus_ponens_numbs expr = 
	let lst = Hashtbl.find_all right_tree_list_map expr in
		let rec get_num_from_list cur = match cur with
		| [] -> (0, 0)
		| head::tail -> if Hashtbl.mem tree_ind_map (get_1 head) then (get_2 head, Hashtbl.find tree_ind_map (get_1 head)) else get_num_from_list tail
		in
			get_num_from_list lst
;;
let is_modus_ponens expr = match (check_if_modus_ponens expr) with
| true -> (match (get_modus_ponens_numbs expr) with
			| (0, 0) -> false
			| (a, b) -> k := a;j := b; true)
| _ -> false
;;
let get_first_param x = match x with
	| Binop(c, a, b) -> a
	| _ -> Var("NOTHING")
;;
let get_second_param x = match x with
	| Binop(c, a, b) -> b
	| _ -> Var("NOTHING")
;;
let get_upd_map my_expr cur_id = Hashtbl.add right_tree_list_map (get_second_param my_expr) ((get_first_param my_expr), cur_id);;

let get_axiom expr = match expr with
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
;;


let is_axiom expr = 
let a = get_axiom expr in
	match a with
	| 0 -> false
	| _ -> true
;;
let print_prove_alpha () = 
	result := (!result)@[(!part1); (!part2); (!part3); (!part4); (!part5)]
	(* fprintf oc "%s\n" (get_norm_string_of_tree (!part2));
	fprintf oc "%s\n" (get_norm_string_of_tree (!part3));
	fprintf oc "%s\n" (get_norm_string_of_tree (!part4));
	fprintf oc "%s\n" (get_norm_string_of_tree (!part5)) *)
;;
let deduce assumptList nAlpha dataList = 
	try
		j := 0;
		k := 0;
		Hashtbl.clear assumption_hash_table;
		Hashtbl.clear right_tree_list_map;
		Hashtbl.clear tree_ind_map;
		Hashtbl.clear index_table;
		add_assumptions assumptList;
		alpha := nAlpha;
		part1 := (Binop(Impl, (!alpha), Binop(Impl, (!alpha), (!alpha))));
		part2 := (get_ax2 (!alpha) (Binop(Impl, (!alpha), (!alpha))) (!alpha));
		part3 := (Binop(Impl, Binop(Impl, (!alpha), Binop(Impl, Binop(Impl, (!alpha), (!alpha)), (!alpha))), Binop(Impl, (!alpha), (!alpha))));
		part4 := (Binop(Impl, (!alpha), Binop(Impl, Binop(Impl, (!alpha), (!alpha)), (!alpha))));
		part5 := (Binop(Impl, (!alpha), (!alpha)));
		result := [];
		(* print_endline "the assump list"; *)
		(* print_tree_list assumptList; *)
		let rec solve cur_id =
			(* print_endline "CCCCCCC"; *)
			(* print_endline (string_of_int (List.length (dataList))); *)
			let my_expr = (List.nth dataList (cur_id - 1)) in
					(* print_endline ((get_norm_string_of_tree my_expr)^" The curret shit"); *)
					if (is_axiom my_expr || is_assumption my_expr) then
					(
						let just1 = (Binop(Impl, my_expr, Binop(Impl, (!alpha), my_expr))) in
						let just2 = (Binop(Impl, (!alpha), my_expr)) in
						result := (!result)@[my_expr; just1; just2]
						(* fprintf oc "%s\n%s\n%s\n" (get_norm_string_of_tree my_expr) (get_norm_string_of_tree (Binop(Impl, my_expr, Binop(Impl, (!alpha), my_expr)))) (get_norm_string_of_tree (Binop(Impl, (!alpha), my_expr))); *)
					)	
					else 
					(
						if (my_expr = (!alpha)) then
							(print_prove_alpha ();)
						else
						(
							let nothing = is_modus_ponens my_expr in
								let dj = Hashtbl.find index_table (!j) in
									let p1 = get_ax2 (!alpha) dj my_expr in
										let p2 = Binop(Impl, Binop(Impl, (!alpha), Binop(Impl, dj, my_expr)), Binop(Impl, (!alpha), my_expr)) in
											let p3 = Binop(Impl, (!alpha), my_expr) in
											 	(* fprintf oc "%s\n" (get_norm_string_of_tree p1);
												fprintf oc "%s\n" (get_norm_string_of_tree p2);
												fprintf oc "%s\n" (get_norm_string_of_tree p3); *)
												result := (!result)@[p1; p2; p3]
						)
					);
					get_upd_map my_expr cur_id;
		       		Hashtbl.add tree_ind_map my_expr cur_id;
		       		Hashtbl.add index_table cur_id my_expr;
		    	solve (cur_id + 1);
		    in solve 1
	with Failure "nth" -> (!result)
;;
(*DEDUCTION PART HW2 END*)

let contrapos = (read_file "proofs/_contraposition.txt");;

let remove_alpha alpha expr = (

	(*Do contraposition (alpha, alpha|!alpha)*)
	let contapos1 = List.map (replace_in_lemma (alpha) (Binop(Disj, alpha, Neg(alpha)))) contrapos in
	(*Do contraposition (!alpha, alpha|!alpha)*)
	let contapos2 = List.map (replace_in_lemma (Neg(alpha)) (Binop(Disj, alpha, Neg(alpha)))) contrapos in
	(*!alpha->expr alpha->expr get expr*)
	let removed = List.map (replace_in_lemma alpha expr) (read_file "proofs/_excluded.txt") in
		contapos1@contapos2@removed
)
;;

let prove_by_masks expr =
	let rec make_mask id var_list = 
	(
		if id = arg_sz then
				(
					(* print_endline "CCCCCCC";
					print_tree_list var_list;print_endline "\n\n";
 *)					let res = prove expr in 
					match (get_1 res) with
						| false -> fprintf oc "Высказывание ложно при %s\n" (print_wrong args_list); (false, [])
						| _ -> res
				)    
		else 	(
					Hashtbl.replace var_value (List.nth args_list id) true;
					let vr1 = Var((List.nth args_list id)) in
					let res1 = make_mask (id + 1) (var_list@[vr1]) in
					match (get_1 res1) with
					| false -> (false, [])
					| true -> 	(
									Hashtbl.replace var_value (List.nth args_list id) false; 
									let vr2 = Neg(Var((List.nth args_list id))) in
									let res2 = (make_mask (id + 1) (var_list@[vr2])) in
									match (get_1 res2) with
									| false -> (false, [])
									| true ->   let dp1 = deduce var_list vr1 (get_2 res1) in 
												let dp2 = deduce var_list vr2 (get_2 res2) in
													(true, dp1@dp2@(remove_alpha vr1 expr))
													(* return a@b@(exclude curVar a b) stopped in here
													my_merge res1 res2 *)
									
								)
				)
	)
	in
	make_mask 0
;;

(* print_endline (get_norm_string_of_tree expr);; *)
let proof = (prove_by_masks expr []);;
let overal_proof = (get_2 proof);;
let cont = (get_1 proof);;
let rec print_with_impl lst = match lst with
| [] -> ()
(* | head::[] -> fprintf oc "%s" (get_norm_string_of_tree head); *)
| head::tail -> fprintf oc "%s->" (get_norm_string_of_tree head);print_with_impl tail
;;
let rec antideduce hypo expr = match hypo with
| [] -> ()
| head::tail -> fprintf oc "%s\n" (get_norm_string_of_tree head); print_with_impl tail;fprintf oc "%s\n" (get_norm_string_of_tree expr); antideduce tail expr
;;
if cont then begin
	fprintf oc "%s\n" pred2;
	print_tree_list overal_proof;
	antideduce hypothesis (!the_part_to_be_proven);
end;;

close_out oc;;
close_in ic;;
