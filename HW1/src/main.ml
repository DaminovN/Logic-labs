open Tree;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->";;

let string_of_tree tree = 

  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
    | Binop (op,l,r) -> bprintf buf "(%s," (s_op op); s_t l; add_char buf ','; s_t r; add_char buf ')'
  in s_t tree; 
  contents buf;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let get_tree expr = match expr with
	| "" -> raise End_of_file
	| _ -> (expr >> Lexing.from_string >> Parser.main Lexer.main)
;;


let get_norm_string_of_tree tree = 
  let buf = create 1000 in
  let rec chk t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; chk t; add_char buf ')'
    | Binop (op,l,r) -> add_char buf '('; chk l; bprintf buf "%s" (s_op op); chk r; add_char buf ')'
  in chk tree; 
  contents buf
;;

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


let is_axiom expr id = 
	let a = get_axiom expr in
		match a with
		| 0 -> false
		| _ -> fprintf oc "(%d) %s (Сх. акс. %d)\n" id (get_norm_string_of_tree expr) a; true
;;


let read_string () =
	 Str.global_replace (Str.regexp "[ \n\r\x0c\t]+") "" (ic >> input_line)
;;

let pred = read_string();;


let get_pred pred = match (String.get pred 0) with
| '|' -> ""
| _ -> List.nth (Str.split (Str.regexp "|-") pred) 0;;
;;

let expr = get_pred pred;;		



let split_by_comma = Str.split (Str.regexp ",");;

let rec print_list lst = match lst with
| [] -> ()
| head::[] -> print_endline head
| head::tail -> print_string (head^" "); print_list tail
;;


let get_1 (a, b) = a;;
let get_2 (a, b) = b;;

let rec print_right_map_list lst = match lst with
| [] -> print_endline ""
| head::[] -> print_string ((string_of_tree (get_1 head))^" \n")
| head::tail -> print_string ((string_of_tree (get_1 head))^" "); print_right_map_list tail
;;

let rec convert_stringlist_to_treelist lst = match lst with
| [] -> []
| head::tail -> (get_tree head)::(convert_stringlist_to_treelist tail)
;;

let assumption_hash_table = Hashtbl.create 1;;
Hashtbl.clear assumption_hash_table;;

let right_tree_list_map = Hashtbl.create 1;;
Hashtbl.clear right_tree_list_map;;

let tree_ind_map = Hashtbl.create 1;;
Hashtbl.clear tree_ind_map;;


let rec add_to_hshtb_assump lst id = match lst with
| [] -> ()
| head::tail -> Hashtbl.add assumption_hash_table (get_tree head) id;add_to_hshtb_assump tail (id + 1)
;;

let add_assumptions () = add_to_hshtb_assump (split_by_comma expr) 1;;
add_assumptions ();;

let is_assumption expr id = match (Hashtbl.mem assumption_hash_table expr) with
| false -> false
| _ -> fprintf oc "(%d) %s (Предп. %d)\n" id (get_norm_string_of_tree expr) (Hashtbl.find assumption_hash_table expr); true
;;


let rec add_to_list expr lst = match lst with
| [] -> expr::[]
| head::tail -> head::(add_to_list expr tail)
;;


module TreeMap = Map.Make(struct type t = tree let compare = compare end);;


let check_if_modus_ponens expr = Hashtbl.mem right_tree_list_map expr;;

let modus_ponens_num = -1;;


let get_modus_ponens_numbs expr = 
	let lst = Hashtbl.find_all right_tree_list_map expr in
		let rec get_num_from_list cur = match cur with
		| [] -> (0, 0)
		| head::tail -> if Hashtbl.mem tree_ind_map (get_1 head) then (get_2 head, Hashtbl.find tree_ind_map (get_1 head)) else get_num_from_list tail
		in
			get_num_from_list lst
;;

let is_modus_ponens expr id = match (check_if_modus_ponens expr) with
| true -> (match (get_modus_ponens_numbs expr) with
			| (0, 0) -> false
			| (a, b) -> fprintf oc "(%d) %s (M.P. %d, %d)\n" id (get_norm_string_of_tree expr) a b; true)
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

let cur_id = ref 0;;

let get_upd_map my_expr cur_id = Hashtbl.add right_tree_list_map (get_second_param my_expr) ((get_first_param my_expr), cur_id)
;;

(* let test_var = Binop(Impl, (Var("B")), Binop(Conj, (Var("A")), (Var("B"))));;

print_endline (string_of_tree test_var);; *)

try
	let rec solve cur_id =
		let my_expr = get_tree (read_string ()) in
			if (not (is_axiom my_expr cur_id) && not (is_assumption my_expr cur_id) && not (is_modus_ponens my_expr cur_id)) then
	            fprintf oc "(%d) %s (Не доказано)\n" cur_id (get_norm_string_of_tree my_expr);
	        get_upd_map my_expr cur_id;
	        Hashtbl.add tree_ind_map my_expr cur_id;
	    	solve (cur_id + 1);
	    in solve 1
with End_of_file -> ()
;;

close_out oc;;
close_in ic;;
