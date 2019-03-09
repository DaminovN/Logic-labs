open Tree;;
open Buffer;;
open Printf;;
open Deducer;;

let (>>) x f = f x;;

let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Negg -> "#";;

let the_part_to_be_proven = ref "";;

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



let read_string () =
	 Str.global_replace (Str.regexp "[ \n\r\x0c\t]+") "" (ic >> input_line)
;;

let pred = read_string();;


let get_pred pred = match (String.get pred 0) with
| '|' -> ""
| _ -> let lst = (Str.split (Str.regexp "|-") pred) in the_part_to_be_proven := (List.nth lst 1); List.nth lst 0;;
;;

let split_by_comma = Str.split (Str.regexp ",");;

let expr_all = split_by_comma (get_pred pred);;

let sz = List.length expr_all;;

let alpha = get_tree (List.nth expr_all (sz - 1));;

let rec remove_last list = match list with
| head::[] -> fprintf oc "|-(%s)->(%s)\n" (List.nth expr_all (sz - 1)) !the_part_to_be_proven; []
| head::tail -> (match tail with
				| head2::[] -> fprintf oc "%s" head; head::(remove_last tail)
				| _ -> fprintf oc "%s," head; head::(remove_last tail)
				)
| [] -> fprintf oc "VERY BAD\n"; []
;;

let expr = remove_last expr_all;;
let data = ref [];;
try
	let rec solve cur_id =
		let my_expr = (read_string ()) in
			data := (!data)@[my_expr];
	    	solve (cur_id + 1);
	    in solve 1
with End_of_file -> ()
;;

let deduce = new deducer alpha expr (!data) ic oc;;

deduce#start ();;

close_out oc;;
close_in ic;;
