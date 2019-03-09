open Buffer;;
open Printf;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let n = int_of_string (input_line ic);;

(* -1 if a is small 0 if not comp and 1 if b is small*)
let cmp = Hashtbl.create 100;;
let rev_cmp = Hashtbl.create 100;;
let visited = Hashtbl.create 100;;
let rev_visited = Hashtbl.create 100;;
let pos_in_top_sort = Hashtbl.create 100;;
let rev_pos_in_top_sort = Hashtbl.create 100;;
let resh_sum = Hashtbl.create 100;;
let resh_mul = Hashtbl.create 100;;
let resh_impl = Hashtbl.create 100;;
let graph = Hashtbl.create 100;;
let rev_graph = Hashtbl.create 100;;
let top_sort_list = ref [];;
let rev_top_sort_list = ref [];;

let rec update_graph lst vertice = match lst with
| [] -> ()
| head::tail -> if vertice <> (int_of_string head) then 
					begin
						(* fprintf oc "%d -> %d\n" vertice (int_of_string head); *)
						Hashtbl.add graph vertice (int_of_string head);
						Hashtbl.add rev_graph (int_of_string head) vertice; 
					end;
					update_graph tail vertice
;;

(* fprintf oc "%d\n" n;; *)

for i = 1 to n do
	update_graph (Str.split (Str.regexp " ") (input_line ic)) i
done;;

for a = 1 to n do
	for b = 1 to n do
		Hashtbl.add cmp (a, b) 0;
		Hashtbl.add rev_cmp (a, b) 0;
	done
done;;

let rec dfs par v = (
	Hashtbl.replace cmp (v, par) 1;
	Hashtbl.replace cmp (par, v) (-1);

	Hashtbl.replace rev_cmp (par, v) 1;
	Hashtbl.replace rev_cmp (v, par) (-1);
	let lst = Hashtbl.find_all graph v in 
	List.iter (dfs par) lst
);;

for i = 1 to n do
	dfs i i
done;;

let top_sort () = (
	let rec tps_dfs v = (
		Hashtbl.add visited v 1;
		let lst = Hashtbl.find_all graph v in 
		let help_func x = (match (Hashtbl.mem visited x) with
		| false -> tps_dfs x
		| true -> ()
		) in
		List.iter help_func lst;
		top_sort_list := v :: (!top_sort_list);
		(*The bigger the index the SMALLER the number*)
		Hashtbl.add pos_in_top_sort v (List.length (!top_sort_list))
	) in
	for i = 1 to n do
		if not (Hashtbl.mem visited i) then
			tps_dfs i
	done
);;



let rev_top_sort () = (
	let rec rev_tps_dfs v = (
		Hashtbl.add rev_visited v 1;
		let lst = Hashtbl.find_all rev_graph v in 
		let rev_help_func x = (match (Hashtbl.mem rev_visited x) with
		| false -> rev_tps_dfs x
		| true -> ()
		) in
		List.iter rev_help_func lst;
		rev_top_sort_list := v :: (!rev_top_sort_list);
		(*The bigger the index the SMALLER the number*)
		Hashtbl.add rev_pos_in_top_sort v (List.length (!rev_top_sort_list))
	) in
	for i = 1 to n do
		if not (Hashtbl.mem rev_visited i) then
			rev_tps_dfs i
	done
);;

top_sort();;
rev_top_sort();;

let rec check_if_min a lst = match lst with
| [] -> true
| head::tail -> (* fprintf oc "%d comp %d\n" head (Hashtbl.find cmp (a, head)); *) if ((Hashtbl.find cmp (a, head)) = (-1)) then check_if_min a tail else false
;;

let rec rev_check_if_min a lst = match lst with
| [] -> true
| head::tail -> (* fprintf oc "%d comp %d\n" head (Hashtbl.find cmp (a, head)); *) if ((Hashtbl.find rev_cmp (a, head)) = (-1)) then rev_check_if_min a tail else false
;;


(* CHECK + *)
for a = 1 to n do
	for b = 1 to n do
		let lst = ref [] in
		let smallest = ref 0 in
		for c = 1 to n do
			if ((Hashtbl.find cmp (a, c)) = -1) && ((Hashtbl.find cmp (b, c)) = -1) then 
			(
				lst := c :: (!lst);
				(* fprintf oc "%d - %d\n" c (Hashtbl.find pos_in_top_sort (c)); *)
				if ((!smallest) = 0) then
					smallest := c;
				if ((Hashtbl.find pos_in_top_sort (!smallest)) <= (Hashtbl.find pos_in_top_sort (c))) then
					smallest := c;
			)
		done;
		if ((!smallest) = 0) then (
			fprintf oc "Операция '+' не определена: %d+%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		(* fprintf oc "Операция '+' не: %d+%d=%d\n" a b (!smallest); *)
		if (check_if_min (!smallest) (!lst)) = false then (
			fprintf oc "Операция '+' не определена: %d+%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		Hashtbl.add resh_sum (a, b) (!smallest);
		(* exit 0 *)
	done
done;;

(* CHECK multip *)
for a = 1 to n do
	for b = 1 to n do
		let lst = ref [] in
		let smallest = ref 0 in
		for c = 1 to n do
			if ((Hashtbl.find rev_cmp (a, c)) = -1) && ((Hashtbl.find rev_cmp (b, c)) = -1) then 
			(
				lst := c :: (!lst);
				(* fprintf oc "%d - %d\n" c (Hashtbl.find pos_in_top_sort (c)); *)
				if ((!smallest) = 0) then
					smallest := c;
				if ((Hashtbl.find rev_pos_in_top_sort (!smallest)) <= (Hashtbl.find rev_pos_in_top_sort (c))) then
					smallest := c;
			)
		done;
		if ((!smallest) = 0) then (
			fprintf oc "Операция '*' не определена: %d*%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		(* fprintf oc "Операция '+' не: %d+%d=%d\n" a b (!smallest); *)
		if (rev_check_if_min (!smallest) (!lst)) = false then (
			fprintf oc "Операция '*' не определена: %d*%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		Hashtbl.add resh_mul (a, b) (!smallest);
		(* exit 0 *)
	done
done;;

let (#+) a b = Hashtbl.find resh_sum (a, b);;
let (#*) a b = Hashtbl.find resh_mul (a, b);;

(* CHECK a*(b+c) ?= a*b+a*c *)

for a = 1 to n do
	for b = 1 to n do
		for c = 1 to n do
			if (not ((a #* (b #+ c)) = ((a #* b) #+ (a #* c)))) then (
				fprintf oc "Нарушается дистрибутивность: %d*(%d+%d)\n" a b c;
				close_out oc;
				close_in ic;
				exit 0
			)
		done;
	done
done;;

let rec check_if_max a lst = match lst with
| [] -> true
| head::tail -> (* fprintf oc "%d comp %d\n" head (Hashtbl.find cmp (a, head)); *) if ((Hashtbl.find cmp (head, a)) = (-1)) then check_if_max a tail else false
;;

(* CHECK -> *)
for a = 1 to n do
	for b = 1 to n do
		let lst = ref [] in
		let largest = ref 0 in
		for c = 1 to n do
			if ( (Hashtbl.find cmp ((a #* c), b)) = -1 ) then 
			(
				lst := c :: (!lst);
				if ((!largest) = 0) then
					largest := c;
				(* fprintf oc "%d - %d\n" c (Hashtbl.find pos_in_top_sort (c)); *)
				if ((Hashtbl.find pos_in_top_sort (!largest)) >= (Hashtbl.find pos_in_top_sort (c))) then
					largest := c;
			)
		done;
		(* fprintf oc "Операция '+' не: %d+%d=%d\n" a b (!smallest); *)
		if ((!largest) = 0) then (
			fprintf oc "Операция '->' не определена: %d->%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		if (check_if_max (!largest) (!lst)) = false then (
			fprintf oc "Операция '->' не определена: %d->%d\n" a b;
			close_out oc;
			close_in ic;
			exit 0
		);
		Hashtbl.add resh_impl (a, b) (!largest);
		(* exit 0 *)
	done
done;;


let (#->) a b = Hashtbl.find resh_impl (a, b);;

let zero = ref 0;;
let one = ref 0;;
let zero_bool = ref true;;
let one_bool = ref true;;
(*Get 1 and 0*)
for a = 1 to n do
	zero_bool := true;
	one_bool := true;
	for b = 1 to n do
		if (Hashtbl.find cmp (a, b)) <> (-1) then
			zero_bool := false;
		if (Hashtbl.find cmp (b, a)) <> (-1) then
			one_bool := false;
	done;
	if (!zero_bool) then
		zero := a;
	if (!one_bool) then
		one := a;
done;;

(*Check bool-Algebra*)
for a = 1 to n do
	if ((a #+ (a #-> (!zero))) <> (!one)) then (
		fprintf oc "Не булева алгебра: %d+~%d\n" a a;
		close_out oc;
		close_in ic;
		exit 0
	)
done;;	

fprintf oc "Булева алгебра\n";;

close_out oc;;
close_in ic;;
