open Buffer;;

let (>>) x f = f x;;

type op = Conj | Disj | Impl | Negg;;

type tree = 
	| Binop of op * tree * tree
        | Neg of tree
        | Var of string
;;

let (-->) a b = Binop(Impl, a, b);;

(* type annotation = ModusPonens of int * int
	| Axiom of int
	| Assumption of int
	| UnProven
;; *)