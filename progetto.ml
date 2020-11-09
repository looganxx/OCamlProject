type ide = string;;
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | MyDict of (ide * exp) list | Select of exp * ide | Insert of exp * (ide * exp) |
	Remove of exp * ide | Clear of exp | ApplyOver of exp * exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | String of string | Unbound | MyDictVal of (ide * evT) list | FunVal of evFun | RecFunVal of ide * evFun
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x)
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*Funzione che restituisce il valore dell'ide se presente nel dizionario (funzione utilizzata nella Select)*)
let rec check (l : (ide * evT) list) (i : ide) : evT = match l with
	[]-> Unbound
	| (i1, e)::xs -> if i1 = i then e else check xs i;;

(*Funzione che dato un ide lo rimuove dal dizionario con anche il suo corrispettivo valore (utilizzata nella Remove)*)
let rec rem (l : (ide * evT) list) (i : ide) : (ide * evT) list = match l with
	[]-> []
	| (i1, e)::xs -> if i = i1 then xs else (i1, e)::rem xs i;;

(*Funzione che restituisce true se l'ide appartiene al dizionario, restituisce false se non appartiene.
	Viene utilizzata nella Insert per vedere se l'ide che si vuole inserire appartiene già al dizionario.*)
let rec member (l : (ide * evT) list) (i : ide) : bool = match l with
	[]-> false
	| (i1, e)::xs -> if i=i1 then true else member xs i;;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) ->
		let g = (eval a r) in
			if (typecheck "bool" g)
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	MyDict(l) -> MyDictVal(evallist l r) |  (*Dichiarazione di un dizionario*)
	Select(e1, i) -> (match (eval e1 r) with (*Selezione di un ide*)
		MyDictVal(l) -> (check l i) |
		_->failwith("type error")) |
	Insert(e1, (i , e2)) -> (match (eval e1 r) with (*Inserimento di un dato nel dizionario*)
		MyDictVal(l) -> let v = (eval e2 r) in
										let b = (member l i) in
										if b = false then MyDictVal((i,v)::l)
																else failwith("ide just present") |
		_->failwith("type error")) |
	Remove(e1, i) -> (match (eval e1 r) with (*Rimozione di un dato nel dizionario*)
		MyDictVal(l) -> MyDictVal(rem l i) |
		_-> failwith("type error")) |
	Clear(e1) -> (match (eval e1 r) with  (*Cancellazione del dizionario*)
 		MyDictVal(l) -> MyDictVal([]) |
		_ -> failwith("type error")) |
	ApplyOver(e1, e2) -> (match (eval e2 r) with (*Applicazione di una funzione sugli elementi del dizionario*)
		MyDictVal(l) -> MyDictVal(apply e1 l r) |
		_ -> failwith("type error")) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) ->
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) ->
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) ->
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
  Letrec(f, funDef, letBody) ->
  		(match funDef with
      		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                   			                eval letBody r1 |
      		_ -> failwith("non functional def"))
	(*funzione per valutare una lista utilizzata nella dichiarazione del dizionario (MyDict)*)
	and evallist (l : (ide * exp) list) (r : evT env) : (ide * evT) list = match l with
		[] -> []
		| (i, e)::xs -> let v = (eval e r) in (i,v) :: (evallist xs r)
	(*funzione che applica la funzione passata nell'ApplyOver al dizionario*)
	and apply (f : exp) (l : (ide * evT) list) (r: evT env) : (ide * evT) list = match l with
		[] -> []
		| (i , v)::xs ->  (match (eval f r) with
													FunVal(arg, body, decEnv) -> (i, eval body (bind decEnv arg v))::apply f xs r
													| _-> failwith("type error"));;

(* =============================  TESTS  =================*)

(*creo un ambiente*)
let env0 = emptyenv Unbound;;

(*creo un nuovo dizionario*)
let e = MyDict([ "nome", Estring "Giuseppe"; "eta", Eint 20]);;

(*uso la Select facendomi restituisce il valore di età e il nome*)
let e1 = Select(e, "eta");;
let e12 = Select(e, "nome");;

(*uso la Insert per inserire la matricola,
nel secondo caso ci sarà un errore poichè non accetto l'inserimento dello stesso dato*)
let e2 = Insert(e , ("matricola", Eint 1234));;
let e3 = Insert(e2 , ("matricola", Eint 1111));;

(*Rimuovo il dato nome*)
let e4 = Remove(e2 , "nome");;

(*creo la funzione e la uso nell'ApplyOver*)
let f = Fun("n",Sum(Den "n", Eint 1));;
let e5 = ApplyOver(f , e4);;

(*uso l'ApplyOver in un dizionario con anche una stringa per far vedere che
se è presente un tipo diverso da quello sul quale la funzione agisce,
la funzione non viene applicata e viene restituito un type error*)
let e52 = ApplyOver(f , e2);;

(*cancello l'intero dizionario*)
let e6 = Clear(e5);;

eval e env0;;

eval e1 env0;;

eval e12 env0;;

eval e2 env0;;

eval e3 env0;;

eval e4 env0;;

eval e5 env0;;

eval e52 env0;;

eval e6 env0;;
