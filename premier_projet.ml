(*à faire :
optimiser l'arbre si op1 (op2, op2) -> LA FLEEEEMMMEUUUUH*)


type exp =
	|Int of int
	|To_int of exp
	|Float of float
	|To_float of exp
	|Add of exp * exp
	|Sub of exp * exp
	|Mul of exp * exp
	|Div of exp * exp
	|Mod of exp * exp
	|Adf of exp * exp
	|Suf of exp * exp
	|Muf of exp * exp;;

type lexeme =
	|Pao
	|Paf
	|Int' of string
	|To_int'
	|Float' of string
	|To_float'
	|Add'
	|Sub'
	|Mul'
	|Div'
	|Mod'
	|Adf'
	|Suf'
	|Muf';;

(*on convertit la chaine de char en liste de char*)
let string_to_list f =
	let rec aux i l =
		if i<0 then l else aux (i-1) (f.[i] :: l)
	in aux (String.length f - 1) [];;

(*on convertit la liste de char en liste de lexemes*)
let rec anal_lex f =
	match f with
	(*si la liste est vide, on a fini la conversion*)
	| [] ->
		[]
	(*si on lit un . à ce niveau, il n'appartient pas à un opérateur, donc il appartient à un nombre*)
	| t1 :: ' ' :: t2 :: f1
		when (t1 = '.') || (t1 <= '9' && t1 >= '0') &&
			 (t2 = '.') || (t2 <= '9' && t2 >= '0') ->
		failwith "l'opérateur vide n'est pas un opérateur. Il doit y avoir un " " au mauvais endroit."
	(*si on est dans ce cas, alors on n'a pas planté, et donc on se fou royalement de l'espace*)
	| ' ' :: f1 -> anal_lex f1
	(*explicite*)
	| '(' :: f1 ->
		Pao :: (anal_lex f1)
	(*explicite*)
	| ')' :: f1 ->
		Paf :: (anal_lex f1)
	(*si "int" alors ce on veut faire une conversion vers un int*)
	(*le cas int(int(exp)) fera planter lors de la phase de compilation.*)
	(*on impose également la syntaxe int(exp) avec la parenthèse juxtaposée.*)
	| 'i' :: 'n' :: 't' :: '(' :: f1 ->
		To_int' :: Pao :: (anal_lex f1)
	(*idem avec float*)
	| 'f' :: 'l' :: 'o' :: 'a' :: 't' :: '(' :: f1 ->
		To_float' :: Paf :: (anal_lex f1)
	(*addition flottante.*)
	(*on la cherche avant de chercher l'addition tout court, car sinon, on trouvera toujours des additions tout court*)
	(*on fait de même pour toutes les autres opérations.*)
	| '+' :: '.' :: f1 ->
		Adf' :: (anal_lex f1)
	| '-' :: '.' :: f1 ->
		Suf' :: (anal_lex f1)
	| '*' :: '.' :: f1 ->
		Muf' :: (anal_lex f1)
	| '+':: f1 ->
		Add' :: (anal_lex f1)
	| '-' :: f1 ->
		Sub' :: (anal_lex f1)
	| '*' :: f1 ->
		Mul' :: (anal_lex f1)
	| '/' :: f1 ->
		Div' :: (anal_lex f1)
	| '%' :: f1 ->
		Mod' :: (anal_lex f1)
	(*si on croise un point à ce stade, il n'appartenait pas à une opération, donc il indique qu'on passe à un float.*)
	(*De même que pour les int plus bas, on ne sait pas quelle taille il fera,*)
	(*donc on commence par chercher sa partie droite à laquelle on rajoute le *)
	(*caractère en cours de lecture                                           *)
	| '.' :: t2 :: f1 when t2 <= '9' && t2 >= '0' -> begin
		(*on regarde le type du nombre obtenu*)
		match anal_lex (t2::f1) with
		(*si c'est un int, on le transforme en float*)
		| Int' str :: q ->
			(Float' ("." ^ str)) :: q
		(*si c'est un float, alors il a déjà une virgule quelque part, et sa conversion en vrai float fera planter.*)
		(*en soi, on pourrait déjà faire planter à ce stade.*)
		| Float' str :: q ->
			(Float' ("." ^ str)) :: q end
	(*de même, on extrait la partie droite à laquelle on rajoute le caractère courant*)
	| t1 :: t2 :: f1
			when t1 <= '9' && t1 >= '0'
			&& ((t2 <= '9' && t2 >= '0') || t2 = '.') -> begin
			match anal_lex (t2::f1) with
			| Int' str :: q ->
				(Int' ((String.make 1 t1) ^ str)) :: q
			| Float' str :: q ->
				(Float' ((String.make 1 t1) ^ str)) :: q end
	(*si le 1er caractère est un chiffre, et qu'on arrive au traitement de ce cas, alors*)
	(*le suivant n'en est pas un, et on sait que le caractère courant est tout à droite *)
	| t1 :: f1 when t1 <= '9' && t1 >= '0' ->
			Int' (String.make 1 t1) :: (anal_lex f1)
	(*de même si c'est un point*)
	| '.' :: f1 ->
			Float' "." :: (anal_lex f1)
	| _	-> failwith "Il y a un caractère indésirable.";;

(*dès qu'on a une pao, on construit l'arbre encapsulé en fouillant dans la*)
(*suite de la liste de lexeme jusqu'à trouver sa paf associée             *)
let rec fermer_par l f1 n =
	match f1 with
	| [] ->
		failwith "Il y a trop de pao"
	| Paf :: f2 when n = 0 ->
		l, f2
	| Pao :: f2 ->
		fermer_par (l@[Pao]) f2 (n+1)
	| Paf :: f2 when n <> 0 ->
		fermer_par (l@[Paf]) f2 (n-1)
	| t :: f2 ->
		fermer_par (l@[t]) f2 n;;

(*on extrait le prochain bloc (donc soit un nombre, soit un arbre (une pao ou un to__))*)
let rec extrait f =
	match f with
	| Int' str :: suite ->
		[Int' str], suite
	| Float' str :: suite ->
		[Float' str], suite
	| Add' :: suite ->
		let a, fin = extrait suite in
		a, fin
	(*ce cas permet de traiter les float négatifs, ma construction extrait toujours*)
	(*les valeurs absolues                                                         *)
	| Sub' :: suite ->
		let a, fin = extrait suite in begin
		match a with
		| [Float' str] -> Sub' :: a, fin
		| Pao :: fin2 -> Sub' :: a, fin
		| [Int' str]   -> Sub' :: a, fin
		| _ -> failwith "Un '-' en début de bloc ne peut qu'être suivit d'un nombre (auquel cas c'est un nombre négatif) ou d'une parenthèse (auquel cas on traite un -(exp))" end
	(*on avait déjà fait planter dans le lexeur si un to__ n'est pas suivit d'une *)
	(*parenthèse, on peut donc ne plus s'en soucier                               *)
	| To_int' :: suite ->
		let a, fin = extrait suite in
		To_int' :: a, fin
	| To_float' :: suite ->
		let a, fin = extrait suite in
		To_float' :: a, fin
	| Pao :: suite ->
		let a, fin = fermer_par [] suite 0 in
		Pao :: (a @ [Paf]), fin
	| _ ->
		failwith "Un bloc commence par un nombre ou une pao";;

let prio op =
	match op with
	| Add' -> 0
	| Sub' -> 0
	| Mul' -> 2
	| Div' -> 2
	| Mod' -> 1
	| Adf' -> 0
	| Suf' -> 0
	| Muf' -> 3;;

(*on extrait le bloc des prochaines opérations prioritaires*)
let rec extrait_prio f p =
	let a, fin = extrait f in
	match fin with
	| op :: suite when prio op > p ->
		let b, fin2 = extrait_prio suite p in
		a @ [op] @ b, fin2
	| _ -> a, fin;;

(*explicite. C'est principalement à cause de ce connard et des autres fonctions       *)
(*qui reçoivent des opérateurs que je dois mettre des ' de partout, c'est trop chiant,*)
(* mais bon, vu que c'est que des lexemes, ça va                                     *)
let apply_op op arg1 arg2 =
	match op with
	| Add' -> Add (arg1, arg2)
	| Sub' -> Sub (arg1, arg2)
	| Mul' -> Mul (arg1, arg2)
	| Div' -> Div (arg1, arg2)
	| Mod' -> Mod (arg1, arg2)
	| Adf' -> Adf (arg1, arg2)
	| Suf' -> Suf (arg1, arg2)
	| Muf' -> Muf (arg1, arg2)
	| _ -> failwith "Erreur d'opérateur";;

(*en vrai cette fonction elle sert à rien, "a, fin = extrait f; gen_arbre a" ça suffit... d'autant qu'on l'appelle que deux fois quoi *)
(*edit : j'ai essayé de m'en passer, et ça marche pas vraiment, parce que la fonction extrait renvoie deux listes, donc en particulier*)
(*si on essaye d'évalier simplement "0" on va avoir une boucle infinie où on appelle extrait sur [Int' "0"] et elle renvoie ça plus []*)
let rec extrait_bloc f =
	match f with
	| Int' str :: suite ->
		Int (int_of_string str), suite
	| Float' str :: suite ->
		Float (Float.of_string str), suite 
	| Add' :: suite ->
		let a, fin = extrait_bloc suite in
		a, fin
	(*avec un - en début de bloc, on vérifie qu'on a bien la syntaxe -(exp) ou -|x|, et on doit utiliser extrait et pas extrait_bloc pour préserver les parenthèses.*)
	| Sub' :: suite ->
		let temp_a, temp_fin = extrait suite in begin
		match temp_a with
		| [Float' str] -> Suf (Float 0., Float (Float.of_string str)), temp_fin
		| [Int' str]   -> Sub (Int 0, Int (int_of_string str)), temp_fin
		| Pao :: fin2 -> let a, fin = extrait_bloc suite in
			Sub (Int 0, a), fin
		| _ -> failwith "Un '-' en début de bloc ne peut qu'être suivit d'un nombre (auquel cas c'est un nombre négatif) ou d'une parenthèse (auquel cas on traite un -(exp))" end
	| To_int' :: suite ->
		let a, fin = extrait_bloc suite in
		To_int a, fin
	| To_float' :: suite ->
		let a, fin = extrait_bloc suite in
		To_float a, fin
	| Pao :: suite ->
		let a, fin = fermer_par [] suite 0 in
		gen_arbre a, fin
	| _ -> failwith "Un bloc commence par un nombre ou une pao"

(*génère un arbre à partir d'une liste de lexeme.*)
(*cette fonction sera appelée récursivement lorsqu'on extrait un bloc de*)
(*lexemes prioritaires, typiquement, un * ou un (exp), et qu'on veut le *)
(*transformer en arbre                                                  *)
and gen_arbre f =
	let a, fin = extrait_bloc f in
	donne a fin

(*t1 est l'arbre gauche du noeud opérateur qui arrive. *)
(*on extrait ensuite le bloc qui va jusqu'au prochain  *)
(*opérateur de niveau de priorité plus faible au sens  *)
(*large, on transforme ce bloc en arbre, et on continue*)
and donne t1 fin =
	match fin with
	| [] -> t1
	| op :: suite ->
		match op with
		| Add' | Adf' | Sub' | Suf'  ->
			(*cf optimisation desequilibre à droite*)
			let b, fin2 = extrait_prio suite 0 in
			donne (apply_op op t1 (gen_arbre b)) fin2
		| Mul' | Muf' | Div' ->
			let b, fin2 = extrait_prio suite 2 in
			donne (apply_op op t1 (gen_arbre b)) fin2
		| Mod' ->
			let b, fin2 = extrait_prio suite 1 in
			donne (apply_op op t1 (gen_arbre b)) fin2

	| _ -> failwith "Après un bloc il ne peut qu'y avoir une opération";;

(*0 = int*)
(*1 = float*)
let typ tr =
	match tr with
	| Int a -> 0
	| To_int a -> 0
	| Float a -> 1
	| To_float a -> 1
	| Add (a, b) -> 0
	| Sub (a, b) -> 0
	| Mul (a, b) -> 0
	| Div (a, b) -> 0
	| Mod (a, b) -> 0
	| Adf (a, b) -> 1
	| Suf (a, b) -> 1
	| Muf (a, b) -> 1;;

(*explicite*)
let rec verif_type tr =
	match tr with
	| Int a -> true
	(*int d'un entier devrait renvoyer ce même entier, donc je ne fais pas planter *)
	(*à ce niveau parce que les correct... euh le suj... . Parce que j'ai oublié c:*)
	| To_int a -> verif_type a
	| Float a -> true
	(*idem que pour to_int*)
	| To_float a -> verif_type a
	| Add (a, b) ->  typ a = 0 && typ b = 0 && verif_type a && verif_type b
	| Sub (a, b) ->  typ a = 0 && typ b = 0 && verif_type a && verif_type b
	| Mul (a, b) ->  typ a = 0 && typ b = 0 && verif_type a && verif_type b
	| Div (a, b) ->  typ a = 0 && typ b = 0 && verif_type a && verif_type b
	| Mod (a, b) ->  typ a = 0 && typ b = 0 && verif_type a && verif_type b
	| Adf (a, b) ->  typ a = 1 && typ b = 1 && verif_type a && verif_type b
	| Suf (a, b) ->  typ a = 1 && typ b = 1 && verif_type a && verif_type b
	| Muf (a, b) ->  typ a = 1 && typ b = 1 && verif_type a && verif_type b;;

(*explicite*)
let anal_synt f =
	let tree = gen_arbre f in
	if verif_type tree
		then tree
		else failwith "Erreur de typage";;

(*compile l'arbre et génère le code principal, et les floats à stocker dans data*)
let rec compile_tree tree code data nb_float =
	match tree with
	(*on ne fait que push l'entier sur la pile*)
	| Int a -> code
				^ "\n\tpushq $"
				^ string_of_int a,
				data,
				nb_float
	(*on prend le résultat de a, et on le transforme en int*)
	| To_int a ->
		let code', data', nb_float' = compile_tree a code data nb_float in begin
		match typ a with
		| 0 -> failwith "you can't transform an integer into an integer, you dumb."
		| 1 -> code'
				^ "\n\tmovsd (%rsp), %xmm0"
				^ "\n\taddq $8, %rsp"
				^ "\n\tcvtsd2siq %xmm0, %rax"
				^ "\n\tpushq %rax",
				data',
				nb_float' end
	(*on "push" le float sur la pile*)
	| Float a -> code
				^ "\n\tsubq $8, %rsp"
				^ "\n\tmovsd F"
				^ string_of_int nb_float
				^ ", %xmm3"
				^ "\n\tmovsd %xmm3, (%rsp)",
				data
				^ "\nF"
				^ string_of_int nb_float
				^ " :"
				^ "\n\t.double "
				^ string_of_float a,
				(nb_float+1)
	(*on prend le résultat de a, et on le transforme en float*)
	| To_float a ->
		let code', data', nb_float' = compile_tree a code data nb_float in begin
		match typ a with
		| 0 -> code'
				^ "\n\tpopq %rax"
				^ "\n\tcvtsi2sdq %rax, %xmm0"
				^ "\n\tsubq $8, %rsp"
				^ "\n\tmovsd %xmm0, (%rsp)",
				data',
				nb_float'

		| 1 -> failwith "You can't transform a float into a float..." end
	(*on évalue les sous arbres, puis on récupère leur résultat, puis on fait l'opération correspondante*)
	| Add (a, b) | Sub (a, b) ->
		let code'', data'', nb_float'' =  compile_tree a code data nb_float in
		let code_, data', nb_float' = compile_tree b code'' data'' nb_float'' in
		let code' = ref code_ in begin
		code' := !code'
				^ "\n\tpopq %rbx"			(*b -> rbx*)
				^ "\n\tpopq %rax";			(*a -> rax*)
		match tree with						(*a op b -> a*)
		| Add (c, d) -> code' := !code'
				^ "\n\taddq %rbx, %rax"
		| Sub (c, d) -> code' := !code'
				^ "\n\tsubq %rbx, %rax" end;
		!code'  ^ "\n\tpushq %rax",
		data',
		nb_float'
	(*on évalue les sous arbres, puis on récupère leur résultat, puis on fait l'opération correspondante*)
	| Mul (a, b) | Div (a, b) | Mod (a, b) ->
		let code'', data'', nb_float'' =  compile_tree a code data nb_float in
		let code_, data', nb_float' = compile_tree b code'' data'' nb_float'' in
		let code' = ref code_ in begin
		!code'	^ "\n\tpopq %rbx"
				^ "\n\tpopq %rax"
				^ "\n\tcqto";
		match tree with
		| Mul (c, d) -> code' := !code'
				^ "\n\timulq %rbx"
				^ "\n\tpushq %rax"
		| Div (c, d) -> code' := !code'
				^ "\n\tidivq %rbx"
				^ "\n\tpushq %rax"
		| Mod (c, d) -> code' := !code'
				^ "\n\tidivq %rbx"
				^ "\n\tpushq %rdx" end;
		!code',
		data',
		nb_float'
	(*on évalue les sous arbres, puis on récupère leur résultat, puis on fait l'opération correspondante*)
	(*ATTENTION : il est fort possible que la multiplication flottante ne marche pas !*)
	| Adf (a, b) | Suf (a, b) | Muf (a, b) ->
		let code'', data'', nb_float'' =  compile_tree a code data nb_float in
		let code_, data', nb_float' = compile_tree b code'' data'' nb_float'' in
		let code' = ref code_ in begin
		code' := !code'
				^ "\n\tmovsd (%rsp), %xmm1"
				^ "\n\taddq $8, %rsp"		(*b -> xmm1*)
				^ "\n\tmovsd (%rsp), %xmm0"
				^ "\n\taddq $8, %rsp";		(*a -> xmm0*)
		match tree with						(*a op b -> a*)
		| Adf (c, d) -> code' := !code'
				^ "\n\taddsd %xmm1, %xmm0"
		| Suf (c, d) -> code' := !code'
				^ "\n\tsubsd %xmm1, %xmm0"
		| Muf (c, d) -> code' := !code'
				^ "\n\tmulsd %xmm1, %xmm0" end;
		!code'  ^ "\n\tsubq $8, %rsp"
				^ "\n\tmovsd %xmm0, (%rsp)",
		data',
		nb_float';;

(*explicite*)
let compile tree =
	let code_v1 = "\t.text"
				^ "\n\t.globl main"
				^ "\n\nmain:" in
	let code_v2, data_v2, nb_float = compile_tree tree code_v1 "" 0 in
	match typ tree with
	| 0 -> code_v2
				^ "\n\tpopq %rsi"
				^ "\n\tmovq $message, %rdi"
				^ "\n\tmovq $0, %rax"
				^ "\n\tcall printf"
				^ "\n\n\tret"
				^ "\n\n\t.data"
				^ "\n\nmessage:"
				^ "\n\t.string \"%d \""
				^ data_v2
	| 1 -> (String.sub code_v2 0 26)
				^ "\n\tpushq %rbp"
				^ (String.sub code_v2 26 ((String.length code_v2) - 26))
				^ "\n\tmovsd (%rsp), %xmm0"
				^ "\n\taddq $8, %rsp"
				^ "\n\tmovq $message, %rdi"
				^ "\n\tmovq $1, %rax"
				^ "\n\tcall printf"
				^ "\n\tpopq %rbp"
				^ "\n\n\tret"
				^ "\n\n\t.data"
				^ "\n\nmessage:"
				^ "\n\t.string \"%f \""
				^ data_v2;;

(*si un arbre est de la forme op1(op2, op2) (sur des entiers) alors on les met dans le même registre xmm_,*)
(*et on fait une seule fois l'opération op2. Je ferais ça lorsque j'aurais pas trop la flemme             *)
(*rendons à césar ce qui est à césat, cette idée émane d'Emmanuel*)
(*l'idée optimisations opt_sub et optimise_code émanent de moi*)
let opt_sop tree = 0;;

(*le but de cette fonction est de réduire le nombre de - effectués.*)
(*j'ai baptisé l'algorithme "moins à bulles" :                                                        *)
(*-On fait remontrer les moins à gauche et à droite (faire remonter les moins = simplifier)           *)
(*-On fait remonter les moins du noeud courant avec ce qui est apparu dans ses fils droit et gauches. *)
(*	En particulier, si il y avait un moins en fils, alors les cas de base assurent qu'il y sera toujou*)
(*-On n'aura jamais à se soucier de si il y a plusieurs couches qui peuvent se simplifier ensemble,   *)
(*	puisqu'alors les couches "profondes" ont déjà été simplifiées avec la couche des fils immédiats   *)
(*-On peut donc se ramener aux cas "élémentaires" qui sont implémentés et qui vont générer toutes les *)
(*	simplifications de ce type possibles. Les cas élémentaires ne doivent jamais compliquer           *)
(*	évidemment, même si c'est pour re simplifier derrière, car sinon l'algorithme n'a pas de garantie *)
(*	de fonctionner                                                                                    *)
let rec opt_sub tree =
	match tree with
	| Int a -> tree
	| Float a -> tree
	| To_int a ->
		let a' = opt_sub a in begin
		match a' with
		| Suf (Float 0., c) -> Sub (Int 0, To_int c)
		| _ -> To_int a' end
	| To_float a ->
		let a' = opt_sub a in begin
		match a' with
		| Sub (Int 0, c) -> Suf (Float 0., To_float c)
		| _ -> To_float a' end
	| Add (a', b') ->
		let a = opt_sub a'
		and b = opt_sub b' in begin
		match a, b with
		| Sub (Int 0, c), Sub (Int 0, d) ->
			Sub (Int 0, Add (c, d))
		| Sub (Int 0, c), _ ->
			Sub (b, c)
		| _, Sub (Int 0, d) ->
			Sub (a, d)
		| _ ->
			Add (a, b) end
	| Sub (a', b') ->
		let a = opt_sub a'
		and b = opt_sub b' in begin
		match a, b with
		| Int 0, Sub (Int 0, d) ->
			d
		| Int 0, Sub (c, d) ->
			Sub (d, c)
		| _, Sub (Int 0, d) ->
			Add (a, d)
		| _ ->
			Sub (a, b) end
	| Mul (a', b') | Div (a', b') | Mod (a', b') ->
		let a = opt_sub a'
		and b = opt_sub b' in begin
		match a, b with
		| Sub (Int 0, c), Sub (Int 0, d) when tree = Mul (a', b') ->
			Mul (c, d)
		| Sub (Int 0, c), _ when tree = Mul (a', b') ->
			Sub (Int 0, Mul (c, b))
		| _, Sub (Int 0, d) when tree = Mul (a', b') ->
			Sub (Int 0, Mul (a, d))
		| _ when tree = Mul (a', b') ->
			Mul (a, b)
		| Sub (Int 0, c), Sub (Int 0, d) when tree = Div (a', b') ->
			Div (c, d)
		| Sub (Int 0, c), _ when tree = Div (a', b') ->
			Sub (Int 0, Div (c, b))
		| _, Sub (Int 0, d) when tree = Div (a', b') ->
			Sub (Int 0, Div (a, d))
		| _ when tree = Div (a', b') ->
			Div (a, b)
		| Sub (Int 0, c), Sub (Int 0, d) when tree = Mod (a', b') ->
			Mod (c, d)
		| Sub (Int 0, c), _ when tree = Mod (a', b') ->
			Sub (Int 0, Mod (c, b))
		| _, Sub (Int 0, d) when tree = Mod (a', b') ->
			Sub (Int 0, Mod (a, d))
		| _ ->
			Mod (a, b) end
	| _ -> failwith "Cas non implémenté. Il est probable que vous ayez voulu optimiser des floats, qui ne sont pas encore pris en charge. Merci de réessayer plus tard.";;

let rec opt_neg tree =
	match tree with
	| Sub (Int 0, Int a) -> Int (-a)
	| Int a -> Int a
	| Float a -> Float a
	| To_int a -> To_int (opt_neg a)
	| To_float a -> To_float (opt_neg a)
	| Add (a, b) -> Add (opt_neg a, opt_neg b)
	| Sub (a, b) -> Sub (opt_neg a, opt_neg b)
	| Mul (a, b) -> Mul (opt_neg a, opt_neg b)
	| Div (a, b) -> Div (opt_neg a, opt_neg b)
	| Mod (a, b) -> Mod (opt_neg a, opt_neg b)
	| Adf (a, b) -> Adf (opt_neg a, opt_neg b)
	| Suf (a, b) -> Suf (opt_neg a, opt_neg b)
	| Muf (a, b) -> Muf (opt_neg a, opt_neg b);;

(*On veut déséquilibrer l'arbre à droite. En effet, on doit se souvenir des valeurs de gauche, en attendant*)
(*la droite, et on n'aime pas se souvenir.*)
(*cette fonction a été supprimée, car l'analyseur syntaxique s'en chargeait déjà tout seul.*)
let opt_des tree = 0;;

(*l'idée est que les accès à la mémoire sont très coûteux, donc on veut travailler au maximum avec *)
(*les registres directement. Donc, pour les entiers, si on croise un push et un pop sur deux lignes*)
(*qui se suivent, on peut le remplacer simplement par un movq. De même avec l'équivalent de push et*)
(*pop pour les flottants même si j'ai eu la flemme de l'implémenter                                *)

(*cette fonction de sera appelé que lors du traitement du corps de main, où les lignes sont exactement séparées*)
(*par un \n, donc pas de saut de lignes.                                                                       *)
let extract_next_line code =
	let i = ref 1
	and n = String.length code in
	while !i < n && code.[!i] <> '\n' do
		i := !i + 1
	done;
	match !i, code with
	| a, _ when a >= n -> code, ""
	| _ -> String.sub code 0 !i, String.sub code !i (n - !i);;

(*cette fonction optimise principalement l'évaluation du sous arbre droit qui produit systématiquement*)
(*un push suivit immédiatement d'un pop                                                               *)
let opt_rbx code =
	let rec aux_parcours debut l1 l2 fin =
		match String.sub l1 2 5 with
		| "pushq" -> begin
			match String.sub l2 2 4 with
			| "popq" ->
				let n1 = String.length l1
				and n2 = String.length l2
				(*il n'y a aucun popq avant deux lignes avant le call, donc c'est bon on peut faire ça*)
				and l3, suite' = extract_next_line fin in
				let l4, suite = extract_next_line suite' in
				aux_parcours (debut ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", " ^ (String.sub l2 7 (n2 - 7))) l3 l4 suite
			| _ ->
				let l3, suite = extract_next_line fin in
				aux_parcours (debut ^ l1) l2 l3 suite end
		| "call " -> debut ^ l1 ^ l2 ^ fin
		| _ ->
			let l3, suite = extract_next_line fin in
			aux_parcours (debut ^ l1) l2 l3 suite
	in
	let n = String.length code in
	let l1, suite = extract_next_line (String.sub code 26 (n-26)) in
	let l2, fin = extract_next_line suite in
	aux_parcours (String.sub code 0 26) l1 l2 fin;;

let rec find_pop mid fin' n =
	let l, fin = extract_next_line fin' in
	match String.sub l 2 4, n, fin with
	| "popq", 0, _ -> mid, l, fin
	| "popq", _, f when f <> "" -> find_pop (mid ^ l) fin (n - 1)
	| "push", _, f when f <> "" -> find_pop (mid ^ l) fin (n + 1)
	| _, _, f when f <> "" -> find_pop (mid ^ l) fin n
	| _ -> failwith "il n'y a pas de prochain pop";;

(*cette fonction optimise les valeurs, qui sont push quand on les rencontre, parce qu'on ne sait pas*)
(*quand on les utilisera pendant la construction naive du code, mais maintenant, on sait, donc on   *)
(*peut se contenter de la move au bon endroit au moment où on en a besoin                           *)
let opt_val code =
	let rec aux_parcours debut fin' =
		match fin' with "" -> debut | _ -> begin
		let l1, fin = extract_next_line fin' in
		match String.sub l1 2 7 with
		| "pushq $" ->
			let mid, l2, suite = find_pop "" fin 0 in
			let n1 = String.length l1
			and n2 = String.length l2 in
			(*les push et pop du milieu sont encapsulé par le push et pop local, par principe d'une pile*)
			(*donc on peut optimiser le milieu indépendament de la fin*)
			let mid_opt = aux_parcours "" mid in
			let new_debut = debut ^ mid_opt ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", " ^ (String.sub l2 7 (n2 - 7)) in
			aux_parcours new_debut suite
		| "call pr" -> debut ^ fin'
		| _ -> aux_parcours (debut ^ l1) fin end
	in
	aux_parcours (String.sub code 0 26) (String.sub code 26 ((String.length code) - 26));;

(*il arrive souvent qu'on push le résultat gauche puis qu'on move le résultat droit puis qu'on pop*)
(*le résultat gauche aussi sec (dans le cas où à droite il y a un nombre). Dans ce cas, autant ne *)
(*rien faire                                                                                      *)
(*C'est en fait le seul cas où on a un push et un pop séparés d'une seule ligne                   *)
let opt_rax code =
	let rec aux_parcours debut l1 l2 l3 fin =
		match String.sub l1 2 5 with
		| "pushq" -> begin
			match String.sub l3 2 4 with
			| "popq" ->
				(*il n'y a aucun popq avant deux lignes avant le call, donc c'est bon on peut faire ça*)
				let l4, suite' = extract_next_line fin in
				let l5, suite = extract_next_line suite' in
				aux_parcours debut l2 l4 l5 suite
			| _ ->
				let l4, suite = extract_next_line fin in
				aux_parcours (debut ^ l1) l2 l3 l4 suite end
		| "call " -> debut ^ l1 ^ l2 ^ l3 ^ fin
		| _ ->
			let l4, suite = extract_next_line fin in
			aux_parcours (debut ^ l1) l2 l3 l4 suite
	in
	let n = String.length code in
	let l1, suite = extract_next_line (String.sub code 26 (n-26)) in
	let l2, fin' = extract_next_line suite in
	let l3, fin = extract_next_line fin' in
	aux_parcours (String.sub code 0 26) l1 l2 l3 fin;;

(*QUI A DIT QUIL FALLAIT UTILISER LA PILE ???? QU'IL SE DENONCE !!!*)
let opt_max code =
	(*on cosidère qu'on résèrve                                      *)
	(*rax à l'arbre gauche,                                          *)
	(*rbx à l'arbre droit,                                           *)
	(*rdx à la division et au modulo                                 *)
	(*rcx je sais pas ce qu'il fout là, mais la division me fait peur*)
	(*		donc dans le doute j'y touche pas                        *)
	(*on ne touche pas aux registres de fonctions au cas ou on doit  *)
	(*		faire un vrai compilateur avec des fonctions plus tard   *)
	let rec aux_parcours debut fin' reg =
		match fin' with "" -> debut | _ -> begin
		let l1, fin = extract_next_line fin' in
		match String.sub l1 2 5 with
		| "pushq" ->
			let mid, l2, suite = find_pop "" fin 0 in
			let n1 = String.length l1
			and n2 = String.length l2 in begin
			match reg with
			(*on gère les registres 12 à 15 comme une mini pile,*)
			(*si elle est épuisée, on est contraint d'utiliser la vrai pile*)
			(*en particulier, si elle est épuisée, elle le sera pour toute la "fin'" par construction*)
			(*(cf autres cas)*)
			(*ce cas ne sera jamais appelé, on ne s'embête pas a optimiser quand on a rempli la pile*)
			| 4 -> debut ^ fin'
			(*si la "pile" n'est pas épuisée, alors on stocke la valeur dans la "pile", et on s'occupe *)
			(*du code au milieu de ce stockage. Ce code ne pourra bien évidemment pas utiliser l'indice*)
			(*de pile qui vient d'être utilisé, par contre, la suite pourra ! D'où la remarque du cas 4*)
			(*puisque si on est dans le cas 4 alors on est en train de traiter un code du milieu qui a *)
			(*épuisé sa pile                                                                           *)
			| 0 ->
				let mid_opt = aux_parcours "" mid 1 in
				let new_debut = debut ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", %r12"
							^ mid_opt ^ "\n\tmovq %r12, " ^ (String.sub l2 7 (n2 - 7)) in
				aux_parcours new_debut suite 0
			| 1 ->
				let mid_opt = aux_parcours "" mid 2 in
				let new_debut = debut ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", %r13"
							^ mid_opt ^ "\n\tmovq %r13, " ^ (String.sub l2 7 (n2 - 7)) in
				aux_parcours new_debut suite 1
			| 2 ->
				let mid_opt = aux_parcours "" mid 3 in
				let new_debut = debut ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", %r14"
							^ mid_opt ^ "\n\tmovq %r14, " ^ (String.sub l2 7 (n2 - 7)) in
				aux_parcours new_debut suite 2
			| 3 ->
				let mid_opt = mid in
				let new_debut = debut ^ "\n\tmovq " ^ (String.sub l1 8 (n1 - 8)) ^ ", %r15"
							^ mid_opt ^ "\n\tmovq %r15, " ^ (String.sub l2 7 (n2 - 7)) in
				aux_parcours new_debut suite 3 end
		| "call " -> debut ^ fin'
		| _ -> aux_parcours (debut ^ l1) fin reg end
	in
	aux_parcours (String.sub code 0 26) (String.sub code 26 ((String.length code) - 26)) 0;;

let compile_opt tree =
	let tr_v1 = opt_sub tree in
	let tr_v2 = opt_neg tr_v1 in
	let code_v1 = compile tr_v2 in
	let code_v2 = opt_rbx code_v1 in
	let code_v3 = opt_val code_v2 in
	let code_v4 = opt_rax code_v3 in
	let code_v5 = opt_max code_v4 in
	code_v5;;

(*
let f1 = "-(4*(-3+(18/-2)))" ;;
let f2 = string_to_list f1 ;;
let f3 = anal_lex f2 ;;
let f4 = anal_synt f3 ;;
let code = compile_opt f4;;

let f1 = "-3+-5*-4/9%7+3-2-2*5*14/8+2" ;;

let rec en n =
  match n with
  |	0 -> "(1 + 1)"
  |	_ -> (en (n-1)) ^ "*" ^ (en (n-1));;

let f1 = en 5;;
*)


let file_name = Sys.argv[0];;
let file = open_in file_name ;;

(*cette construction permet de faire la gestion de variable aisément.*)
(*
and l = ref [] in
let cond = true in
while cond do
	try
		l := (input_line file) :: !l
	with End_of_file ->
		close_in file*)

let f1 = input_line file;;
close_in file;;
let f2 = string_to_list f1 ;;
let f3 = anal_lex f2 ;;
let f4 = anal_synt f3 ;;
let code = compile f4;;

let i = ref 0;;
while file_name.[i] <> '.' do
	i := !i + 1
done;;
let nom = String.sub file_name 0 i;;

let oc = open_out (nom ^ ".s");;
Printf.fprintf oc "%s\n" code;;
close_out oc;;
