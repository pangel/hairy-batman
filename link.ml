(*let lidoc = ["./shift_lemmas.v"];;*)

let lidoc = ["env_subst.v";"inference.v";"init.v";"lemmas_narrowing.v";"lemmas_regularity.v";"narrowing.v";"red.v";"regularity.v";"shift_lemmas.v"];;
let isdelim c = (c = ' ' || c = ':') ;;

let get2 s = 
  let curs = ref 0 in
  let fst = ref false in
  let cont = ref true in
  let where1 = ref 0 in
  let where = ref 0 in
  while (!cont) do
    if (isdelim(s.[!curs])&& (!fst)) then 
      (
	where := !curs;
	cont := false
      )
    else
      (
	if (isdelim(s.[!curs])) then
	     (
	       where1 := !curs;
	       incr curs;
	       fst := true
	     )
	    else
	      incr curs
      )
  done;
  String.sub s (!where1+1) (!where - !where1 -1);;

type isthere = 
  |Def of string
  |Lem of string
  |Thm of string
  |Fix of string
  |None;;

let line_get s = 
  let n = String.length s in
  if (n >= 10 && (String.sub s 0 10) = "Definition") then (Def(get2 s))
  else if (n >= 5 && (String.sub s 0 5) = "Lemma") then (Lem(get2 s))
  else if (n >= 8 && (String.sub s 0 8) = "Fixpoint") then (Fix(get2 s))
  else if (n >= 7 && (String.sub s 0 7) = "Theorem") then (Thm(get2 s))
  else None

let f_get doc = 
  let input = open_in doc in
  let rep = ref [] in
  (
    try 
      while (true) do 
	let s = input_line (input) in
	let a = line_get s in
	match (a) with
	|None -> ()
	|_ -> rep := (a,doc) :: (!rep)
      done
    with
    |End_of_file -> ();
  );
  !rep;;
		  
let get_l () = 
  let rep = ref [] in
  let rec aux evth = match evth with
    |p::q -> rep := (f_get p)@(!rep); aux q
    |[] -> ()
  in
  aux lidoc;
  !rep;;

Str.regexp;;

let deal_l s l scope = 
  let n = String.length s in
  if (n = 0) then (scope,[])
  else if (n >= 3 && (String.sub s 0 3) = "(**") then (None,[])
  else if (n >= 4 && (String.sub s 0 4) = "Qed.") then (None,[])
  else if (n >= 9 && (String.sub s 0 9) = "Inductive") then (None,[])
  else if (n >= 8 && (String.sub s 0 8) = "Implicit") then (None,[])
  else if (n >= 8 && (String.sub s 0 8) = "Fixpoint") then (Fix(get2 s),[])
  else if (n >= 9 && (String.sub s 0 9) = "Arguments") then (None,[])
  else if (n >= 10 && (String.sub s 0 10) = "Definition") then ((Def(get2 s)),[])
  else if (n >= 5 && (String.sub s 0 5) = "Lemma") then (Lem(get2 s),[])
  else if (n >= 7 && (String.sub s 0 7) = "Theorem") then (Thm(get2 s),[])
  else (
    let rep = ref [] in
    let rec search li = match li with
      |(Thm(st),d)::q -> 
	(
	  try (
	    let rst = Str.regexp (st^("[^A-Za-z0-9_]")) in
	    Str.search_forward rst s 0;
	    rep := (Thm(st),scope) :: (!rep)
	  )
	  with
	  |Not_found -> ()
	);
	search q
      |(Fix(st),d)::q -> 
	(
	  try (
	    let rst = Str.regexp (st^("[^A-Za-z0-9_]")) in
	    Str.search_forward rst s 0;
	    rep := (Fix(st),scope) :: (!rep)
	  )
	  with
	  |Not_found -> ()
	);
	search q
      |(Lem(st),d)::q -> 
	(
	  try (
	    let rst = Str.regexp (st^("[^A-Za-z0-9_]")) in
	    Str.search_forward rst s 0;
	    rep := (Lem(st),scope) :: (!rep)
	  )
	  with
	  |Not_found -> ()
	);
	search q
      |(Def(st),d)::q -> 
	(
	  try (
	    let rst = Str.regexp (st^("[^A-Za-z0-9_]")) in
	    Str.search_forward rst s 0;
	    rep := (Def(st),scope) :: (!rep)
	  )
	  with
	  |Not_found -> ()
	);
	search q

      |_ -> ()
    in
    search l;
    (scope,!rep);
  );;

let deal_doc d l = 
  let rep = ref [] in
  let input = open_in d in
  let sco = ref (None) in
  (
    try 
      while (true) do 
	let s = input_line (input) in
	let a,b = deal_l s l (!sco) in
	sco := a;
	rep := (b) @ (!rep);
      done
    with
    |End_of_file -> ();
  );
  !rep;;

let print_label out l = 
  let rec aux li = match li with
    |p::q -> 
      (
	match p with
	|Thm(s) -> 
	  Printf.fprintf out ("Thm %s\n") s
	|Fix(s) -> 
	  Printf.fprintf out ("Fix %s\n") s
	|Lem(s) -> 
	  Printf.fprintf out ("Lem %s\n") s
	|Def(s) -> 
	  Printf.fprintf out ("Def %s\n") s
	|_ -> ();
      );
      aux q
    |[] -> ()
  in aux l
;;
let toprint = ["Thm","Lem"] ;;
let rec insert_key k a l = match l with
  |(elem,b)::q when (k = elem) -> (elem,(a::b))::q
  |(elem,b)::q -> (elem,b)::(insert_key k a q)
  |[] -> [(k,[a])];;

let transform lab = 
  let rep = ref [] in
  let rec aux l = match l with
    |(a,d)::q -> rep := (insert_key (d) a (!rep)); aux q
    |[] -> ()
  in
  aux lab;
  !rep;;

let cur = ref 0 ;;
let fresh () = incr cur; "cluster"^(string_of_int (!cur));;

let print_link out l (lab : (isthere * string) list) =
  Printf.fprintf out "%s\n" ("digraph G {");
  Printf.fprintf out "%s\n" "rankdir=\"LR\"";
  Printf.fprintf out "%s\n" "K=0.1";
  Printf.fprintf out "%s\n" "fixedsize=true"; 
  Printf.fprintf out "%s\n" "size=\"40.,50.\""; 
  Printf.fprintf out "%s\n" "ratio = \"1.7\"";
  Printf.fprintf out "%s\n" "center = true";
  Printf.fprintf out "%s\n" "nodesep = 0.02";

  let li = transform lab in
  let rec aux1 li = match li with
    |(Thm(s))::q -> 
      (
      	Printf.fprintf out ("Thm_%s [width = 4, height = 2, shape = rectangle, color = lightblue, style = filled, fontsize = 30]\n") s;
	aux1 q
      )
(*    |Fix(s)::q -> 
      (
      	Printf.fprintf out ("Fix_%s [shape = ellipse, color = red, style = filled]\n") s;
	aux1 q
      )
 *)
    |(Lem(s))::q -> 
      (
      	  Printf.fprintf out ("Lem_%s [width = 4, height = 2, shape = ellipse, color = purple, style = filled, fontsize = 30]\n") s;
	  aux1 q
      )
    |_::q -> aux1 q
    |[] -> ()
  in
  let rec aux2 ll =
    match ll with
    |(k,l)::q -> 
      Printf.fprintf out "subgraph %s {\n" (fresh ());
      Printf.fprintf out "label = \"%s\";\n" (k);
      Printf.fprintf out "fontsize = 45\n";
      aux1 l;
      Printf.fprintf out "%s\n" ("}");
      aux2 q
    |[] -> ()
  in
  aux2 li;
  let rec aux li = match li with
    |p::q -> 
      (
	match p with
	|Thm(s),Thm(s2) -> 
	  Printf.fprintf out ("Thm_%s -> Thm_%s [weight=1.2,penwidth=5,arrowsize = 2]\n") s s2
	|Lem(s),Thm(s2) -> 
	  Printf.fprintf out ("Lem_%s -> Thm_%s [weight=1.2,penwidth=5,arrowsize = 2]\n") s s2
(*
	|Fix(s),Thm(s2) -> 
	  Printf.fprintf out ("Fix_%s -> Thm_%s\n") s s2

	|Thm(s),Fix(s2) -> 
	  Printf.fprintf out ("Thm_%s -> Fix_%s\n") s s2
	|Lem(s),Fix(s2) -> 
	  Printf.fprintf out ("Lem_%s -> Fix_%s\n") s s2
	|Fix(s),Fix(s2) -> 
	  Printf.fprintf out ("Fix_%s -> Fix_%s\n") s s2
 *)
	|Thm(s),Lem(s2) -> 
	  Printf.fprintf out ("Thm_%s -> Lem_%s [weight=1.2,penwidth=5,arrowsize = 2]\n") s s2
	|Lem(s),Lem(s2) -> 
	  Printf.fprintf out ("Lem_%s -> Lem_%s [weight=1.2,penwidth=5,arrowsize = 2]\n") s s2
(*
	|Fix(s),Lem(s2) -> 
	  Printf.fprintf out ("Fix_%s -> Lem_%s\n") s s2
 *)
	|_ -> ();
      );
      aux q
    |[] -> ()
  in 
  aux l;
  Printf.fprintf out "%s" "}"
;;

let remove_dup l = 
  let rec remove_aux l a accu= match l with
    |p::q -> 
      if (a = p) then remove_aux q a accu else remove_aux q a (p::accu)
    |[] -> accu
    and rem l = match l with
      |p::q -> p::(rem (remove_aux q p []))
      |[] -> []
  in
  rem l;;

let rec remove_loop l = match l with
  |p::q ->
    ( 
      match p with
      |(Def(x)),(Def(y)) when (x = y) -> remove_loop q
      |(Fix(x)),(Fix(y)) when (x = y) -> remove_loop q
      |(Thm(x)),(Thm(y)) when (x = y) -> remove_loop q
      |(Lem(x)),(Lem(y)) when (x = y) -> remove_loop q
      |_ -> p::(remove_loop q)
    )
  |[] -> []
;;

let main () = 
  let label = get_l () in
  let tot_rep = ref [] in
  let rec aux l = match l with
    |p::q -> tot_rep := (deal_doc p label) @ (!tot_rep) ; aux q
    |[] -> ()
  in
  aux lidoc;
  let outl = open_out "outlabel" in
  let outli = open_out "outlink" in
  tot_rep := remove_loop (remove_dup (!tot_rep));
  print_link outli (!tot_rep) label;
  close_out outl;
  close_out outli;
  print_int (List.length label);
  (label,!tot_rep);;

main ();;

