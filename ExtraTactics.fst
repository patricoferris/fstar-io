module ExtraTactics

open FStar.Tactics

let grewrite_eq (b:binder) : Tac unit =
  match term_as_formula (type_of_binder b) with
  | Comp (Eq _) l r ->
    grewrite l r;
    iseq [idtac; (fun () -> exact (binder_to_term b))]
  | _ -> fail "failed in grewrite_eq"


// let rec extract_nth (n:nat) (l : list 'a) : option ('a * list 'a) =
//   match n, l with
//   | _, [] -> None
//   | 0, hd::tl -> Some (hd, tl)
//   | _, hd::tl -> begin
//     match extract_nth (n-1) tl with
//     | Some (hd', tl') -> Some (hd', hd::tl')
//     | None -> None
//   end

// let bump_nth (n:pos) : Tac unit =
//   // n-1 since goal numbering begins at 1
//   match extract_nth (n - 1) (goals ()) with
//   | None -> fail "bump_nth: not that many goals"
//   | Some (h, t) -> set_goals (h :: t)


private
let rec innermost_sc (t:term) : Tac term =
  match inspect t with
  | Tv_Match s _ -> innermost_sc s
  | _ -> t

let get_match_body () : Tac term =
  match FStar.Reflection.Formula.unsquash (cur_goal ()) with
  | None -> fail "Goal is not squashed"
  | Some t -> match inspect t with
             | Tv_Match sc _ -> innermost_sc sc
             | _ -> fail "Goal is not a match"

let rec last (x : list 'a) : Tac 'a =
    match x with
    | [] -> fail "last: empty list"
    | [x] -> x
    | _::xs -> last xs

(** When the goal is [match e with | p1 -> e1 ... | pn -> en],
destruct it into [n] goals for each possible case, including an
hypothesis for [e] matching the correposnding pattern. *)
let branch_on_match () : Tac unit =
    focus (fun () ->
      let x = get_match_body () in
      let _ = t_destruct x in
      iterAll (fun () ->
        let bs = repeat intro in
        let b = last bs in (* this one is the equality *)
        // grewrite_eq b;
        rewrite_eqs_from_context ();
        norm [iota])
    )

let let_intro () : Tac unit =
    focus (fun () ->
      let x = get_match_body () in
      let _ = t_destruct x in
      iterAll (fun () -> ignore (intro ()); ignore (intro ()); grewrite_eq (intro ()))
    )

let rewrite_lemma (n:nat) (m:nat) : Tac unit =
    let zz = match (List.Tot.nth (cur_binders ()) n) with
    | Some y -> y | None -> fail "no binder" in
    
    let zz' = match (List.Tot.nth (cur_binders ()) m) with
    | Some y -> y | None -> fail "no binder" in
    
    let b' = instantiate (binder_to_term zz) (binder_to_term zz') in
    mapply (binder_to_term b')
 
    // by (explode (); bump_nth 3; 
    // let bs = List.Tot.map (fun (_, b) -> b) (skolem ()) in
    // iter (fun b -> ignore (trytac (fun () -> ignore (destruct_and (binder_to_term b))))) bs;
    // rewrite_eqs_from_context ();
    // let _ = l_intros () in
    // split ();
    // bump_nth 2;
    // explode ();
    // // let f = cur_formula () in
    // // dump (term_to_string (quote f));
     
    // //branch_on_match (); 
    // dump "H") =

let copy_binder (b:binder) : Tac binder =
  focus (fun () ->
    let nb = tcut (type_of_binder b) in
    flip ();
    exact (binder_to_term b);
    nb
  )

let get_binder (n:nat) : Tac binder =
  match (List.Tot.nth (cur_binders ()) n) with
  | Some y -> y 
  | None -> fail "no binder"
  
let rec instantiate_n_times_with_none (b:binder) (n : nat{n>0}) : Tac binder =
  let b' = instantiate b (fresh_uvar None) in
  if n = 1 then b else (
    let r = instantiate_n_times_with_none b' (n-1) in
    clear b';
    r
  )


let rec instantiate_multiple_foralls (b:binder) (l : list term) : Tac binder =
  match l with
  | [] -> b
  | h :: tail ->
    let b' = instantiate (binder_to_term b) h in
    let r = instantiate_multiple_foralls b' tail in
    (if List.length tail = 0 then ()
    else clear b');
    r

(** The boom_binder is not working. Binder can be any kind of binder,
but I only try to destruct recursivly the ones that are conjunctions. destruct_and unfortunately throws an error if the binder is not a
conjunctions and I can not catch the error. **)
// let rec boom_binder (b : binder) : Tac bool =
//   let bv, (x, y) = inspect_binder b in
//   match x with
//   | Q_Explicit -> begin
//     try (let b1, _ = destruct_and b in
//          // ignore (boom_binder b1);
//          true)
//     with | _ -> false
//   end
//   | _ -> false

//   // match term_as_formula' b with
//   // | Name 
//   // | And _ _ -> (dump "cezar123"; try (let b1, _ = destruct_and b in
//   //                   ignore (boom_binder b1);
//   //                   true)
//   //             with | _ -> false)
//   // | _ -> false

// let boom () : Tac unit =
//     ignore (
//       repeatseq (fun () -> first [
//         (fun () -> ignore (l_intro ()));
//           // let x = l_intro () in
//           // if boom_binder x then (
//           //   rewrite_eqs_from_context ();
//           //   norm [iota]
//           // ) else ()
//           // );
//         (fun () -> ignore (split ()));
//         (fun () -> branch_on_match ())]))
