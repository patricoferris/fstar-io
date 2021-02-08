module Common

open FStar.Exn

exception Contract_failure

type maybe a = either a exn

type file_descr = int

let compose #a #b #c (g:b->c) (f:a->b) = fun x -> g (f x)

let id #a (x:a) = x

unfold let inl_app #a #b (f:a -> b) : maybe a -> maybe b =
  fun x ->
    match x with
    | Inl x -> Inl (f x)
    | Inr err -> Inr err


let cdr #a (_, (x:a)) : a = x

let elim_pure #a #wp ($f : unit -> PURE a wp) p :
  Pure a (requires (wp p)) (ensures (fun r -> p r)) =
  //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
  // ^ basically this, requires monotonicity
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  f ()

let rec prefix_of (l1 l2: list 'a)
: Tot Type0 (decreases l2)
= match l1, l2 with
  | [], [] -> True
  | [], _ -> True
  | _, [] -> False
  | h1 :: t1, h2 :: t2 -> h1 == h2 /\ t1 `prefix_of` t2

let rec prefix_of_length (l1 l2: list 'a)
: Lemma
  (requires (prefix_of l1 l2))
  (ensures (List.length l1 <= List.length l2))
  (decreases l1)
= match l1, l2 with
  | h1 :: t1, h2 :: t2 ->
    prefix_of_length t1 t2
  | _ -> ()

let rec suffix_of (l1 l2: list 'a)
: Tot Type0 (decreases l2)
= l1 == l2 \/ (match l2 with
  | [] -> False
  | _ :: q ->  l1 `suffix_of` q)

let rec suffix_of_length (l1 l2: list 'a)
: Lemma
  (requires (suffix_of l1 l2))
  (ensures (List.length l1 <= List.length l2))
  (decreases l2) =
  admit ()

let suffix_of_append () :
  Lemma (forall h l1 l2. suffix_of h ((List.rev l1) @ (List.rev l2) @ h)) =
  admit()

val rev_nil : (a:Type) -> Lemma (List.rev #a [] == [])
let rev_nil a = ()

val append_rev: l1:list 'a -> l2:list 'a ->
  Lemma (
    ((List.rev l1)@(List.rev l2)) == (List.rev (l2@l1)))
let append_rev l1 l2 = List.rev_append l2 l1
