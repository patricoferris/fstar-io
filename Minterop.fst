module Minterop

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open MIIO.Effect

(**
lift: IO -> IIO (Done - in IIO.Effect.fst)
lift: MIO -> MIIO (the lift from IO to IIO should work automatically)

export: IIO -> MIIO (Done: exportable_IIO)
export: IO -> MIIO (Done: exportable_IO - lift automatically to IIO,
                          and then use export: IIO -> MIIO)

import: MIIO -> IIO (Done: importable_MIIO_IIO)
import: MIO -> IIO (Done: importable_MIO_IIO) lift from MIO to MIIO,
                          and then import to IIO)

Not possible cases:
IIO -> IO
IIO -> MIO (the runtime checks can not be
           enforced statically because GetTrace is missing in IO)

IO -> MIO (the preconditions can not be enforced
           dynamically because GetTrace is missing in IO)

MIO -> IO (we can not enforce preconditions
           statically)

MIIO -> IO
MIIO -> MIO (Not possible because we can not get rid of GetTrace)
**)

(** ** `ml` class *)
(* Intuition, this are morally MIO types written in F* syntax *)

class ml (t:Type) = { mldummy : unit }

// Basic MIO types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }
instance ml_pair t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 * t2) = { mldummy = () }
instance ml_mioarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> MIO t2) = { mldummy = () }
instance ml_miioarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> MIIO t2) = { mldummy = () }

instance ml_file_descr : ml file_descr = { mldummy = () }
(** CA: Is this required? **)
// instance ml_monitorable_prop : ml monitorable_prop = { mldummy = () }



(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
// - the types of values we can safely `import` from malicious MIO code
// - the types of values we can safely `export` to malicious MIO code
// This interoperability model includes extraction as well as
// adding extra checking and wrapping.
// *)

(** TODO:
we have 3 importable classes and I don't think they are named very well.

Context:
One thing we learned is that our import function should not throw errors because we
need to use it in writing specifications, therefore we want an import function of
type t1 -> option t2. In the same time, it is much easier to write code using
exceptions, therefore there is the exn_import, which is just a lift from option to
exceptions.

There is a special case for functions. Functions always can be imported, because
the cast from the strong type to the weak type is done inside the function (?).
Also, ml types can be always imported safely. Therefore, I added safe_import of type
t1 -> t2. I am not that happy with the safe_ part in the name. To me import and
safe_import are both 'safe'.
**)

class exportable (t : Type) = { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; import : itype -> option t; ml_itype : ml itype }

class exn_importable (t : Type) = { eitype : Type; exn_import : eitype -> MIO t; ml_eitype : ml eitype }
class safe_importable (t : Type) = { sitype : Type; safe_import : sitype -> t; ml_sitype : ml sitype }

let mk_exportable (#t1 t2 : Type) {| ml t2 |} (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) {| ml t1 |} (imp : t1 -> option t2) : importable t2 =
  { itype = t1; import = imp; ml_itype = solve }
let mk_exn_importable (t1 #t2 : Type) {| ml t1 |} (imp : t1 -> MIO t2) : exn_importable t2 =
  { eitype = t1; exn_import = imp; ml_eitype = solve }
let mk_safe_importable (t1 #t2 : Type) {| ml t1 |} (imp : t1 -> t2) : safe_importable t2 =
  { sitype = t1; safe_import = imp; ml_sitype = solve }

(** Are this two needed? **)
instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) = d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance exportable_ml t {| ml t |} : exportable t = mk_exportable t (fun x -> x)
instance safe_importable_ml t {| ml t |} : safe_importable t = mk_safe_importable t (fun x -> x)

instance importable_safe_importable t {| d:safe_importable t |} : importable t =
  mk_importable d.sitype #t #d.ml_sitype (fun (x:d.sitype) -> (Some (safe_import x)) <: option t)

instance exn_importable_importable t {| d:importable t |} : exn_importable t =
  mk_exn_importable d.itype (fun (x:d.itype) ->
    (match import x with
    | Some x -> x
    | None -> IO.Effect.throw Contract_failure) <: MIO t)

instance exportable_refinement t {| d:exportable t |} (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) export

class checkable (#t:Type) (p : t -> Type0) = { check : (x:t -> b:bool{b ==> p x}) }
instance general_is_checkeable t (p : t -> bool) : checkable (fun x -> p x) = { check = fun x -> p x }
class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}
 
class checkable4 (#b1 #b2 #b3 #b4:Type) (p : b1 -> b2 -> b3 -> b4 -> Type0) = { check4 : (x1:b1 -> x2:b2 -> x3:b3 -> x4:b4 -> b:bool{b ==> p x1 x2 x3 x4}) }
instance general_is_checkable4 b1 b2 b3 b4 (p : b1 -> b2 -> b3 -> b4 -> bool) : checkable4 (fun x1 x2 x3 x4 -> p x1 x2 x3 x4) = { check4 = fun x1 x2 x3 x4 -> p x1 x2 x3 x4}

instance importable_refinement
  t {| d:importable t |}
  (rp : t -> Type0) {| checkable rp |} :
  Tot (importable (x:t{rp x})) =
  mk_importable (d.itype)
    (fun (x:d.itype) ->
      (match import x with
      | Some x -> if check #t #rp x then Some x else None
      | None -> None) <: option (x:t{rp x}))

let test_refinement () : MIO (y:int{y = 5}) = exn_import 5

instance exportable_pair t1 t2 {| d1:exportable t1 |} {| d2:exportable t2 |} : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

instance importable_pair t1 t2 {| d1:importable t1 |} {| d2:importable t2 |} : importable (t1 * t2) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) ->
    (match (import x, import y) with
    | (Some x, Some y) -> Some (x, y)
    | _ -> None) <: option (t1 * t2))

instance importable_dpair_refined t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:importable t2 |} {| d3:checkable2 p |} : importable (x:t1 & y:t2{p x y}) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
      (match (import x', import y') with
       | (Some x, Some y) ->
               if check2 #t1 #t2 #p x y then Some (| x, y |) else None
       | _ -> None) <: option (x:t1 & y:t2{p x y}))

let test_dpair_refined () : MIO (a:int & b:int{b = a + 1}) = exn_import (10, 11)

// A typed term in an untyped context
instance exportable_arrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> Tot t2)  =
  mk_exportable (d1.itype -> MIO d2.etype)
    (fun (f:(t1 -> t2)) -> (fun (x:d1.itype) -> export (f (exn_import x)) <: MIO d2.etype))
 
// instance exportable_exarrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> Ex t2)  =
//   mk_exportable (d1.itype -> MIO d2.etype)
//     (fun (f:(t1 -> Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: MIO d2.etype))

instance exportable_mlarrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> MIO t2)  =
  mk_exportable (d1.itype -> MIO d2.etype)
    (fun (f:(t1 -> MIO t2)) ->
      (fun (x:d1.itype) -> export (f (exn_import x)) <: MIO d2.etype))

// An untyped term in a typed context
instance importable_mlarrow t1 t2 {| d1:exportable t1 |} {| d2:importable t2 |} : safe_importable (t1 -> MIO t2)  =
  mk_safe_importable (d1.etype -> MIO d2.itype)
    (fun (f:(d1.etype -> MIO d2.itype)) ->
      (fun (x:t1) -> exn_import (f (export x)) <: MIO t2))
 
// Example trueish
let trueish (x:int{x >= 0}) : bool = true
let trueish' (x:int) : MIO bool = (trueish (exn_import x))
let trueish'' : int -> MIO bool = export trueish

instance importable_darrow_refined
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (p:t1->t2->Type0) {| d3:checkable2 p |} :
  Tot (safe_importable (x:t1 -> MIO (y:t2{p x y}))) =
  mk_safe_importable (d1.etype -> MIO d2.itype) #(x:t1 -> MIO (y:t2{p x y}))
    (fun (f:(d1.etype -> MIO d2.itype)) ->
      (fun (x:t1) ->
        let y : t2 = exn_import (f (export x)) in
        if check2 #t1 #t2 #p x y then y
        else IO.Effect.throw Contract_failure))

// Example incr

let incr (x:int) : int = x + 1

let incr2 : int -> MIO int = export incr

let p x y : bool = (y = x + 1)
let incr'' (x:int) : MIO (y:int{p x y}) = exn_import (incr x)

// TODO: fix this. see https://github.com/FStarLang/FStar/issues/2128
val incr' : (x:int) -> MIO (y:int{p x y})
// let incr' = safe_import incr2

instance exportable_purearrow_spec t1 t2 (pre : t1 -> Type0) (post : t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:exportable t2 |} {| d3:checkable pre |} : exportable ((x:t1) -> Pure t2 (pre x) (post x)) =
  mk_exportable (d1.itype -> MIO d2.etype)
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = exn_import x in
        (if check #t1 #pre x then (
          export (f x)
        ) else IO.Effect.throw Contract_failure) <: MIO d2.etype))

let _export_IIO
  (#t1:Type) {| d1:importable t1 |}
  (#t2:Type) {| d2:exportable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post: t1 -> trace -> maybe t2 -> trace -> Type0)
  (f:(x:t1 -> IIO t2 pi (pre x) (post x))) :
  Tot (d1.itype -> MIIO d2.etype) =
    (fun (x:d1.itype) ->
      match import x with
      | Some x -> (
        let h = get_trace () in
        (** TODO: Can any global property help us remove 'enforced_globally'?
            The context is instrumented, therefore this should check **)
        if check2 #t1 #trace #pre x h && enforced_globally pi h then
          export (f x)
        else IIO.Effect.throw Contract_failure)
      | None -> IIO.Effect.throw Contract_failure)

instance exportable_IIO
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:exportable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post: t1 -> trace -> maybe t2 -> trace -> Type0) :
  Tot (exportable (x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_exportable
    (d1.itype -> MIIO d2.etype)
    (_export_IIO pi pre post)

instance exportable_IO
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:exportable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post: t1 -> trace -> maybe t2 -> trace -> Type0) :
  Tot (exportable (x:t1 -> IO t2 pi (pre x) (post x))) =
  mk_exportable
    (d1.itype -> MIIO d2.etype)
    (fun (f:(x:t1 -> IO t2 pi (pre x) (post x))) ->
      _export_IIO pi pre post f)

let rec _import_pi_IIO
  (#b:Type)
  (tree : iio b)
  (pi:monitorable_prop) :
  IIO b pi (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> r
  | Throw r -> IIO.Effect.throw r
  | Call GetTrace argz fnc ->
      let h = IIO.Effect.get_trace () in
      let z' : iio b = fnc (Inl h) in
      rev_append_rev_append ();
      _import_pi_IIO z' pi
  | Call (cmd:io_cmds) argz fnc ->
      let rez : res cmd = IIO.Effect.dynamic_cmd pi cmd argz in
      let z' : iio b = fnc (Inl rez) in
      rev_append_rev_append ();
      _import_pi_IIO z' pi

let _import_pre_pi_IIO
  (#t1:Type) {| d1:exportable t1 |}
  (#t2:Type) {| d2:importable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| checkable2 pre |}
  (f : d1.etype -> MIIO d2.itype)
  (x:t1) :
  IIO t2 pi (pre x) (fun _ _ _ -> True) =
  rev_append_rev_append ();
  let x' : d1.etype = export x in
  let h = get_trace () in
  (** The pre-condition of MIO is always true so we can pass any
  post-condition to reify **)
  let tree : iio d2.itype = (* MIO?.*)reify (f x') h (fun _ _ -> True) in
  let (r:d2.itype) = _import_pi_IIO tree pi in
  match import r with
  | Some a -> a
  | None -> IIO.Effect.throw #t2 Contract_failure

let rec suffix_of (l1 l2: trace)
: Tot Type0 (decreases l2)
= l1 == l2 \/ (match l2 with
  | [] -> False
  | _ :: q ->  l1 `suffix_of` q)

let rec suffix_of_length (l1 l2: trace)
: Lemma
  (requires (suffix_of l1 l2))
  (ensures (List.length l1 <= List.length l2))
  (decreases l2) =
  admit ()

let rec prefix_of (#a: Type) (l1 l2: list a)
: Tot Type0 (decreases l2)
= match l1, l2 with
  | [], [] -> True
  | [], _ -> True
  | _, [] -> False
  | h1 :: t1, h2 :: t2 -> h1 == h2 /\ t1 `prefix_of` t2

let rec prefix_of_length (l1 l2: trace)
: Lemma
  (requires (prefix_of l1 l2))
  (ensures (List.length l1 <= List.length l2))
  (decreases l1)
= match l1, l2 with
  | h1 :: t1, h2 :: t2 ->
    prefix_of_length t1 t2
  | _ -> ()

// let x (h h':trace) :
//   Lemma (requires (prefix_of h h'))
//     (ensures (
//       prefix_of_length h h';
//       let n : nat = (List.length h') - (List.length h) in
//       let (lt, _) = List.Tot.Base.splitAt n h' in
//       h == lt @ h')) =
//   ()

let extract_local_trace (h:trace) (pi:monitorable_prop) :
  IIO trace pi
    (requires (fun h' -> suffix_of h h'))
    (ensures (fun h' r lt ->
      lt == [] /\
      Inl? r /\
      h' == (apply_changes h (Inl?.v r))))
  =
  let h' = get_trace () in
  suffix_of_length h h';
  let n : nat = (List.length h') - (List.length h) in
  let (lt, ht) = List.Tot.Base.splitAt n h' in
  assume (lt @ ht == h');
  assume (ht == h);
  List.Tot.Properties.rev_involutive lt;
  assert (h' == apply_changes h (List.rev lt));
  List.rev lt

let suffix_of_append () :
  Lemma (forall h l1 l2. suffix_of h ((List.rev l1) @ (List.rev l2) @ h)) =
  admit()

val rev_nil : unit -> Lemma (List.rev #event [] == [])
let rev_nil () = ()


val append_rev: l1:trace -> l2:trace ->
  Lemma (((List.Tot.Base.rev l1)@(List.Tot.Base.rev l2)) == (List.Tot.Base.rev (l2@l1)))
let append_rev l1 l2 = List.rev_append l2 l1


let fnc
  (#t1:Type) {| d1:exportable t1 |}
  (#t2:Type) {| d2:importable t2 |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r}))
  {| d4:checkable4 post |}
  (x:t1)
  (h:trace)
  (r:t2)
  (lt:trace) :
  IIOwp t2 (fun _ p ->
    let b = check4 #t1 #trace #(maybe t2) #trace #post x h (Inl r) lt in
    (b ==>  p (Inl r) []) /\
    (~b ==> p  (Inr Contract_failure) [])) =
  (if check4 #t1 #trace #(maybe t2) #trace #post x h (Inl r) lt
  then r
  else IIO.Effect.throw #t2 Contract_failure)

val append_inv_tail:
  #t1:Type ->
  #t2:Type ->
  x:t1 ->
  h:trace ->
  r:t2 ->
  post:(t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) ->
  {| d4:checkable4 post |} ->
  rlt:(maybe trace){Inl? rlt} ->
  lt1:trace ->
  lt2:trace ->
  Lemma
   (requires (
      (List.rev lt1 @ List.rev lt2 @ h) == (List.rev (Inl?.v rlt) @ h)
      /\ check4 #t1 #trace #(maybe t2) #trace #post x h (Inl r) (Inl?.v rlt)
   ))
   (ensures (post x h (Inl r) (lt1 @ lt2)))
let append_inv_tail x h r lt1 lt2 post rlt = admit()

// val append_inv_tail: l:trace -> l1:trace -> l2:trace -> l3:(maybe trace){Inl? l3} ->
//   Lemma
//       (((List.rev l1 @ List.rev l2 @ l) == (List.rev (Inl?.v l3) @ l))
//       ==>
//       ((Inl?.v l3) == l2@l1))
// let rec append_inv_tail l l1 l2 l3 = admit()

// TODO: fix admit here. this enforces the post condition of IIO *)
let _import_IIO
  (#t1:Type) {| d1:exportable t1 |}
  (#t2:Type) {| d2:importable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r}))
  {| d4:checkable4 post |}
  (f : (d1.etype -> MIIO d2.itype))
  (x:t1) :
  IIO t2 pi (pre x) (post x) by (
    ignore (pose_lemma (`(suffix_of_append ())));
    ignore (pose_lemma (`(rev_append_rev_append ())));
    norm [delta_only [`%pure_null_wp;`%pure_assume_wp;`%pure_bind_wp]];
    norm [delta_only [`%iio_post;`%apply_changes]];
    ExtraTactics.blowup ();
    bump_nth 6;
    ExtraTactics.branch_on (ExtraTactics.get_binder 22);
    (* Branch 2: Inr *) bump_nth 2; smt ();
    (* Branch 1: Inl *)
      // l_to_r [`List.append_assoc; `append_rev];
      ExtraTactics.blowup (); (* 2 new goals *)
      smt (); smt ();

      ExtraTactics.branch_on (ExtraTactics.get_binder 27);
      (* Branch 1.2: Inr *) bump_nth 2; smt ();
      (* Branch 1.1: Inl *)
        let wp = ExtraTactics.get_binder 15 in
        let x3 = ExtraTactics.get_binder 19 in
        let x5 = ExtraTactics.get_binder 23 in
        let av = ExtraTactics.get_binder 25 in

        ExtraTactics.blowup (); (* 4 new goals *)
        l_to_r [`rev_nil; `List.append_l_nil; `List.append_nil_l];
        let wp' = ExtraTactics.instantiate_multiple_foralls wp [(`(Inl (`#av))); (`((`#x3)@(`#x5)))] in
        mapply wp';
        split ();
        smt ();
        (** this one is easy. should get out that av == x'3@x'5 **)

        let eq = ExtraTactics.get_binder 30 in
        let x0 = ExtraTactics.get_binder 13 in
        let x6 = ExtraTactics.get_binder 27 in
        ExtraTactics.branch_on x6;
        // apply_lemma (`append_inv_tail);
        // let breq = ExtraTactics.get_binder 34 in
        // let lem = pose_lemma (`(Classical.forall_intro_4 append_inv_tail)) in
        // let lem' = ExtraTactics.instantiate_multiple_foralls lem [
        //   binder_to_term x0;
        //   binder_to_term x5;
        //   binder_to_term x3;
        //   binder_to_term x6
        // ] in
        // clear lem;
        // mapply lem';
        dump "x";
        later ();
        tadmit ()

        // l_to_r [`rev_nil; `List.append_l_nil; `List.append_nil_l];
        // let wp' = ExtraTactics.instantiate_multiple_foralls wp [(`(Inr Contract_failure)); (`((`#x3)@(`#x5)))] in
        // mapply wp';
        // split ();
        // smt ();

        (** this one should be easy. post is refined to accept any
        Inr therefore it is weird that F* does not accept this **)
  )=
  (** The post condition should allow the computation to fail.
  The computation can fail by itself or because it does not
  respect the contracts. It is not reasonable to assume the
  computation handles by itself all errors, therefore the
  context that imported this function should expeect errors. **)
  let h : trace = get_trace () in
  let f' = _import_pre_pi_IIO pi pre f in
  let r : t2 = f' x in
  let lt : trace = extract_local_trace h pi in
  Classical.forall_intro_2 (Classical.move_requires_2 (append_inv_tail #t1 #t2 x h r post #d4 (Inl lt)));
  fnc #t1 #d1 #t2 #d2 post #d4 x h r lt

instance importable_MIO_pi_IIO
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) {| d4:checkable4 post |} :
  Tot (safe_importable (pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_safe_importable
    (d1.etype -> MIO d2.itype)
    #(pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))
    (fun (f:(d1.etype -> MIO d2.itype)) ->
      (fun pi -> _import_IIO pi pre post f))

instance importable_MIO_IIO
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) {| d4:checkable4 post |} :
  Tot (safe_importable (x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_safe_importable
    (d1.etype -> MIO d2.itype)
    #(x:t1 -> IIO t2 pi (pre x) (post x))
    (_import_IIO pi pre post #d4)

instance importable_MIIO_pi_IIO
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) {| d4:checkable4 post |} :
  Tot (safe_importable (pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_safe_importable
    (d1.etype -> MIIO d2.itype)
    #(pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))
    (fun (f:(d1.etype -> MIIO d2.itype)) ->
        (fun pi -> _import_IIO pi pre post f))

instance importable_MIIO_IIO
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) {| d4:checkable4 post |} :
  Tot (safe_importable (x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_safe_importable
    (d1.etype -> MIIO d2.itype)
    #(x:t1 -> IIO t2 pi (pre x) (post x))
    (_import_IIO pi pre post #d4)
