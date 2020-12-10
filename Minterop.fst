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
lift: IO -> IIO (Done)
export: IIO -> MIIO (Done: _export_IIO)

possible: IO -> MIIO (lift automatically to IIO, and then use export: IIO -> MIIO)
possible: MIO -> MIIO (the lift from IO to IIO should work automatically)

import: MIIO -> IIO (Done: _import_IIO)
possible: MIO -> IIO (lift from MIO to MIIO, and then import to IIO)

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
instance ml_monitorable_prop : ml monitorable_prop = { mldummy = () }



(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
// - the types of values we can safely `import` from malicious MIO code
// - the types of values we can safely `export` to malicious MIO code
// This interoperability model includes extraction as well as
// adding extra checking and wrapping.
// *)

exception Contract_failure
class exportable (t : Type) = { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; import : itype -> option t; ml_itype : ml itype }
class exn_importable (t : Type) = { eitype : Type; exn_import : eitype -> MIO t; ml_eitype : ml eitype }

let mk_exportable (#t1 t2 : Type) {| ml t2 |} (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) {| ml t1 |} (imp : t1 -> option t2) : importable t2 =
  { itype = t1; import = imp; ml_itype = solve }
let mk_exn_importable (t1 #t2 : Type) {| ml t1 |} (imp : t1 -> MIO t2) : exn_importable t2 =
  { eitype = t1; exn_import = imp; ml_eitype = solve }

instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) = d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance exportable_ml t {| ml t |} : exportable t = mk_exportable t (fun x -> x)
instance importable_ml t {| ml t |} : importable t = mk_importable t (fun x -> Some x)

instance exn_importable_importable t {| d:importable t |} : exn_importable t =
  mk_exn_importable d.itype (fun x -> 
    (match import x with
    | Some x -> x
    | None -> IO.Effect.throw Contract_failure) <: MIO t)

instance exportable_refinement t {| d:exportable t |} (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) export

class checkable (#t:Type) (p : t -> Type0) = { check : (x:t -> b:bool{b ==> p x}) }
instance general_is_checkeable t (p : t -> bool) : checkable (fun x -> p x) = { check = fun x -> p x }
class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkeable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}
  
class checkable4 (#t1 #t2:Type) (p : t1 -> trace -> maybe (t2) -> trace -> Type0) = { check4 : (x1:t1 -> s0:trace -> r:maybe (t2) -> lt:trace -> b:bool{b ==> p x1 s0 r lt}) }
instance general_is_checkeable4 t1 t2 (p : t1 -> trace -> maybe (trace * t2) -> trace -> bool) : checkable4 (fun x1 x2 x3 x4 -> p x1 x2 x3 x4) = { check4 = fun x1 x2 x3 x4 -> p x1 x2 x3 x4}

instance importable_refinement 
  t {| d:importable t |} 
  (rp : t -> Type0) {| checkable rp |} : 
    importable (x:t{rp x}) = 
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
    (fun (f:(t1 -> MIO t2)) -> (fun (x:d1.itype) -> export (f (exn_import x)) <: MIO d2.etype))

// An untyped term in a typed context
instance importable_mlarrow t1 t2 {| d1:exportable t1 |} {| d2:importable t2 |} : importable (t1 -> MIO t2)  =
  mk_importable (d1.etype -> MIO d2.itype)
    (fun (f:(d1.etype -> MIO d2.itype)) -> 
      Some (fun (x:t1) -> exn_import (f (export x)) <: MIO t2))
  
// Example trueish
let trueish (x:int{x >= 0}) : bool = true
let trueish' (x:int) : MIO bool = (trueish (exn_import x))
let trueish'' : int -> MIO bool = export trueish

instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  {| d1:ml t1 |} {| d2:ml t2 |} {| d3:checkable2 p |} : importable (x:t1 -> MIO (y:t2{p x y})) =
  mk_importable (t1 -> MIO t2) #(x:t1 -> MIO (y:t2{p x y}))
    (fun (f:(t1 -> MIO t2)) -> 
      let f':(x:t1 -> MIO (y:t2{p x y})) = (fun (x:t1) -> 
        let y : t2 = f x in
        (if check2 #t1 #t2 #p x y then y 
         else IO.Effect.throw Contract_failure) <: MIO (y:t2{p x y})) in Some f')

// Example incr

let incr (x:int) : int = x + 1

let incr2 : int -> MIO int = incr

let p x y : bool = (y = x + 1)
let incr'' (x:int) : MIO (y:int{p x y}) = exn_import (incr x)

// TODO: fix this. see https://github.com/FStarLang/FStar/issues/2128
// val incr' : unit -> MIO ((x:int) -> MIO (y:int{p x y}))
// let incr' () = 
//   let (z:(x:int) -> MIO (y:int{p x y})) = import incr2 in
//   z

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
        if check2 #t1 #trace #pre x h then
          if enforced_globally pi h then
            export (f x)
          else IIO.Effect.throw Contract_failure
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
  (#t2:Type)
  (tree : io (t2)) 
  (pi:monitorable_prop) : 
  IIO t2 pi (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> r 
  | Throw r -> IIO.Effect.throw r
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = IIO.Effect.dynamic_cmd pi cmd argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : io t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      _import_pi_IIO z' pi

let _import_pre_pi_IIO 
  (#t1:Type)
  (#t2:Type)
  (tree : io (t2)) 
  (pi:monitorable_prop) 
  (pre:t1 -> trace -> Type0) {| checkable2 pre |} : 
  Tot (x:t1 -> IIO t2 pi (pre x) (fun _ _ _ -> True)) =
  (fun x ->
    let h = get_trace () in
    if check2 #t1 #trace #pre x h then
      _import_pi_IIO tree pi 
    else IIO.Effect.throw Contract_failure)


let extract_local_trace (s0 s1:trace) :
  Pure trace
    (requires (exists lt. s1 == apply_changes s0 lt))
    (ensures (fun lt -> s1 == apply_changes s0 lt)) = 
  admit ();
  assert (List.length s1 >= List.length s0);
  let n : nat = (List.length s1) - (List.length s0) in
  let (lt, _) = List.Tot.Base.splitAt n s1 in
  List.rev lt

// TODO: fix admit here. this enforces the post condition of IIO *)
let _import_IIO_0
  (#t1:Type)
  (#t2:Type)
  (tree : io (t2)) 
  (pi:monitorable_prop) 
  (pre:t1 -> trace -> Type0) {| checkable2 pre |} 
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) {| checkable4 post |} : 
  Tot (x:t1 -> IIO t2 pi (pre x) (post x)) =
  (fun x ->
    admit ();
    let h = get_trace () in
    let f = _import_pre_pi_IIO tree pi pre in
    let r : t2 = f x in
    let h' = get_trace () in
    let lt = extract_local_trace h h' in
    if check4 #t1 #t2 #post x h (Inl r) lt then (
      assert (post x h (Inl r) lt);
      r
    ) else IIO.Effect.throw Contract_failure)
  
let _import_IIO
  (#t1:Type) {| d1:exportable t1 |} 
  (#t2:Type) {| d2:importable t2 |}
  (tree : io (t2)) 
  (pi:monitorable_prop) 
  (pre:t1 -> trace -> Type0) {| checkable2 pre |} 
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) {| checkable4 post |} : 
  Tot (x:t1 -> IIO t2 pi (pre x) (post x)) =
    (fun (x:t1) -> 
    let x' : d1.etype = export x in
    let f : d1.etype -> IIO d2.itype pi (pre x) (post x) = 
      _import_IIO_0 tree pi pre post in
    let r : d2.itype = f x' in
    import r)

instance importable_IIO 
  (t1:Type) {| d1:exportable t1 |} 
  (t2:Type) {| d2:ml t2 |}
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) {| d4:checkable4 post |} :
  Tot (importable (pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))) =
  mk_importable 
    (d1.etype -> MIO t2) 
    #(pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x))
    (fun (f:(d1.etype -> MIO t2)) ->
      let f' : (pi:monitorable_prop -> x:t1 -> IIO t2 pi (pre x) (post x)) =
        (fun (pi:monitorable_prop) (x:t1) ->
          let x' : d1.etype = export x in
          let h = get_trace () in
          (** TODO: This seems weird. 
            Why do I pass my post condition (fun _ -> True)?
            Guido recommended me to do this, but I don't remember why
            should this be safe. **)
          let tree : io t2 = (* MIO?.*)reify (f x') h (fun _ r -> True) in
          _import_IIO tree pi pre post x <: IIO t2 pi (pre x) (post x))
      in Some f')


instance importable_MIO_to_IIO 
  t1 {| d1:exportable t1 |} 
  t2 {| d2:ml t2 |} 
  (pi:monitorable_prop) :
  Tot (importable (t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True))) =
  mk_importable (d1.etype -> MIO t2) #(t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True))
    (fun (f:(d1.etype -> MIO t2)) ->
      let f' : (t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True)) = (
        fun (x:t1) ->
            let x : d1.etype = export x in
            let h = get_trace () in
            let tree = reify (f x) h (fun _ r -> True) in
            _import_MIO_to_IIO #t2 tree pi <: IIO t2 pi (fun _ -> True) (fun _ _ _ -> True)) 
      in Some f')


val allowed_file : string -> bool
let allowed_file fnm = match fnm with
  | "../Makefile" -> false
  | "Demos.fst" -> true
  | _ -> false

val allowed_fd : file_descr -> trace -> bool
let rec allowed_fd fd s0 =
  match s0 with
  | [] -> false
  | EOpenfile fnm (Inl fd') :: t -> if fd = fd' then allowed_file(fnm)
                                  else allowed_fd fd t
  | EClose fd' _  :: t -> if fd = fd' then false else allowed_fd fd t
  | _ :: t -> allowed_fd fd t

let pi : monitorable_prop = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> allowed_file(fnm)
  | (| Read, fd |) -> allowed_fd fd s0
  | (| Close, fd |) -> allowed_fd fd s0)

// the plugin will be written in GIO (should be ML?)
let plugin_type = (pi:monitorable_prop) -> file_descr -> IIO unit pi (fun _ -> True) (fun _ _ _ -> True)

// import plugin_type 
let webserver (plugin:plugin_type) : IIO unit pi (fun _ -> True) (fun _ _ _ -> True) =
  rev_append_rev_append ();
  let fd = static_cmd pi Openfile "Demos.fst" in
  plugin pi fd

let m4_cmd (cmd:io_cmds) (argz: args cmd) : MIO (res cmd) = 
  MIO?.reflect (fun _ _ -> io_call cmd argz)

let plugin1 : file_descr -> MIO unit = fun fd ->
  m4_cmd Close fd

// val plugin1_g : unit -> MIO ((pi:monitorable_prop) -> file_descr -> GIO unit pi)
// let plugin1_g () = exn_import plugin1

// let sdx () : GIO unit pi = 
//   webserver (plugin1_g)

// let plugin2 : file_descr -> MIO unit = fun fd ->
//   let fd = m4_cmd Openfile "../Makefile" in
//   m4_cmd Close fd;
//   let msg = m4_cmd Read fd in ()


// val plugin2_g : (pi:monitorable_prop) -> file_descr -> GIO unit pi 
// let plugin2_g = import plugin2
  
// let sdz () : GIO unit pi = 
//   webserver (plugin2_g)

// TODO : try to import from MIO to IOStHist and dynamically enforce the
// post condition

// this can not have a precondition because you can not dynamically
// check it and still return in IOStHist pre if it fails. also it does
// not make sense to have a precondition for a computation

// the post has to accept as a result any errors, espicially 
// Contract_failure

// let extract_local_events (s0 s1:trace) :
//   Pure trace
//     (requires (exists le. s1 == apply_changes s0 le))
//     (ensures (fun le -> s1 == apply_changes s0 le)) = 
//   admit ();
//   assert (List.length s1 >= List.length s0);
//   let n : nat = (List.length s1) - (List.length s0) in
//   let (le, _) = List.Tot.Base.splitAt n s1 in
//   List.rev le


// let _import_MIO4_to_GIO
//   (t1:Type) {| d1:exportable t1 |}
//   (t2:Type) {| d2:ml t2 |}
//   (f:(d1.etype -> MIO t2))
//   (pi:monitorable_prop) :
//   Tot (t1 -> GIO t2 pi) = admit ()

// let someother
//   (t1:Type) {| d1:exportable t1 |}
//   (t2:Type) {| d2:ml t2 |}
//   (post : t1 -> trace -> maybe (trace * t2) -> trace -> Type0) 
//   (_:squash (forall x err s0 le. post x s0 (Inr err) le == true))
//   {| d3:checkable4 post |}
//   (f:(d1.etype -> MIO t2))
//   (pi:monitorable_prop)
//   (x:t1) :
//   IOStHist t2
//     (gio_pre pi)
//     (fun h res le -> gio_post pi h res le /\ post x h res le) 
//   by (
//     explode ();
//     bump_nth 23;
//     let zz = get_binder 13 in 
//     focus (fun () ->
//       let _ = t_destruct zz in
//       iterAll (fun () ->
//         let bs = repeat intro in
//         let b = last bs in (* this one is the equality *)
//         rewrite_eqs_from_context ();
//         norm [iota];
//         ())
//     );
//     let aq = get_binder 16 in
//     focus (fun () -> 
//       let _ = t_destruct aq in
//       let bs1 = intro () in
//       let br = intro () in
//       let b = intro () in (* this one is the equality *)
//       rewrite_eqs_from_context ();
//       norm [iota];
//       let goal = match (List.Tot.Base.nth (goals ()) 0) with
//       | Some z -> z | None -> fail "Asd" in
//       let _ = inspect (goal) in
//       ()
//     );
//     dump "h"
//   ) =
//   // rev_append_rev_append ();
//   // assume (forall x err s0 le. post x s0 (Inr err) le == true);
//   let (f':t1 -> GIO t2 pi) = _import_MIO4_to_GIO t1 t2 f pi in
//   let s0 : trace = IOStHist.get () in
//   let result : t2 = f' x in
//   let s1 : trace = IOStHist.get () in
//   let le = extract_local_events s0 s1 in

//   // // the casting is done wrongly because you don't have an extra le...
//   // // in a way this is not correct because it uses the materialized le ^ and the ghost le
//   // // without realizing that are the same thing.
//   if check4 #t1 #t2 #post #d3 x s0 (Inl (s1, result)) le then (
//     assert (post x s0 (Inl (s1, result)) le);
//     result
//   ) else (
//     IOStHist.throw Contract_failure
//   )
  


// instance importable_MIO_to_IOStHist 
//   (t1:Type) {| d1:exportable t1 |}
//   (t2:Type) {| d2:ml t2 |}
//   (post : t1 -> trace -> maybe (trace * t2) -> trace -> Type0) 
//   {| checkable4 post |} :
//   Tot (importable (x:t1 -> IOStHistwp t2 (fun s0 p -> forall res le. post x s0 res le ==>  p res le))) =
//   mk_importable 
//     (d1.etype -> MIO t2) 
//     #(x:t1 -> IOStHistwp t2 (fun s0 p -> forall restl le. post x s0 restl le ==>  p restl le)) 
//     (fun (f:(d1.etype -> MIO t2)) -> Some (someother t1 t2 post f))



