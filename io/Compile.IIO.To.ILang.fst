module Compile.IIO.To.ILang

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open IO.Sig
open Compiler.Languages
open TC.Checkable

class exportable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  etype : Type u#b;
  [@@@no_method]
  c_etype : ilang etype pi;
  [@@@no_method]
  export : typ_posts fl rcs -> t -> etype;
}

class safe_importable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  sitype : Type u#b;
  [@@@no_method]
  c_sitype : ilang sitype pi;
  [@@@no_method]
  safe_import : sitype -> (typ_posts fl rcs -> t); 
}


class importable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  itype : Type u#b; 
  [@@@no_method]
  c_itype : ilang itype pi;
  [@@@no_method]
  import : itype -> (typ_posts fl rcs -> resexn t);
}

(** *** Exportable instances **)

instance ilang_is_exportable (#pi:monitorable_prop) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) t {| d1: ilang t pi |} : exportable t pi rcs fl = {
  etype = t;
  c_etype = d1;
  export = (fun Leaf x -> x)
}

instance exportable_unit (#pi:monitorable_prop) (#fl:erased tflag) : exportable unit pi Leaf fl = {
  etype = unit;
  c_etype = ilang_unit pi;
  export = (fun Leaf () -> ())
}

instance exportable_file_descr (#pi:monitorable_prop) (#fl:erased tflag) : exportable file_descr pi Leaf fl = {
  etype = file_descr;
  c_etype = ilang_file_descr pi;
  export = (fun Leaf fd -> fd)
}

instance exportable_refinement (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag) t {| d:exportable t pi rcs fl |} (p : t -> Type0) : exportable (x:t{p x}) pi rcs fl = {
  etype = d.etype;
  c_etype = d.c_etype;
  export = d.export
}

instance exportable_option
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi rcs fl |} :
  Tot (exportable (option t1) pi rcs fl) = {
  etype = option d1.etype;
  c_etype = ilang_option pi d1.etype #d1.c_etype;
  export = (fun eff_rcs x -> match x with | Some x' -> Some (d1.export eff_rcs x') | None -> None)
}


instance exportable_pair
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (eleft rcs) fl |} t2 {| d2:exportable t2 pi (eright rcs) fl |} :
  Tot (exportable (t1 * t2) pi rcs fl) = {
  etype = d1.etype * d2.etype;
  c_etype = ilang_pair pi d1.etype #d1.c_etype d2.etype #d2.c_etype;
  export = (fun eff_rcs (x, y) -> (d1.export (eleft eff_rcs) x, d2.export (eright eff_rcs) y));
}

instance exportable_either
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (eleft rcs) fl |} t2 {| d2:exportable t2 pi (eright rcs) fl |} :
  Tot (exportable (either t1 t2) pi rcs fl) = {
  etype = either d1.etype d2.etype;
  c_etype = ilang_either pi d1.etype #d1.c_etype d2.etype #d2.c_etype;
  export = (fun eff_rcs x -> 
      match x with | Inl x -> Inl (d1.export (eleft eff_rcs) x) | Inr x -> Inr (d2.export (eright eff_rcs) x))
}

instance ilang_resexn (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} : ilang (resexn t1) pi = { mldummy = () }

(** *** Exportable arrows **)

instance exportable_arrow_with_no_pre_and_no_post
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:importable t1 pi (eleft rcs) fl |}
  (t2:Type) {| d2:exportable t2 pi (eright rcs) fl|} :
  exportable (t1 -> IIOpi (resexn t2) fl pi) pi rcs fl = {
    etype = d1.itype -> IIOpi (resexn d2.etype) fl pi;
    c_etype = ilang_arrow pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(t1 -> IIOpi (resexn t2) fl pi)) (x:d1.itype) ->
      match d1.import x (eleft eff_rcs) with
      | Inl x' -> begin
        match f x' with 
        | Inl x'' -> Inl (d2.export (eright eff_rcs) x'') 
        | Inr err -> Inr err
      end
      | Inr err -> Inr err
    )
  }

(** This is a design choice for making proofs easier. One can remove the post-condition **)
instance exportable_arrow_with_post
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:importable t1 pi (eleft rcs) fl |}
  t2 {| d2:exportable t2 pi (eright rcs) fl |}
  (post : t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0)) 
  (#c1 : squash (forall x h lt r. post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x)) pi rcs fl = {
    etype = x:d1.itype -> IIOpi (resexn d2.etype) fl pi;
    c_etype = ilang_arrow #fl pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x))) ->
      let f' : t1 -> IIOpi (resexn t2) fl pi = f in
      (exportable_arrow_with_no_pre_and_no_post t1 #d1 t2 #d2).export eff_rcs f');
  }

let trivialize_new_post_resexn
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> resexn 'b -> trace -> Type0) :
  Tot ('a -> trace -> resexn 'b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x h ==> post x h r lt) 

let lemma_trivialize_new_post_monitorable
  #t1
  #t2
  (pre:t1 -> trace -> bool)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0) 
  pi
  (x:squash (forall (x:t1) (h lt:trace) r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)) :
  squash (forall x h lt r. (trivialize_new_post_resexn pre post) x h r lt ==> enforced_locally pi h lt) = 
  ()

let enforce_pre
  #t1 #t2
  (#fl:erased tflag)
  (pre : t1 -> trace -> Type0)
  (rc : t1 -> trace -> unit -> trace -> bool)
  (eff_rc : eff_rc_typ fl t1 unit rc) 
  (post : t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0)) 
  (#c_pre : squash (forall h x. rc x h () [] ==> pre x h))
  (f:(x:t1 -> IIO (resexn t2) fl (pre x) (post x)))
  (x:t1) :
  IIO (resexn t2) fl (fun _ -> True) (trivialize_new_post_resexn (fun x h -> rc x h () []) post x) =
  let (| h, eff_rc' |) : (initial_h:(erased trace) & eff_rc_typ_cont fl t1 unit rc x initial_h) = eff_rc x in
  let (lt, b) = eff_rc' () in
  assume (reveal lt == []);
  assert (b ==> rc x h () lt);
  if b then f x 
  else Inr Contract_failure

let fast_convert_0 (a b c d:Type) (rc:rc_typ a b) : Pure (rc_typ c d) (requires (a == c /\ b == d)) (ensures (fun _ -> True)) = rc

assume val fast_convert : (#fl:erased tflag) -> (#a:Type u#a) -> (#b:Type u#b) -> (c:Type{c == a}) -> (d:Type{d == b}) -> (rc:rc_typ a b) -> (t : eff_rc_typ fl a b rc) -> (eff_rc_typ fl c d (fast_convert_0 a b c d rc))
  
instance exportable_arrow_pre_post
  (t1:Type) (t2:Type)
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ Mkdtuple3?._1 (root rcs) == t1 /\ (Mkdtuple3?._2 (root rcs) == unit)})
  (#fl:erased tflag)
  {| d1:importable t1 pi (left rcs) fl |}
  {| d2:exportable t2 pi (right rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0)) 
  (#c_pre : squash (forall h x. (Mkdtuple3?._3 (root rcs)) x h () [] ==> pre x h))
  (#c1 : squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
    etype = d1.itype -> IIOpi (resexn d2.etype) fl pi; 
    c_etype = ilang_arrow pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (pre x) (post x))) ->
      assert (root rcs == root (map_tree eff_rcs dfst));
      let (| pck_rc, eff_rc |) = root eff_rcs in
      let rc = Mkdtuple3?._3 pck_rc in
      let eff_rc : eff_rc_typ fl t1 unit (Mkdtuple3?._3 pck_rc) = fast_convert t1 unit _ eff_rc in
      let f' = enforce_pre pre rc eff_rc post f in
      let rc_pre = (fun x h -> rc x h () []) in
      let new_post = trivialize_new_post_resexn rc_pre post in
      let rcs' = (EmptyNode (left rcs) (right rcs)) in
      let d = (exportable_arrow_with_post #_ #rcs' t1 #d1 t2 #d2 new_post #(lemma_trivialize_new_post_monitorable rc_pre post pi c1)) in
      d.export (EmptyNode (left eff_rcs) (right eff_rcs)) f'
    )
}

    
(** *** Safe importable instances **)
let ilang_is_safely_importable (#pi:monitorable_prop) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) #t (d:ilang t pi) : safe_importable t pi rcs fl = {
  sitype = t;
  c_sitype = d;
  safe_import = (fun x Leaf -> x); 
}

instance importable_unit (#pi:monitorable_prop) (#fl:erased tflag) : importable unit pi Leaf fl = {
  itype = unit;
  c_itype = ilang_unit pi;
  import = (fun () Leaf -> Inl ())
}

instance importable_file_descr (#pi:monitorable_prop) (#fl:erased tflag) : importable file_descr pi Leaf fl = {
  itype = file_descr;
  c_itype = ilang_file_descr pi;
  import = (fun fd Leaf -> Inl fd)
}

(** *** Importable instances **)

instance safe_importable_is_importable (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag) #t (d:safe_importable t pi rcs fl) : importable t pi rcs fl = {
  itype = d.sitype;
  c_itype = d.c_sitype;
  import = (fun x eff_rcs -> Inl (d.safe_import x eff_rcs))
}

instance importable_refinement
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |}
  (rp : t -> Type0) {| checkable rp |} :
  Tot (importable (x:t{rp x}) pi rcs fl) = {
  itype = d.itype;
  c_itype = d.c_itype;
  import = (fun (x:d.itype) eff_rcs ->
    (match d.import x eff_rcs with
    | Inl x ->
      if check #t #rp x then Inl x 
      else Inr Contract_failure
    | Inr err -> Inr err) <: resexn (x:t{rp x}))
}
    
instance importable_option
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |} :
  Tot (importable (option t) pi rcs fl) = {
  itype = option d.itype;
  c_itype = ilang_option pi d.itype #d.c_itype;
  import = (fun (x:option d.itype) eff_rcs ->
    match x with
    | Some x' -> begin
      match d.import x' eff_rcs with
      | Inl x'' -> Inl (Some x'')
      | Inr err -> Inr err
    end
    | None -> Inr Contract_failure)
}

instance importable_pair
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |} :
  Tot (importable (t1 * t2) pi rcs fl) = {
  itype = d1.itype * d2.itype;
  c_itype = ilang_pair pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun (x,y) eff_rcs ->
      match (d1.import x (eleft eff_rcs), d2.import y (eright eff_rcs)) with
      | (Inl x, Inl y) -> Inl (x, y)
      | _ -> Inr Contract_failure)
}

instance importable_either
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |} :
  Tot (importable (either t1 t2) pi rcs fl) = {
  itype = either d1.itype d2.itype;
  c_itype = ilang_either pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun x eff_rcs ->
      match x with
      | Inl x' -> begin
        match d1.import x' (eleft eff_rcs) with
        | Inl x'' -> Inl (Inl x'')
        | Inr err -> Inr err
      end
      | Inr y -> begin
        match d2.import y (eright eff_rcs) with
        | Inl y' -> Inl (Inr y')
        | Inr err -> Inr err
      end)
}

instance importable_dpair_refined
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |}
  {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y}) pi rcs fl) = {
  itype = d1.itype & d2.itype;
  c_itype = ilang_pair pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun ((x', y')) eff_rcs ->
      match (d1.import x' (eleft eff_rcs), d2.import y' (eright eff_rcs)) with
       | (Inl x, Inl y) ->
            if check2 #t1 #t2 #p x y then Inl ((| x, y |) <: (x:t1 & y:t2{p x y})) else Inr Contract_failure
       | _ -> Inr Contract_failure)
}

(** *** Safe importable arrows **)
instance safe_importable_resexn
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:importable t1 pi rcs fl |} :
  Tot (safe_importable (resexn t1) pi rcs fl) = {
  sitype = resexn d1.itype;
  c_sitype = ilang_resexn pi d1.itype #d1.c_itype;
  safe_import = (fun x eff_rcs ->
      match x with
      | Inl x' -> d1.import x' eff_rcs 
      | Inr y -> Inr y)
}
    
instance safe_importable_arrow
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:exportable t1 pi (eleft rcs) fl |}
  (t2:Type) {| d2:importable t2 pi (eright rcs) fl |} : 
  safe_importable ((x:t1) -> IIOpi (resexn t2) fl pi) pi rcs fl = {
  sitype = d1.etype -> IIOpi (resexn d2.itype) fl pi;
  c_sitype = ilang_arrow pi d1.c_etype (ilang_resexn pi d2.itype #d2.c_itype);
  safe_import = (fun (f:d1.etype -> IIOpi (resexn d2.itype) fl pi) eff_rcs (x:t1) -> 
    (let x' = d1.export (eleft eff_rcs) x in 
     let y : resexn d2.itype = f x' in
     (safe_importable_resexn t2 #d2).safe_import y (eright eff_rcs)) <: IIOpi (resexn t2) fl pi)
}

#set-options "--split_queries"
let enforce_post
  (#t1 #t2:Type)
  (#fl:erased tflag)
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0{r == Inr Contract_failure ==> b}))
  (rc : t1 -> trace -> resexn t2 -> trace -> bool)
  (eff_rc : eff_rc_typ fl t1 (resexn t2) rc) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt)))
  (c2post : squash (forall x h r lt. pre x h /\ (rc x h r lt) ==> post x h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) =
  let (| h, eff_rc' |) = eff_rc x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  let (lt, b) = eff_rc' r in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if b then r
  else (assert (post x h (Inr Contract_failure) lt); Inr Contract_failure)

instance safe_importable_arrow_pre_post
  (t1:Type) (t2:Type)
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ (Mkdtuple3?._1 (root rcs) == t1 /\ (Mkdtuple3?._2 (root rcs) == (resexn t2))) })
  (#fl:erased tflag)
  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (** it must be `resexn t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0{r == Inr Contract_failure ==> b})) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt)))
  (c2post: squash (forall x h r lt. pre x h /\ ((Mkdtuple3?._3 (root rcs)) x h r lt) ==> post x h r lt)) :
  safe_importable ((x:t1) -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
  sitype = d1.etype -> IIOpi (resexn d2.itype) fl pi;
  c_sitype = ilang_arrow pi d1.c_etype (ilang_resexn pi d2.itype #d2.c_itype);
  safe_import = (fun (f:(d1.etype -> IIOpi (resexn d2.itype) fl pi)) eff_rcs ->
    let rcs' = (EmptyNode (left rcs) (right rcs)) in
    let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
    let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
    let (| rc_pck, eff_rc |) = root eff_rcs in
    enforce_post pi pre post (Mkdtuple3?._3 rc_pck) (fast_convert t1 (resexn t2) _ eff_rc) c1post c2post f')
}
