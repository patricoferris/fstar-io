module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription

(** Similar to strict_prefix_of, but the opposite.

    I believe the names should be swapped but well...
*)
let rec strict_suffix_of #a (s l : list a) :
  Pure Type0 (requires True) (ensures fun _ -> True) (decreases l)
= match l with
  | [] -> False
  | x :: l ->
    match s with
    | [] -> True
    | y :: s -> x == y /\ s `strict_suffix_of` l

let rec strict_suffix_or_eq_append #a (s l : list a) :
  Lemma
    (ensures l == [] \/ s `strict_suffix_of` (s @ l))
    (decreases s)
= match s with
  | [] -> ()
  | y :: s -> strict_suffix_or_eq_append s l

let rec strict_suffix_length #a (s l : list a) :
  Lemma (ensures s `strict_suffix_of` l ==> length s <= length l) (decreases l)
= match l with
  | [] -> ()
  | x :: l ->
    match s with
    | [] -> ()
    | y :: s -> strict_suffix_length s l

(** Encoding of interaction trees, specialised to a free monad

   The idea is to bypass the absence of coinductive datatypes in F* by instead
   doing something similar to how one would encode the type [stream A] as
   functions [nat -> A].
   Here we define itrees as functions from positions (or paths in the tree) to
   nodes which contain a label corresponding to either [Ret] for return, [Tau]
   for delays, and [Call] for the monadic operations.

*)

noeq
type op_sig (op : Type) = {
  args : op -> eqtype ;
  res : op -> eqtype
}

type ichoice (op : Type) (s : op_sig op) =
| Tau_choice : ichoice op s
| Call_choice : o:op -> s.args o -> s.res o -> ichoice op s

(** Type of positions as sequences of choices in the tree *)
type ipos op s = list (ichoice op s)

(** Nodes of an itree *)
type inode op (s : op_sig op) (a:Type) =
| Ret : a -> inode op s a
| Call : o:op -> s.args o -> inode op s a
| Tau : inode op s a

(** A *raw* itree

    This type is unconstrained, and potentially nonsensical data could be
    represented.

*)
type raw_itree op s a =
  ipos op s -> option (inode op s a)

let isRet #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Ret x) -> true
  | _ -> false

let ret_val #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x) -> x

let isEvent #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Call o x) -> true
  | Some Tau -> true
  | _ -> false

let valid_itree (#op:eqtype) #s #a (t : raw_itree op s a) =
  forall p. isRet (t p) ==> (forall q. p `strict_suffix_of` q ==> None? (t q)) // Ret is final
  // Should we instead use some [consistent t p] boolean predicate that would traverse the itree?
  // Maybe forall p. (p == [] /\ Some? (t [])) \/ (exists q c. p == q @ [c] /\ consistent_choice (t q) c)
  // where consistent_choice n c checks that both are call or both tau
  // Two other options:
  // - say that isCall (t p) ==> forall y. Some? (t (p @ [Call_choice o x y])) where o and x are extracted from isCall
  //   and that isCall (t p) ==> None?(p @ [Tau_choice])
  //   and that None is final probably
  // - define the itree at a given position (not just the node) and say that at every (Some) position, the resulting
  //   itree is either ret or call or tau. Probably not going to work for SMT.

(** Itrees are defined by refinement over [raw_itree].

    The choice of only specifying what happens when an itree returns and
    nothing more can seem arbitrary as it doesn't forbid all ill-formed
    itrees. The reason for this choice is that it seems to be the minimal
    requirement to obtain a Dijkstra monad in the end.

*)
let itree (op:eqtype) s a =
  t:(raw_itree op s a) { valid_itree t }

(** return of the monad *)
let ret #op #s #a (x:a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Ret x)
    | _ -> None

(** monadic operations *)
let call (#op:eqtype) #s #a (o : op) (x : s.args o) (k : s.res o -> itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Call o x)
    | Tau_choice :: p -> None
    | Call_choice o' x' y :: p ->
      if o = o' && x = x'
      then k y p
      else None

(** delay *)
let tau #op #s #a (k : itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some Tau
    | Tau_choice :: p -> k p
    | Call_choice _ _ _ :: _ -> None

(** Before we can bind, we have to find a prefix of the position which returns
    and then forwards the suffix.
    Indeed, take for instance [ret x p] it will only return its contents it [p]
    is the empty list (or root position). [find_ret (ret x) [] p] will thus
    return [Some (x, p)] meaning that we can graft the other tree in place of
    the return leaf by forwarding the position [p] to it.

    [pp] is an accumaltor prefix, not efficient.
*)
let rec find_ret #op #s #a (m : itree op s a) (pp p : ipos op s) : Pure (option (a * ipos op s)) (requires True) (ensures fun r -> True) (decreases p) =
  if isRet (m pp)
  then Some (ret_val (m pp), p)
  else begin
    match p with
    | [] -> None
    | c :: p -> find_ret m (pp @ [c]) p
  end

let rec find_ret_None_noRet #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires find_ret m pp p == None)
    (ensures ~ (isRet (m (pp @ p))))
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p -> append_assoc pp [c] p ; find_ret_None_noRet m (pp @ [c]) p
  end

let rec find_ret_append_aux #op #s #a (m : itree op s a) pp p q :
  Lemma
    (ensures isRet (m (pp @ p)) ==> find_ret m pp (p @ q) == Some (ret_val (m (pp @ p)), q))
    (decreases p)
= if isRet (m pp)
  then strict_suffix_or_eq_append pp p
  else begin
    match p with
    | [] -> ()
    | c :: p ->
      begin
        append_assoc pp [c] p ;
        find_ret_append_aux m (pp @ [c]) p q
      end
  end

let find_ret_append #op #s #a (m : itree op s a) :
  Lemma (ensures forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q))
= forall_intro_2 (find_ret_append_aux m [])

let rec find_ret_strict_suffix_aux #op #s #a (m : itree op s a) pp p q u p' :
  Lemma
    (ensures
      find_ret m pp p == Some (u, p') ==>
      p `strict_suffix_of` q ==>
      (exists q'. find_ret m pp q == Some (u, q') /\ p' `strict_suffix_of` q')
    )
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p ->
      begin
        match q with
        | [] -> ()
        | c' :: q ->
          find_ret_strict_suffix_aux m (pp @ [c]) p q u p'
      end
  end

let find_ret_strict_suffix #op #s #a (m : itree op s a) :
  Lemma
    (ensures
      forall p q u p'.
        find_ret m [] p == Some (u, p') ==>
        p `strict_suffix_of` q ==>
        (exists q'. find_ret m [] q == Some (u, q') /\ p' `strict_suffix_of` q')
    )
= forall_intro_4 (find_ret_strict_suffix_aux m [])

let rec find_ret_Event_None #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires isEvent (m (pp @ p)))
    (ensures find_ret m pp p == None)
    (decreases p)
= if isRet (m pp)
  then begin
    match p with
    | [] -> ()
    | c :: p -> strict_suffix_or_eq_append pp (c :: p)
  end
  else begin
    match p with
    | [] -> ()
    | c :: p -> append_assoc pp [c] p ; find_ret_Event_None m (pp @ [c]) p
  end

let cast_node #op #s #a #b (n : (option (inode op s a)) { ~ (isRet n) }) : option (inode op s b) =
  match n with
  | Some Tau -> Some Tau
  | Some (Call o x) -> Some (Call o x)
  | None -> None

(** bind function

    We use [find_ret] as described above.
    We also make use of [cast_node] to deal with the case where there is
    no return leaf in the considered branch and the return type can then
    be anything as we return [m p] which is of type [inode op s a]
    instead of [inode op s b].

*)
let bind #op #s #a #b (m : itree op s a) (f : a -> itree op s b) : itree op s b =
  find_ret_strict_suffix m ;
  fun p ->
    match find_ret m [] p with
    | Some (x, q) -> f x q
    | None -> find_ret_None_noRet m [] p ; cast_node (m p)

(* An ill-formed loop *)
let bad_loop #op #s a : itree op s a =
  fun p -> Some Tau

(** A loop with no events/effects except non-termination *)
let loop #op #s a : itree op s a =
  fun p ->
    match filter (fun c -> c = Tau_choice) p with
    | [] -> Some Tau
    | _ -> None

let cont #op #s #a (n : inode op s a) r =
  match n with
  | Ret x -> unit
  | Call o x -> s.res o -> r
  | Tau -> r

(** Definition of a co-recursor *)

let cont_node op s a r =
  n: inode op s a & cont n r

let rec itree_corec_aux (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) (i : a) (p : ipos op s) :
  Pure (option (inode op s b)) (requires True) (ensures fun r -> True) (decreases p)
= match p with
  | [] ->
    let (| n, _ |) = f i in Some n
  | Tau_choice :: p ->
    begin match f i with
    | (| Tau, next |) -> itree_corec_aux f next p
    | _ -> None
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | (| Call o' x', next |) ->
      if o = o' && x = x'
      then itree_corec_aux f (next y) p
      else None
    | _ -> None
    end

let rec itree_corec_aux_final_ret (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) i p q :
  Lemma
    (ensures isRet (itree_corec_aux f i p) ==> p `strict_suffix_of` q ==> None? (itree_corec_aux f i q))
    (decreases p)
= match p with
  | [] ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau,  n |) -> ()
    | (| Call o' x', n |) -> ()
    end
  | Tau_choice :: p ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau, n |) ->
      begin match q with
      | [] -> ()
      | Tau_choice :: q -> itree_corec_aux_final_ret f n p q
      | Call_choice o x y :: q -> ()
      end
    | (| Call o' x', n |) -> ()
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau, n |) -> ()
    | (| Call o' x', n |) ->
      if o = o' && x = x'
      then begin
        match q with
        | [] -> ()
        | Tau_choice :: q -> ()
        | Call_choice oo xx yy :: q ->
          itree_corec_aux_final_ret f (n y) p q
      end
      else ()
    end

let itree_corec (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) (i : a) : itree op s b =
  forall_intro_2 (itree_corec_aux_final_ret f i) ;
  itree_corec_aux f i

(** Some notion of cofixpoint where the function should produce at least one
    constructor before calling itself recursively.

    Sadly, we need the productivity because we have to be able to produce a
    node when given a position.
    The idea is that we only have to unfold the cofixpoint [length p + 1]
    times to be able to get the node at position [p].

*)

(* Unfold the function (n+1) times *)
let rec itree_cofix_unfoldn (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (n : nat) : a -> itree op s b =
  if n = 0
  then ff (fun _ -> loop _)
  else ff (itree_cofix_unfoldn ff (n - 1))

unfold
let itree_cofix_guarded (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) =
  forall (x : a) (n : nat) (p : ipos op s).
    length p <= n ==>
    itree_cofix_unfoldn ff (length p) x p == itree_cofix_unfoldn ff n x p

let itree_cofix (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (x : a) :
  Pure (itree op s b) (requires itree_cofix_guarded ff) (ensures fun _ -> True)
= fun p -> itree_cofix_unfoldn ff (length p) x p

(* Trivial cofix *)
let ret' #op #s #a (v : a) : itree op s a =
  itree_cofix (fun (_ : unit -> itree op s a) (_ : unit) -> ret v) ()

(* It seems that the guard is too hard to prove for the SMT when there is a
   recursive call. This suggests that maybe we should go for iter directly
   instead.
 *)

(* Alternative def of loop using cofix to test it *)
let loop' #op #s a : itree op s a =
  admit () ;
  itree_cofix (fun loop_ (_ : unit) ->
    tau (loop_ ())
  ) ()

(* Definition of iter from cofixpoint *)
let iter (#op : eqtype) #s #ind #a (step : ind -> itree op s (either ind a)) : ind -> itree op s a =
  admit () ;
  itree_cofix (fun iter_ i ->
    bind (step i) (fun ir ->
      begin match ir with
      | Inl j -> tau (iter_ j)
      | Inr r -> ret r
      end
    )
  )

(** Monad instance

   Without GetTrace for now

*)

open Common

type cmds = | Openfile | Read | Close

unfold let io_args cmd : eqtype =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

unfold let io_res cmd : eqtype =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_op_sig : op_sig cmds = {
  args = io_args ;
  res = io_res
}

unfold
let iotree a = itree cmds io_op_sig a

unfold
let iopos = ipos cmds io_op_sig

unfold
let iochoice = ichoice cmds io_op_sig

unfold
let ioret #a (x : a) : iotree a =
  ret x

(**
  Spec with trace
  The trace contains the response of the environment, in fact it is a subset of
  positions where Tau steps are ignored.

  This specification if enough to talk about (non-)termination of a program
  with respect to its interaction with the environment. Unfortunately, it is
  still more limited than the Itrees in Coq.
*)

let trace = list (c: iochoice { c <> Tau_choice })

let rec ipos_trace (p : iopos) : trace =
  match p with
  | [] -> []
  | Tau_choice :: p -> ipos_trace p
  | Call_choice o x y :: p -> Call_choice o x y :: ipos_trace p

let rec ipos_trace_append (p q : iopos) :
  Lemma (ensures ipos_trace (p @ q) == ipos_trace p @ ipos_trace q) (decreases p)
= match p with
  | [] -> ()
  | Tau_choice :: p -> ipos_trace_append p q
  | Call_choice o x y :: p -> ipos_trace_append p q

unfold
let tio_post a = trace -> option a -> Type0

let twp a = tio_post a -> Type0

let twp_return #a (x : a) : twp a =
  fun post -> post [] (Some x)

let shift_post #a (tr : trace) (post : tio_post a) : tio_post a =
  fun tr' x -> post (tr @ tr') x

let twp_bind #a #b (w : twp a) (f : a -> twp b) : twp b =
  fun post ->
    w (fun tr v ->
      match v with
      | Some x -> f x (shift_post tr post)
      | None -> post tr None
    )

let stronger_twp #a (wp1 wp2 : twp a) : Type0 =
  forall post. wp1 post ==> wp2 post

unfold
let noFutureRet #a (t : iotree a) p =
  forall q. p `strict_suffix_of` q ==> ~ (isRet (t q))

let io_twp #a (t : iotree a) =
  fun post ->
    (forall p. isRet (t p) ==> post (ipos_trace p) (Some (ret_val (t p)))) /\
    (forall p. isEvent (t p) ==> noFutureRet t p ==> post (ipos_trace p) None)

let tio a (w : twp a) =
  t: iotree a { io_twp t `stronger_twp` w }

let tio_return a (x : a) : tio a (twp_return x) =
  assert (isRet (ioret #a x [])) ;
  ret x

let rec noFutureRet_find_ret_None_aux #a (m : iotree a) pp p q :
  Lemma
    (ensures find_ret m pp p == None ==> noFutureRet m p ==> p `strict_suffix_of` q ==> find_ret m pp q == None)
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> assume (noFutureRet m [] ==> [] `strict_suffix_of` q ==> find_ret m pp q == None)
    | c :: p ->
      begin match q with
      | [] -> ()
      | c' :: q ->
        begin
          noFutureRet_find_ret_None_aux m (pp @ [c]) p q ;
          // The problem is that noFutureRet should also mention pp
          assert (find_ret m (pp @ [c]) p == None ==> noFutureRet m p ==> p `strict_suffix_of` q ==> find_ret m (pp @ [c]) q == None) ;
          assume (find_ret m (pp @ [c]) p == None ==> noFutureRet m (c :: p) ==> (c :: p) `strict_suffix_of` (c' :: q) ==> find_ret m (pp @ [c]) q == None)
        end
      end
  end

let noFutureRet_find_ret_None #a (m : iotree a) :
  Lemma (forall p q. find_ret m [] p == None ==> noFutureRet m p ==> p `strict_suffix_of` q ==> find_ret m [] q == None)
= forall_intro_2 (noFutureRet_find_ret_None_aux m [])

let tio_bind_aux1 a b w wf (m : tio a w) (f : (x:a) -> tio b (wf x)) :
  Lemma (forall post p. io_twp (bind m f) post ==> isRet (m p) ==> wf (ret_val (m p)) (shift_post (ipos_trace p) post))
= find_ret_append m ;
  assert (forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q)) ;
  assert (forall p q. isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> ret_val (bind m f (p @ q)) == ret_val (f (ret_val (m p)) q)) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ipos_trace (p @ q)) (Some (ret_val (bind m f (p @ q))))) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ipos_trace (p @ q)) (Some (ret_val (f (ret_val (m p)) q)))) ;
  find_ret_strict_suffix m ;
  assert (forall p q. isRet (m p) ==> noFutureRet (f (ret_val (m p))) q ==> noFutureRet (bind m f) (p @ q)) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isEvent (f (ret_val (m p)) q) ==> noFutureRet (f (ret_val (m p))) q ==> post (ipos_trace (p @ q)) None) ;
  assert (forall x. io_twp (f x) `stronger_twp` wf x) ;
  forall_intro_2 ipos_trace_append

let tio_bind_aux2 a b w wf (m : tio a w) (f : (x:a) -> tio b (wf x)) :
  Lemma (forall post p. io_twp (bind m f) post ==> isEvent (m p) ==> noFutureRet m p ==> post (ipos_trace p) None)
= forall_intro (move_requires (find_ret_Event_None m [])) ;
  assert (forall p. isEvent (m p) ==> find_ret m [] p == None) ;
  assert (forall p. isEvent (m p) ==> isEvent (bind m f p)) ;
  noFutureRet_find_ret_None m ;
  assert (forall p. isEvent (m p) ==> noFutureRet m p ==> noFutureRet (bind m f) p)

// Sometimes need to be retried
let tio_bind a b w wf (m : tio a w) (f : (x:a) -> tio b (wf x)) : tio b (twp_bind w wf) =
  tio_bind_aux1 a b w wf m f ;
  tio_bind_aux2 a b w wf m f ;
  bind m f

// Cannot reproduce itree_cofix_unfoldn as above because of the "base"-case
// of [loop]. Here we would need something in [tio b w] for an arbitrary [w].
// Another point for going for [iter] directly.
// let rec tio_cofix_unfoldn #a #b #w (ff : (a -> tio b w) -> a -> tio b w) (n : nat) : a -> tio b w =
//   if n = 0
//   then ff (fun _ -> loop _)
//   else ff (tio_cofix_unfoldn ff (n - 1))

[@@allow_informative_binders]
reifiable total layered_effect {
  TIO : a:Type -> twp a -> Effect
  with
    repr   = tio ;
    return = tio_return ;
    bind   = tio_bind
}
