(** Partial Dijkstra monad definition on top of DivFree *)

module DivFreeDM

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality

open Util
open Stream
open IIOSig
open DivFree
open DivFreeSpec

type action_wp (sg : signature) =
  ac : sg.act -> x : sg.arg ac -> wp (sg.res x)

let rec theta (#a : Type u#a) #sg (w_act : action_wp sg) (c : m sg a) : wp a =
  match c with
  | Ret x -> w_ret x
  | Req pre k -> w_bind (w_req pre) (fun x -> theta w_act (k x))
  | Iter index b f i k -> w_bind (w_iter u#a (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (k x))
  | Call ac x k -> w_bind (w_act ac x) (fun x -> theta w_act (k x))

let theta_ret #a #sg (w_act : action_wp sg) (x : a) :
  Lemma (theta w_act (m_ret x) `wle` w_ret x)
= ()

// TODO MOVE
let strace_prepend_nil s :
  Lemma (strace_prepend [] s == s)
= match s with
  | Fintrace t -> assert (([] @ t) == t)
  | Inftrace t -> forall_intro (stream_ext t)

// TODO MOVE
let shift_post_nil #a (post : w_post a) :
  Lemma (shift_post [] post `w_post_le` post)
= introduce forall r. shift_post [] post r ==> post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv s -> strace_prepend_nil s
  end

// TODO MOVE
let shift_post_nil_imp #a (post : w_post a) :
  Lemma (post `w_post_le` shift_post [] post)
= introduce forall r. post r ==> shift_post [] post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv s -> strace_prepend_nil s
  end

// TODO Make more principled with w_bind_mono and assoc
let rec theta_bind (#a : Type u#a) (#b : Type u#b) #sg (w_act : action_wp sg) (c : m sg a) (f : a -> m sg b) :
  Lemma (theta w_act (m_bind c f) `wle` w_bind (theta w_act c) (fun x -> theta w_act (f x)))
= match c with
  | Ret x -> forall_intro (shift_post_nil #b)

  | Req pre k ->

    calc (==) {
      m_bind (Req pre k) f ;
      == { _ by (compute ()) }
      Req pre (fun _ -> m_bind (k ()) f) ;
    } ;

    calc (==) {
      theta w_act (Req pre k) ;
      == { _ by (compute ()) }
      w_bind (w_req pre) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Req pre (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_req pre) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    w_bind_assoc (w_req pre) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    w_bind_mono (w_req pre) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    wle_trans (theta w_act (m_bind c f)) (w_bind (w_req pre) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (w_bind (theta w_act c) (fun x -> theta w_act (f x)))

  | Iter index ct g i k ->

    calc (==) {
      m_bind (Iter index ct g i k) f ;
      == { _ by (compute ()) }
      Iter index ct (fun j -> m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x))) i (fun y -> m_bind (k y) f) ;
    } ;

    calc (==) {
      theta w_act (Iter index ct g i k) ;
      == { _ by (compute ()) }
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Iter index ct (fun j -> m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x))) i (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_iter (fun j -> theta w_act (m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x)))) i) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    w_bind_assoc (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    // w_bind_mono (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    // Is there a problem with respect to g satying g in theta but not in m_bind?
    calc (wle) {
      theta w_act (m_bind c f) ;
      == {}
      theta w_act (m_bind (Iter index ct g i k) f) ;
      == {}
      theta w_act (Iter index ct (fun j -> m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x))) i (fun y -> m_bind (k y) f)) ;
      == {}
      w_bind (w_iter (fun j -> theta w_act (m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x)))) i) (fun x -> theta w_act (m_bind (k x) f)) ;
      `wle` {} // If need be, can use w_bind_mono explicitly
      w_bind (w_iter (fun j -> theta w_act (m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x)))) i) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;
      `wle` { admit () }
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ; // Is it a good intermediary? Can also target w_bind (theta w_act c) (fun x -> theta w_act (f x)) directly
    } ;
    // assert (w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) `wle` w_bind (theta w_act c) (fun x -> theta w_act (f x))) ;
    wle_trans (theta w_act (m_bind c f)) (w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (w_bind (theta w_act c) (fun x -> theta w_act (f x)))

   // admit ()

  | Call ac x k ->

    calc (==) {
      m_bind (Call ac x k) f ;
      == { _ by (compute ()) }
      Call ac x (fun y -> m_bind (k y) f) ;
    } ;

    calc (==) {
      theta w_act (Call ac x k) ;
      == { _ by (compute ()) }
      w_bind (w_act ac x) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Call ac x (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    w_bind_assoc (w_act ac x) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    w_bind_mono (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    wle_trans (theta w_act (m_bind c f)) (w_bind (w_act ac x) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (w_bind (theta w_act c) (fun x -> theta w_act (f x)))

let theta_req #a #sg (w_act : action_wp sg) (pre : pure_pre) :
  Lemma (theta w_act (m_req pre) `wle` w_req pre)
= ()
