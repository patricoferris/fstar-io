module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

(** ** Source Language **)
include IIO

(** ** Target Language **)
(** Tlang is a language that acts as an intermediate language between the rich IIO effect that has
    rich types and pre- and post-conditions and an ML language as OCaml.

    The task of compiling an IIO computation is big and it implies converting rich types and pre- and
    post-conditions to runtime checks. Therefore, this intermediate language simplifies our work.
    By compiling to this intermediate language, we convert all of this static requirments to dynamic checks
    but we keep the post-conditions around enough to show that the computation preserves its trace
    properties.

    So, Tlang is weakly typed and its computation can have only as post-condition that it respects a 
    trace property. The pre-condition must be trivial.
**)

(** access_policy is the type of the runtime check that is enforced when instrumenting.
    A access_policy checks if the next operation with its arguments satisfy the property
    over the history. **)
type access_policy = (history:trace) -> (isTrusted:bool) -> (cmd:io_cmds) -> (io_sig.args cmd) -> Type0

(** TODO: show that the type of access_policy is enough to enforce any monitorable property
 (from Grigore Rosu's paper) **)

unfold
let has_event_respected_pi (e:event) (ap:access_policy) (h:trace) : Type0 =
  match e with
  | EOpenfile isTrusted arg _ -> ap h isTrusted Openfile arg
  | ERead isTrusted arg _ -> ap h isTrusted Read arg
  | EWrite isTrusted arg _ -> ap h isTrusted Write arg
  | EClose isTrusted arg _ -> ap h isTrusted Close arg

(** `enforced_locally pi` is a prefix-closed safety trace property. **)
let rec enforced_locally
  (ap : access_policy)
  (h l: trace) :
  Tot Type0 (decreases l) =
  match l with
  | [] -> true
  | e  ::  t ->
    (has_event_respected_pi e ap h ==> enforced_locally (ap) (e::h) t) /\
    ~(has_event_respected_pi e ap h ==> False)
  
let pi_as_hist (#a:Type) (pi:access_policy) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : access_policy) = 
  IIOwp a fl (pi_as_hist #a pi)

class tlang (t:Type u#a) (fl:erased tflag) (pi:access_policy) = { [@@@no_method] mldummy : unit }

instance tlang_unit fl pi : tlang unit fl pi = { mldummy = () }
instance tlang_file_descr fl pi : tlang file_descr fl pi = { mldummy = () }

instance tlang_pair fl pi t1 {| d1:tlang t1 fl pi |} t2 {| d2:tlang t2 fl pi |} : tlang (t1 * t2) fl pi = 
  { mldummy = () }
instance tlang_either fl pi t1 {| d1:tlang t1 fl pi |} t2 {| d2:tlang t2 fl pi |} : tlang (either t1 t2) fl pi =
  { mldummy = () }
instance tlang_resexn fl pi t1 {| d1:tlang t1 fl pi |} : tlang (resexn t1) fl pi =
  { mldummy = () }

type tlang_arrow_typ fl pi (t1 t2:Type) = t1 -> IIOpi t2 fl pi

(** An tlang arrow is a statically/dynamically verified arrow to respect pi.
**)
instance tlang_arrow fl pi #t1 (d1:tlang t1 fl pi) #t2 (d2:tlang t2 fl pi) : tlang (tlang_arrow_typ fl pi t1 t2) fl pi =
  { mldummy = () }

instance tlang_bool fl pi : tlang bool fl pi = { mldummy = () }
instance tlang_int fl pi : tlang int fl pi = { mldummy = () }
instance tlang_option fl pi t1 {| d1:tlang t1 fl pi |} : tlang (option t1) fl pi =
  { mldummy = () }

(**instance tlang_fo_uint8 : tlang_fo UInt8.t = { fo_pred = () }
instance tlang_fo_string : tlang_fo string = { fo_pred = () }
instance tlang_fo_bytes : tlang_fo Bytes.bytes = { fo_pred = () }
instance tlang_fo_open_flag : tlang_fo open_flag = { fo_pred = () } 
instance tlang_fo_socket_bool_option : tlang_fo socket_bool_option = { fo_pred = () }
instance tlang_fo_file_descr : tlang_fo file_descr = { fo_pred = () }
instance tlang_fo_zfile_perm : tlang_fo zfile_perm = { fo_pred = () }
instance tlang_fo_pair_2 t1 t2 t3 {| tlang_fo t1 |} {| tlang_fo t2 |} {| tlang_fo t3 |} : tlang_fo (t1 * t2 * t3) = { fo_pred = () }
instance tlang_fo_pair_3 t1 t2 t3 t4 {| tlang_fo t1 |} {| tlang_fo t2 |} {| tlang_fo t3 |} {| tlang_fo t4 |} : tlang_fo (t1 * t2 * t3 * t4) = { fo_pred = () }
instance tlang_fo_option t1 {| tlang_fo t1 |} : tlang_fo (option t1) = { fo_pred = () }
instance tlang_fo_list t1 {| tlang_fo t1 |} : tlang_fo (list t1) = { fo_pred = () } **)
