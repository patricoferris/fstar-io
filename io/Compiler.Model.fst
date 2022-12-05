module Compiler.Model

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open BeyondCriteria

open IO.Sig
open TC.Monitorable.Hist
  
open Compiler.Languages
open Compile.IIO.To.ILang

type typ_io_cmds (fl:erased tflag) (pi:monitorable_prop) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  IIO (io_sig.res cmd arg) fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      (match r with
       | Inr Contract_failure -> ~(pi cmd arg h) /\ lt == []
       | r' -> pi cmd arg h /\ lt == [convert_call_to_event cmd arg r'])))

val inst_io_cmds : pi:monitorable_prop -> typ_io_cmds AllActions pi
let inst_io_cmds pi cmd arg =
  let h = get_trace () in
  if pi cmd arg h then (admit (); static_cmd cmd arg)
  else Inr Contract_failure

(**
val convert_insts : (ipi:monitorable_prop) -> (epi:monitorable_prop) -> (_:squash (forall h cmd arg. epi cmd arg h ==> ipi cmd arg h)) ->
  (cmd_call:typ_io_cmds AllActions ipi) -> (typ_io_cmds AllActions epi) 
let convert_insts ipi epi () cmd_call cmd arg = 
  assert (forall h. epi cmd arg h ==> ipi cmd arg h);
  cmd_call cmd arg 
**)

(** *** IIO interface **)
noeq
type iio_interface = {
  ct : erased tflag -> Type;
  pt : erased tflag -> Type;

  ct_rcs : tree pck_rc;
  //pt_rc : tree pck_rc;

  epi : monitorable_prop;
 // ipi : monitorable_prop;
//  ipi_stronger_epi : squash (forall h cmd arg. ipi cmd arg h ==> epi cmd arg h);

  //pt_exportable : exportable pt ipi pt_rc AllActions;
  ct_importable : fl:erased tflag -> safe_importable (ct fl) epi ct_rcs fl;
}

let make_rcs_eff (rcs:tree pck_rc) : typ_posts AllActions rcs =
  let r : tree (pck_eff_rc AllActions) = map_tree rcs make_rc_eff in
  assume (equal_trees rcs (map_tree r dfst));
  r

type ctx_iio (i:iio_interface) = #fl:erased tflag -> typ_posts fl i.ct_rcs -> typ_io_cmds fl i.epi -> i.ct fl 

type prog_iio (i:iio_interface) = #fl:erased tflag -> i.ct (IOActions + fl) -> i.pt (IOActions + fl)

let iio_language : language = {
  interface = iio_interface;

  ctx = ctx_iio;
  pprog = prog_iio;
  whole = (i:iio_interface & i.pt AllActions);

  link = (fun #i p c -> 
    let eff_rcs = make_rcs_eff i.ct_rcs in
    (| i, p #AllActions (c #AllActions eff_rcs (inst_io_cmds i.epi)) |));
  event_typ = IO.Sig.event;

  beh = admit ()
}

(** *** ILang interface **)
noeq
type ilang_interface = {
  pt : Type;
  ct : erased tflag -> Type;

  epi : monitorable_prop;
  
  //pt_ilang : ilang pt ipi;
  ct_ilang : fl:erased tflag -> ilang (ct fl) epi;
}

type ctx_ilang (i:ilang_interface) = #fl:erased tflag -> typ_io_cmds fl i.epi -> i.ct fl
type prog_ilang (i:ilang_interface) = i.ct AllActions -> i.pt

let ilang_language : language = {
  interface = ilang_interface;

  ctx = ctx_ilang;
  pprog = prog_ilang;
  whole = (i:ilang_interface & i.pt);

  link = (fun #i p c -> (| i, p (c (inst_io_cmds i.epi)) |));
  event_typ = IO.Sig.event;

  beh = admit ();
}

(** ** Compile interfaces **)
let comp_int_iio_ilang (i:iio_interface) : ilang_interface = {
 // pt = resexn i.pt_exportable.etype;
  pt = i.pt AllActions;
  ct = (fun fl -> (i.ct_importable fl).sitype);
  epi = i.epi;

//  pt_ilang = ilang_resexn i.ipi i.pt_exportable.etype #i.pt_exportable.c_etype;
  ct_ilang = (fun fl -> (i.ct_importable fl).c_sitype);
}


(** ** Phases of compilation **)
val compiler_pprog_iio_ilang : (#i:iio_interface) -> (p_s:prog_iio i) -> ilang_language.pprog (comp_int_iio_ilang i)
let compiler_pprog_iio_ilang #i p_s c_t = 
  let eff_rcs = make_rcs_eff i.ct_rcs in
  let c_s : i.ct AllActions = (i.ct_importable AllActions).safe_import c_t eff_rcs in
  let p : i.pt AllActions = p_s #AllActions c_s in
  // let eff_rc = make_all_rc_eff i.pt_rc in
  // (i.pt_exportable.export eff_rc p)
  p

let phase1 : compiler = {
  source = iio_language;
  target = ilang_language;

  comp_int = comp_int_iio_ilang;

  compile_pprog = compiler_pprog_iio_ilang;

  rel_traces = (==);
}

val backtranslate : (#i:iio_interface) -> (c_t:ctx_ilang (comp_int_iio_ilang i)) -> iio_language.ctx i
let backtranslate #i c_t #fl eff_rcs acts =
  let c_s = (i.ct_importable fl).safe_import (c_t #fl acts) eff_rcs in
  c_s

open FStar.List

(** Tests **)
let test_interface : iio_interface = {
  epi = (fun _ _ _ -> true);

  pt = (fun fl -> (unit -> IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> true)));
  // pt_rc = EmptyNode Leaf Leaf;

  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rcs = Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) Leaf Leaf;


  // pt_exportable = exportable_arrow_with_no_pre_and_no_post unit #importable_unit unit #exportable_unit;
  ct_importable = admit () //safe_importable_is_importable (safe_importable_arrow_pre_post file_descr unit );
}

val test_prog : prog_iio test_interface
let test_prog #fl ctx () : IIO (resexn unit) (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) =
  let _ = ctx () in
  Inl ()

val test_ctx : ctx_iio test_interface
let test_ctx #fl eff_rcs io_acts () : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  io_acts Openfile "/etc/passwd"
