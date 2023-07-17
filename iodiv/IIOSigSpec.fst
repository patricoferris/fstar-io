module IIOSigSpec

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
open DivFreeTauSpec
open DivFreeTauDM

unfold
let i_open (s : string) : iwp file_descr =
  iprepost (fun _ -> True) (fun hist r -> terminates r /\ _trace r == [ EOpenfile s (result r) ])

unfold
let i_read (fd : file_descr) : iwp string =
  iprepost (fun hist -> is_open fd hist) (fun hist r -> terminates r /\ _trace r == [ ERead fd (result r) ])

unfold
let i_print (s : string) : iwp unit =
  iprepost (fun hist -> True) (fun hist r -> terminates r /\ _trace r == [ EPrint s ])

unfold
let i_close (fd : file_descr) : iwp unit =
  iprepost (fun hist -> is_open fd hist) (fun hist r -> terminates r /\ _trace r == [ EClose fd ])

unfold
let i_get_trace : iwp history =
  as_iwp (fun post hist -> post (Cv [] hist))

unfold
let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | Openfile -> i_open arg
    | Read -> i_read arg
    | Print -> i_print arg
    | Close -> i_close arg

unfold
let iiodiv_act : action_iwp iio_sig =
  fun ac arg ->
    match ac with
    | GetTrace -> i_get_trace
    | _ -> iodiv_act ac arg
