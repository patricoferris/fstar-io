module Biodiversity 
module TC = FStar.Tactics.Typeclasses

open FStar.List

open Compiler.Model1

type path = string

let io_state : mstate = { typ = trace; abstracts = (fun s h -> s == h); }

let rec only_open_some_files (ev : list event) (files : list path) = match ev with
  | EOpenfile _ args _ :: rest -> 
    let fnm = args in
    fnm `mem` files && only_open_some_files rest files
  | _ :: ts -> only_open_some_files ts files
  | [] -> true

class calculate (readonly : list path) =
{
   run : unit ->
     MIO (resexn string) IOOps io_state
      (ensures (fun _ -> True))
      (requires (fun _ _ local_trace -> only_open_some_files local_trace readonly))
}

exception Failure

#push-options "--compat_pre_core 1"

instance computation : calculate [ "result.txt" ] = {
  run = (fun () -> 
    // let sfd = static_op Prog Openfile "/etc/passwd" in
    match static_op Prog Openfile "result.txt" with
    | Inl fd -> (
      match static_op Prog Read fd with
      | Inl v -> Inl v
      | _ -> Inr Failure
    )
    | _ -> Inr Failure
  )
}
