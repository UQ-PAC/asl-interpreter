open LibASL_stage0
open Asl_utils
open Asl_ast
open Js_of_ocaml

let init input out err =
  Js_of_ocaml.Sys_js.set_channel_flusher stdout out;
  Js_of_ocaml.Sys_js.set_channel_flusher stderr err;
  Js_of_ocaml.Sys_js.set_channel_filler stdin input;
  ()

let dis (opcode: string) : stmt list =
  let op = Z.of_string opcode in
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) op in
  OfflineASL.Offline.run  bv


(*
import("offline_js.bc.js");
offlineLifter.dis(opcode);
*)

let () = Js.export "aslp_offline"
  begin object%js
    method init (out : string -> unit) (err : string -> unit) =
      Printexc.record_backtrace true;
      init (fun () -> "") out err
    method formatException (exn : exn) = Printexc.to_string exn
    method printException (exn : exn) = output_string stderr (Printexc.to_string exn)

    method dis x = List.map (fun s -> pp_stmt s |> Js.string) (dis (Js.to_string x))
  end end


