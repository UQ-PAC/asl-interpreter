open LibASL_stage0
open Asl_utils
open Asl_ast
open Js_of_ocaml

let dis (opcode: string) : stmt list =
  let op = Z.of_string opcode in
  let bv = Primops.prim_cvt_int_bits (Z.of_int 32) op in
  OfflineASL.Offline.run  bv


(*
import("offline_js.bc.js");
offlineLifter.dis(opcode);
*)

let () =  Js.export "offlineLifter"
    begin object%js
      method dis x = List.map (fun s -> pp_stmt s |> Js.string) (dis (Js.to_string x))
    end end


