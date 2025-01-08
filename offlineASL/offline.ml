(* AUTO-GENERATED LIFTER FILE *)

open Offline_utils
open Decode_tests

let f_A64_decoder v_enc : unit = 
  failwith "unsupported"

let run ?pc enc =
  reset_ir ();
  f_A64_decoder enc;
  get_ir ()
