open LibASL


open Yojson
open Cohttp
open Cohttp_lwt
open Cohttp_lwt_unix
open String
open List
open Array
open Asl_ast
open Value
open Eval
open Asl_utils
open Lwt


let persistent_env = lazy (Option.get (aarch64_evaluation_environment ()))

let eval_instr (opcode: string) : string =
    let pp_raw stmt : string = Utils.to_string (Asl_parser_pp.pp_raw_stmt stmt) |> String.trim  in
    let address = None                                     in
    let env' = Lazy.force persistent_env                    in
    let stmts : Asl_ast.stmt list  = Dis.retrieveDisassembly ?address env' (Dis.build_env env') opcode in
    let stmts'   = List.map pp_raw stmts                                                 in
    String.concat "\n" stmts'


let get_reply (jsonin: string) : Cohttp.Code.status_code * string =
  (*let json  = Yojson.Safe.from_string jsonin in *)
  let make_reply code tail =
    (code, Yojson.Safe.to_string (`Assoc [("instruction", `String jsonin); tail])) in
  Printf.printf "Disassembling '%s'\n" jsonin;
  flush stdout;
  match (eval_instr jsonin) with
  | exception e -> make_reply `Internal_server_error ("error", `String (Printexc.to_string e))
  | x -> make_reply `OK ("semantics", `String x)


let unsupp_method_resp : Cohttp.Code.status_code * string =
  (`Method_not_allowed, Yojson.Safe.to_string (`Assoc [("error", `String "unsupported method.")]))

let missing_param : Cohttp.Code.status_code * string =
  (`Bad_request, Yojson.Safe.to_string (`Assoc [("error", `String "missing opcode param.")]))

(*let () = ignore (List.map (fun (f: string) -> print_endline (eval_instr f)) (tl (to_list Sys.argv))) *)


let get_resp (opcode: string) : Cohttp.Code.status_code * string =
    get_reply opcode

let server addr port =
  Printf.printf "Started aslp-server at http://%s:%d\n" addr port;
  flush stdout;
  let callback _conn req body =
    let uri = req |> Request.uri in
    let meth = req |> Request.meth |> Code.string_of_method in
    let headers = req |> Request.headers |> Header.to_string in
    let body' = body |> Cohttp_lwt.Body.to_string in
    let resp' =
      match (Request.meth req, Uri.get_query_param uri "opcode") with
      | `POST, _ -> body' >|= get_resp
      | `GET, Some param -> Lwt.return (get_resp param)
      | `GET, None -> Lwt.return missing_param
      |  _ -> Lwt.return unsupp_method_resp
    in
    resp' >>= fun (code, body) -> Server.respond_string ~status:code ~body ()
  in
  Server.create ~mode:(`TCP (`Port port)) (Server.make ~callback ())

let port_opt : int ref = ref 8000
let addr_opt : string ref = ref "127.0.0.1"

let speclist =
  [
    ("--host", Arg.Set_string addr_opt, "Server address (default loopback)");
    ("--port", Arg.Set_int port_opt, "Server port (default 8000)");
  ]

let () = Arg.parse speclist ignore "usage: aslp-server --host HOSTNAME --port PORT"

let () =
  let address = Unix.(ADDR_INET (inet_addr_of_string !addr_opt, !port_opt)) in
  Lwt_main.run (server !addr_opt !port_opt)

