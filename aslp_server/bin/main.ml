open LibASL
open Cohttp
open Cohttp_eio
open List
open Asl_ast

(* Lifter wrapper *)

let persistent_env = lazy (Option.get (Arm_env.aarch64_evaluation_environment ()))
let count = Atomic.make 0

let eval_instr (opcode : string) : string * string =
  let pp_raw stmt : string =
    Utils.to_string (Asl_parser_pp.pp_raw_stmt stmt) |> String.trim
  in
  let _address = None in

  let env' = Lazy.force persistent_env in
  let lenv = Dis.build_env env' in
  let decoder = Eval.Env.getDecoder env' (Ident "A64") in
  let enc, stmts =
    Dis.dis_decode_entry_with_inst env' lenv decoder (Z.of_string opcode)
  in

  let stmts' = List.map pp_raw stmts in
  (enc, String.concat "\n" stmts')

let get_reply (jsonin : string) : Cohttp.Code.status_code * string =
  let make_reply code tail =
    ( code,
      Yojson.Safe.to_string
        (`Assoc ([ ("instruction", `String jsonin) ] @ tail)) )
  in
  match eval_instr jsonin with
  | exception e ->
      make_reply `Internal_server_error
        [ ("error", `String (Printexc.to_string e)) ]
  | enc, x ->
      make_reply `OK [ ("encoding", `String enc); ("semantics", `String x) ]

let unsupp_method_resp : Cohttp.Code.status_code * string =
  ( `Method_not_allowed,
    Yojson.Safe.to_string (`Assoc [ ("error", `String "unsupported method.") ])
  )

let missing_param : Cohttp.Code.status_code * string =
  ( `Bad_request,
    Yojson.Safe.to_string
      (`Assoc [ ("error", `String "missing opcode param.") ]) )

let try_set_flags xs : (unit, Cohttp.Code.status_code * string) Result.t =
  match List.iter Flags.set_flag xs with
  | exception (Arg.Bad _ as e) ->
      Result.error
        ( `Bad_request,
          Yojson.Safe.to_string
            (`Assoc [ ("error", `String (Printexc.to_string e)) ]) )
  | _ -> Result.ok ()

let get_resp (opcode : string) : Cohttp.Code.status_code * string =
  if String.equal opcode "die" then exit 0;
  get_reply opcode

type 'a work = Decode of (string * ('a, exn) result Eio.Promise.u)

(* Paralellism Structure

   We have one cohttp request handler domain and an executor pool of 
   workers doing opcode lifting across possibly multiple domains. 

   Basic benchmarks show that cohttp-eio is able to handle 
   >100000 request/second when not doing any work, so in our case
   we are sufficiently compute-bound that multithreading the 
   request handler has no impact.
*)

let submit_req_executor_pool pool opcode =
  Atomic.incr count; 
  Eio.Executor_pool.submit_exn pool ~weight:0.001 (fun () -> get_resp opcode)

(* Request handling *)
let server socket addr port get_resp =
  Eio.traceln "Started aslp-server at http://%s:%d\n" addr port;
  flush stdout;

  let oldflags = Flags.get_flags () in

  let callback _conn req (body : Server.body) =
    let uri = req |> Request.uri in
    let _meth = req |> Request.meth |> Code.string_of_method in
    let _headers = req |> Request.headers |> Header.to_string in

    Flags.set_flags oldflags;

    let code, body =
      match Option.map try_set_flags (Uri.get_query_param' uri "flags") with
      | Some (Error xs) -> xs
      | Some (Ok ()) | None -> (
          match (Request.meth req, Uri.get_query_param uri "opcode") with
          | `POST, _ ->
              let body' : string = Eio.Flow.read_all body in
              get_resp body'
          | `GET, Some param -> get_resp param
          | `GET, None -> missing_param
          | _ -> unsupp_method_resp)
    in
    Server.respond_string ~status:code ~body ()
  in
  Server.run
    ~mode:(`TCP (`Port port))
    socket (Server.make ~callback ())
    ~on_error:(Eio.traceln "Error handling connection: %a" Fmt.exn)

let port_opt : int ref = ref 8000
let addr_opt : string ref = ref "127.0.0.1"
let threads_opt : int ref = ref 4
let killserver = ref false

let speclist =
  [
    ("--host", Arg.Set_string addr_opt, "Server ip address (default 127.0.0.1)");
    ("--port", Arg.Set_int port_opt, "Server port (default 8000)");
    ("--threads", Arg.Set_int threads_opt, "Number of lifter worker threads");
    ("--killserver", Arg.Set killserver, "Tell the server to shut down");
  ]

let rec periodic t () =
  Eio.Time.sleep t 5.0;
  Eio.traceln "lifted %d ops" (Atomic.get count);
  periodic t ()

let () =
  Arg.parse speclist ignore "usage: aslp-server --host HOSTNAME --port PORT";
  let main env =
    let unix_addr = Unix.inet_addr_of_string !addr_opt in
    let e = Eio_unix.Net.Ipaddr.of_unix unix_addr in
    let addr = `Tcp (e, !port_opt) in

    let killwork sw =
      let client = Client.make ~https:None env#net in
      let _ =
        try
          Client.get ~sw client
            (Uri.of_string
               (Printf.sprintf "http://%s:%d/?opcode=die" !addr_opt !port_opt))
          |> ignore
        with | Failure x -> Eio.traceln "%s" x  
      in
      ()
    in

    let work sw =
      (* force the env before starting the server *)
      let _ = Lazy.force persistent_env in
      Eio.Fiber.fork ~sw (periodic env#clock);
      let pool =
        Eio.Executor_pool.create ~sw env#domain_mgr ~domain_count:!threads_opt
      in
      let decode opcode = submit_req_executor_pool pool opcode in
      let socket =
        Eio.Net.listen ~sw ~backlog:5 ~reuse_addr:true env#net addr
      in
      let fd = Eio_unix.Net.fd socket in
      Eio_unix.Fd.use fd
        (fun fd -> Unix.setsockopt fd Unix.TCP_NODELAY true)
        ~if_closed:(fun () -> ());
      server socket !addr_opt !port_opt decode
    in
    if !killserver then Eio.Switch.run killwork else Eio.Switch.run work
  in
  Eio_main.run main
