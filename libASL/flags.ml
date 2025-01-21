module StringMap = Map.Make(String)

let flags = StringMap.of_seq @@ List.to_seq [
    ("trace:write", Eval.trace_write);
    ("trace:fun",   Eval.trace_funcall);
    ("trace:prim",  Eval.trace_primop);
    ("trace:instr", Eval.trace_instruction);
    ("eval:concrete_unknown", Value.concrete_unknown);
    ("dis:vectors", Symbolic.use_vectoriser);
    ("dis:check_rasl", Dis.check_rasl);
]

let set_flag s =
    let plus = Utils.startswith s "+" in
    let minus = Utils.startswith s "-" in
    if not (plus || minus) then
        raise @@ Arg.Bad "flag should start with + to set and - to unset";
    let flags_str = String.concat ", " @@ List.map fst (StringMap.bindings flags) in
    let flag = Utils.stringDrop 1 s in

    match StringMap.find_opt flag flags with
    | None -> raise @@ Arg.Bad (Printf.sprintf "unknown flag '%s'\navailable flags: %s" flag flags_str);
    | Some f -> f := plus

let get_flags () =
    StringMap.map (fun x -> !x) flags

let set_flags xs =
    StringMap.iter (fun k v -> StringMap.find k flags := v) xs;

