(****************************************************************
 * Generic utility functions
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** Generic utility functions *)

let rec mkdir_p p =
    let open Filename in
    if Sys.file_exists p then
        ()
    else begin
        (* make parents, then make final directory. *)
        mkdir_p (dirname p);
        if Sys.file_exists p then ()
        else Sys.mkdir p 0o755
    end


(****************************************************************
 * Pretty-printer related
 ****************************************************************)

let to_string (d: PPrint.document): string =
    let buf = Buffer.create 100 in
    (* PPrint.ToBuffer.pretty 100.0 80 buf d; *)
    PPrint.ToBuffer.compact buf d;
    Buffer.contents buf


(****************************************************************
 * List related
 ****************************************************************)

let rec take (n: int) (xs: 'a list) =
    match xs with
    | _ when n < 0 -> failwith "take: negative"
    | l when n = 0 -> []
    | [] -> failwith "take: list too short"
    | x::rest -> x :: take (n-1) rest

let rec drop (n: int) (xs: 'a list) =
    match xs with
    | _ when n < 0 -> failwith "drop: negative"
    | l when n = 0 -> l
    | [] -> failwith "drop: list too short"
    | _::rest -> drop (n-1) rest

let rec chunks (n: int) (xs: 'a list): 'a list list =
    take n xs :: (chunks n (drop n xs))

let nub (xs: 'a list): 'a list =
    let rec nub_aux seen xs = (match xs with
        | [] -> seen
        | (y::ys) -> if List.mem y seen then nub_aux seen ys else nub_aux (y::seen) ys
    ) in
    nub_aux [] xs

let zip_list (xs: 'a list) (ys: 'b list): ('a * 'b) list =
    List.map2 (fun x y -> (x, y)) xs ys

let zipWithIndex (f: 'a -> int -> 'b) (xs: 'a list): 'b list =
    let rec aux i xs = (match xs with
        | [] -> []
        | (y::ys) -> f y i :: aux (i+1) ys
    ) in
    aux 0 xs

(** Generate range of numbers from i to j *)
let range (i: int) (j: int): 'a list =
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux (j - 1) [] ;;

let rec iter3 (f: 'a -> 'b -> 'c -> unit) (xs: 'a list) (ys: 'b list) (zs: 'c list): unit =
    match (xs, ys, zs) with
    | ([], [], []) -> ()
    | ((x::xs), (y::ys), (z::zs)) -> f x y z; iter3 f xs ys zs
    | _, _, _ -> invalid_arg "Utils.iter3: list lengths differ."

let rec map3 (f: 'a -> 'b -> 'c -> 'd) (xs: 'a list) (ys: 'b list) (zs: 'c list): 'd list =
    match (xs, ys, zs) with
    | ([], [], []) -> []
    | ((x::xs), (y::ys), (z::zs)) -> (f x y z) :: (map3 f xs ys zs)
    | _, _, _ -> invalid_arg "Utils.map3: list lengths differ."

let rec nth_modify (f: 'a -> 'a) (n: int) (xs: 'a list): 'a list =
    match n, xs with
    | n, _ when n < 0 -> invalid_arg "nth_modify: negative index"
    | _, [] -> raise Not_found
    | 0, x::rest -> f x :: rest
    | n, x::rest -> x :: nth_modify f (n-1) rest

(** All elements of a list except the last *)
let rec butlast l =
  match l with
  | [] -> []
  | [e] -> []
  | e::es -> e::(butlast es)

let rec getlast l =
  match l with
  | [] -> invalid_arg "getlast"
  | [e] -> ([],e)
  | e::es -> let (es,l) = getlast es in (e::es,l)

(****************************************************************
 * Option related
 ****************************************************************)

let isNone (ox : 'a option): bool =
    (match ox with
    | None   -> true
    | Some _ -> false
    )

let map_option (f: 'a -> 'b) (ox: 'a option): 'b option =
    (match ox with
    | None -> None
    | Some x -> Some (f x)
    )

let get_option (ox: 'a option): 'a =
    (match ox with
    | None -> raise Not_found
    | Some x -> x
    )

let from_option (ox: 'a option) (d: unit -> 'a): 'a =
    (match ox with
    | None -> d()
    | Some x -> x
    )

let bind_option (ox: 'a option) (f: 'a -> 'b option): 'b option =
    (match ox with
    | None   -> None
    | Some x -> f x
    )

let orelse_option (ox: 'a option) (f: unit -> 'a option): 'a option =
    (match ox with
    | None   -> f()
    | Some _ -> ox
    )

let rec concat_option (oss: (('a list) option) list): ('a list) option =
    (match oss with
    | [] -> Some []
    | None::_ -> None
    | (Some xs)::xss -> map_option (List.append xs) (concat_option xss)
    )

(* extract all non-None elements from a list *)
let flatten_option (os: ('a option) list): 'a list =
    let rec aux r os = (match os with
    | [] -> List.rev r
    | Some o :: os' -> aux (o::r) os'
    | None   :: os' -> aux r      os'
    )
    in
    aux [] os

(* extract all non-None elements from a list *)
let flatmap_option (f: 'a -> 'b option) (xs: 'a list): 'b list =
    let rec aux r xs = (match xs with
    | [] -> List.rev r
    | x :: xs' ->
            (match f x with
            | Some b -> aux (b::r) xs'
            | None   -> aux r      xs'
            )
    )
    in
    aux [] xs

(* todo: give this a better name *)
let flatten_map_option (f: 'a -> 'b option) (xs: 'a list): 'b list option =
    let rec aux r xs = (match xs with
    | [] -> Some (List.rev r)
    | x :: xs' ->
            (match f x with
            | Some b -> aux (b::r) xs'
            | None   -> None
            )
    )
    in
    aux [] xs

(* find first non-None result from function 'f' on list 'xs' *)
let rec first_option (f: 'a -> 'b option) (xs: 'a list): 'b option =
    (match xs with
    | [] -> None
    | x :: xs' ->
            (match f x with
            | Some b -> Some b
            | None   -> first_option f xs'
            )
    )

(** Replaces the first non-None result from f on the list with
    the result of the function. *)
let rec replace_in_list (f: 'a -> 'a option) (xs: 'a list): 'a list =
    match xs with
    | [] -> raise Not_found
    | x::xs' ->
        (match f x with
        | Some y -> y::xs'
        | None -> x::replace_in_list f xs')


(****************************************************************
 * String related
 ****************************************************************)

(** Test whether 'x' starts with (is prefixed by) 'y' *)
let startswith (x: string) (y: string): bool =
    let lx = String.length x in
    let ly = String.length y in
    if lx < ly then begin
        false
    end else begin
        let head = String.sub x 0 ly in
        String.equal head y
    end

(** Test whether 'x' ends with (is suffixed by) 'y' *)
let endswith (x: string) (y: string): bool =
    let lx = String.length x in
    let ly = String.length y in
    if lx < ly then begin
        false
    end else begin
        let tail = String.sub x (lx - ly) ly in
        String.equal tail y
    end

(** Drop first n characters from string *)
let stringDrop (n: int) (s: string): string =
    let l = String.length s in
    if n > l then begin
        ""
    end else begin
        String.sub s n (l-n)
    end

let pp_unit () = "()"

let pp_list f xs = Printf.sprintf "[%s]" (String.concat " ; " (List.map f xs))

let pp_pair l r (x,y) = Printf.sprintf "(%s, %s)" (l x) (r y)

let pp_option f a =
  match a with
  | Some v -> "Some(" ^ f v ^ ")"
  | _ -> "None"

(****************************************************************
 * End
 ****************************************************************)
