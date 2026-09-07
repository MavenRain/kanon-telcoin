module T = Kanon_telcoin

let ( let* ) = Result.bind

let json_string (text : string) : string =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun ch ->
      match ch with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c ->
          if Char.code c < 32 then
            Buffer.add_string buffer (Printf.sprintf "\\u%04x" (Char.code c))
          else Buffer.add_char buffer c)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let integer text =
  (if String.length text > 128 then None
   else Kanon_kernel.Bignum.of_decimal text)
  |> Option.to_result ~none:("invalid integer: " ^ text)

let frontend entry source =
  T.Frontend.compile ~entry source
  |> Result.map_error T.Frontend.error_to_string

let compile entry bound_text source =
  let* bound = integer bound_text in
  let* expr = frontend entry source in
  let* artifact = T.Evm.compile ~bound expr in
  Ok
    (Printf.sprintf
       "{\"creationBytecode\":%s,\"runtimeBytecode\":%s,\"sourceMap\":%s}"
       (json_string ("0x" ^ artifact.creation_hex))
       (json_string ("0x" ^ artifact.runtime_hex))
       artifact.source_map_json)

let evaluate entry state_text source =
  let* state = integer state_text in
  let* () =
    if Z.gt state T.Contract_ir.max_word then Error "input state is outside uint256"
    else Ok ()
  in
  let* expr = frontend entry source in
  let* value =
    T.Contract_ir.eval state expr
    |> Result.map_error (function
         | T.Contract_ir.Intermediate_overflow -> "intermediate word overflow")
  in
  Ok (Printf.sprintf "{\"value\":%s}" (json_string (Z.to_string value)))

let run args source =
  match args with
  | [ _; entry; bound ] -> compile entry bound source
  | [ _; "--eval"; entry; state ] -> evaluate entry state source
  | [] | [ _ ] | [ _; _ ] | [ _; _; _; _ ]
  | _ :: _ :: _ :: _ :: _ :: _ ->
      Error "usage: main.exe ENTRY BOUND < source.kan | main.exe --eval ENTRY STATE < source.kan"

let () =
  let source = In_channel.input_all stdin in
  run (Array.to_list Sys.argv) source
  |> Result.fold
       ~ok:print_endline
       ~error:(fun message -> prerr_endline ("kanonc: " ^ message); exit 2)
