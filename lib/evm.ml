type artifact = {
  creation_hex : string;
  runtime_hex : string;
  source_map_json : string;
}

let ( let* ) = Result.bind

type instruction =
  | Op of int
  | Push of Z.t
  | Push_label of string
  | Mark of string
  | Raw of string

type node_span = { node : int; form : string; first : string; last : string }

type builder = {
  reversed : instruction list;
  size : int;
  next_temp : int;
  next_node : int;
  nodes : node_span list;
}

let runtime_limit = 24_576
let creation_limit = 49_152
let event_topic =
  Z.of_string
    "0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84"

let empty = { reversed = []; size = 0; next_temp = 1; next_node = 0; nodes = [] }
let word n = Push (Z.of_int n)
let jump name = [ Push_label name; Op 0x56 ]
let jump_if name = [ Push_label name; Op 0x57 ]
let destination name = [ Mark name; Op 0x5b ]
let load offset = [ word offset; Op 0x51 ]
let save offset = [ word offset; Op 0x52 ]

let push_encoding value =
  if Z.sign value < 0 || Z.gt value Contract_ir.max_word then
    Error "EVM PUSH literal lies outside uint256"
  else if Z.equal value Z.zero then Ok "5f"
  else
    let digits = Z.format "%x" value in
    let data = if String.length digits mod 2 = 0 then digits else "0" ^ digits in
    Ok (Printf.sprintf "%02x%s" (0x5f + (String.length data / 2)) data)

let valid_hex hex =
  String.length hex mod 2 = 0
  && String.for_all
       (function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false)
       hex

let static_encoding = function
  | Op opcode ->
      if opcode >= 0 && opcode <= 255 then Ok (Printf.sprintf "%02x" opcode)
      else Error "EVM opcode lies outside a byte"
  | Push value -> push_encoding value
  | Raw hex ->
      if valid_hex hex then Ok hex else Error "EVM raw bytecode is malformed"
  | Mark _ -> Ok ""
  | Push_label _ -> Error "EVM label needs assembler resolution"

let instruction_size = function
  | Push_label _ -> Ok 3
  | instruction ->
      let* encoded = static_encoding instruction in
      Ok (String.length encoded / 2)

let emit ?(limit = runtime_limit) state instructions =
  let* added =
    List.fold_left
      (fun count instruction ->
        let* count = count in
        let* size = instruction_size instruction in
        Ok (count + size))
      (Ok 0) instructions
  in
  if state.size + added > limit then Error "EVM artifact exceeds its bytecode size limit"
  else
    Ok
      {
        state with
        reversed = List.rev_append instructions state.reversed;
        size = state.size + added;
      }

let assemble instructions =
  let* _, labels =
    List.fold_left
      (fun result instruction ->
        let* position, labels = result in
        match instruction with
        | Mark name ->
            if List.mem_assoc name labels then Error ("Duplicate EVM label: " ^ name)
            else Ok (position, (name, position) :: labels)
        | Op _ | Push _ | Push_label _ | Raw _ ->
            let* size = instruction_size instruction in
            Ok (position + size, labels))
      (Ok (0, [])) instructions
  in
  let* encoded =
    List.fold_left
      (fun result instruction ->
        let* encoded = result in
        let* fragment =
          match instruction with
          | Push_label name ->
              let* position =
                Option.to_result ~none:("Unknown EVM label: " ^ name)
                  (List.assoc_opt name labels)
              in
              if position > 65_535 then Error "EVM label exceeds PUSH2 address space"
              else Ok (Printf.sprintf "61%04x" position)
          | Op _ | Push _ | Mark _ | Raw _ -> static_encoding instruction
        in
        Ok (fragment :: encoded))
      (Ok []) instructions
  in
  Ok (String.concat "" (List.rev encoded), labels)

let validate_expression expression =
  let rec visit count = function
    | [] -> Ok ()
    | (expression, depth) :: rest ->
        if count >= 1_024 then Error "EVM expression exceeds 1024 nodes"
        else if depth > 256 then Error "EVM expression exceeds nesting depth 256"
        else
          match expression with
          | Contract_ir.State -> visit (count + 1) rest
          | Contract_ir.Const value ->
              if Z.sign value < 0 || Z.gt value Contract_ir.max_word then
                Error "EVM constant lies outside uint256"
              else visit (count + 1) rest
          | Contract_ir.Add (left, right)
          | Contract_ir.Sub (left, right)
          | Contract_ir.Mul (left, right) ->
              visit (count + 1) ((left, depth + 1) :: (right, depth + 1) :: rest)
  in
  visit 0 [ (expression, 0) ]

let form = function
  | Contract_ir.State -> "State"
  | Contract_ir.Const _ -> "Const"
  | Contract_ir.Add _ -> "Add"
  | Contract_ir.Sub _ -> "Sub"
  | Contract_ir.Mul _ -> "Mul"

let rec expression_code state expression =
  let node = state.next_node in
  let first = Printf.sprintf "expression_%d_start" node in
  let last = Printf.sprintf "expression_%d_end" node in
  let state =
    {
      state with
      next_node = node + 1;
      nodes = { node; form = form expression; first; last } :: state.nodes;
    }
  in
  let* state = emit state [ Mark first ] in
  let* state =
    match expression with
    | Contract_ir.State -> emit state [ word 1; Op 0x54 ]
    | Contract_ir.Const value -> emit state [ Push value ]
    | Contract_ir.Add (left, right)
    | Contract_ir.Sub (left, right)
    | Contract_ir.Mul (left, right) ->
        let left_slot = state.next_temp * 32 in
        let right_slot = left_slot + 32 in
        let result_slot = left_slot + 64 in
        let state = { state with next_temp = state.next_temp + 3 } in
        let* state = expression_code state left in
        let* state = emit state (save left_slot) in
        let* state = expression_code state right in
        let* state = emit state (save right_slot) in
        let ready = Printf.sprintf "expression_%d_ready" node in
        let zero = Printf.sprintf "expression_%d_zero" node in
        (match expression with
        | Contract_ir.Add _ ->
            emit state
              (load left_slot @ load right_slot @ [ Op 0x01 ] @ save result_slot
             @ load left_slot @ load result_slot @ [ Op 0x10 ]
             @ jump_if "runtime_revert" @ load result_slot)
        | Contract_ir.Mul _ ->
            emit state
              (load left_slot @ load right_slot @ [ Op 0x02 ] @ save result_slot
             @ load left_slot @ [ Op 0x15 ] @ jump_if ready @ load right_slot
             @ load left_slot @ load result_slot @ [ Op 0x04; Op 0x14; Op 0x15 ]
             @ jump_if "runtime_revert" @ destination ready @ load result_slot)
        | Contract_ir.Sub _ ->
            emit state
              (load right_slot @ load left_slot @ [ Op 0x10 ] @ jump_if zero
             @ load right_slot @ load left_slot @ [ Op 0x03 ] @ jump ready
             @ destination zero @ [ word 0 ] @ destination ready)
        | Contract_ir.State | Contract_ir.Const _ ->
            Error "EVM binary expression classification failed")
  in
  emit state [ Mark last ]

let source_map runtime_labels creation_labels nodes =
  let position labels name =
    Option.to_result ~none:("Missing EVM source-map marker: " ^ name)
      (List.assoc_opt name labels)
  in
  let range labels name first last =
    let* first = position labels first in
    let* last = position labels last in
    Ok (Printf.sprintf "{\"kind\":\"declaration\",\"name\":\"%s\",\"start\":%d,\"end\":%d}" name first last)
  in
  let* dispatch = range runtime_labels "dispatch" "dispatch" "dispatch_end" in
  let* getter = range runtime_labels "get" "get" "get_end" in
  let* increment = range runtime_labels "increment" "increment" "increment_end" in
  let* revert = range runtime_labels "revert" "runtime_revert" "runtime_end" in
  let* constructor = range creation_labels "constructor" "constructor" "runtime_data" in
  let* nodes =
    List.fold_left
      (fun result span ->
        let* result = result in
        let* first = position runtime_labels span.first in
        let* last = position runtime_labels span.last in
        Ok
          (Printf.sprintf
             "{\"kind\":\"expression\",\"node\":%d,\"form\":\"%s\",\"start\":%d,\"end\":%d}"
             span.node span.form first last
          :: result))
      (Ok []) nodes
  in
  Ok
    (Printf.sprintf
       "{\"format\":\"gpt17-evm-node-map-v1\",\"granularity\":\"declaration-and-expression-node\",\"pc_unit\":\"byte\",\"range_end\":\"exclusive\",\"source_lines\":null,\"runtime\":[%s],\"creation\":[%s]}"
       (String.concat "," ([ dispatch; getter; increment; revert ] @ nodes)) constructor)

let compile ~bound expression =
  if Z.sign bound < 0 || Z.gt bound Contract_ir.max_word then
    Error "EVM state bound lies outside uint256"
  else
    let* () = validate_expression expression in
    let* state =
      emit empty
        ([ Mark "dispatch"; Op 0x34 ]
        @ jump_if "runtime_revert"
        @ [ Op 0x36; word 4; Op 0x14; Op 0x15 ]
        @ jump_if "runtime_revert"
        @ [ word 0; Op 0x35; word 224; Op 0x1c; Op 0x80; Push (Z.of_string "0x6d4ce63c"); Op 0x14 ]
        @ jump_if "get"
        @ [ Op 0x80; Push (Z.of_string "0xd09de08a"); Op 0x14 ]
        @ jump_if "increment" @ [ Op 0x50 ] @ jump "runtime_revert"
        @ [ Mark "dispatch_end" ] @ destination "get"
        @ [ Op 0x50; word 1; Op 0x54; word 0; Op 0x52; word 32; word 0; Op 0xf3; Mark "get_end" ]
        @ destination "increment"
        @ [ Op 0x50; Op 0x33; word 0; Op 0x54; Op 0x14; Op 0x15 ]
        @ jump_if "runtime_revert")
    in
    let* state = expression_code state expression in
    let* state =
      emit state
        ([ Op 0x80; Push bound; Op 0x10 ] @ jump_if "runtime_revert"
        @ [ Op 0x80; word 1; Op 0x55; word 0; Op 0x52; Push event_topic; word 32; word 0; Op 0xa1;
            word 32; word 0; Op 0xf3; Mark "increment_end" ]
        @ destination "runtime_revert"
        @ [ word 0; word 0; Op 0xfd; Mark "runtime_end" ])
    in
    let* runtime_hex, runtime_labels = assemble (List.rev state.reversed) in
    let runtime_size = String.length runtime_hex / 2 in
    let* constructor =
      emit ~limit:creation_limit empty
        ([ Mark "constructor"; Op 0x34 ] @ jump_if "constructor_revert"
        @ [ Op 0x33; word 0; Op 0x55; word 0; word 1; Op 0x55;
            word runtime_size; Push_label "runtime_data"; word 0; Op 0x39;
            word runtime_size; word 0; Op 0xf3 ]
        @ destination "constructor_revert"
        @ [ word 0; word 0; Op 0xfd; Mark "runtime_data"; Raw runtime_hex ])
    in
    let* creation_hex, creation_labels = assemble (List.rev constructor.reversed) in
    let* source_map_json = source_map runtime_labels creation_labels state.nodes in
    Ok { creation_hex; runtime_hex; source_map_json }
