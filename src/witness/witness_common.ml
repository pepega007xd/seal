(** Common functions for witness generators. *)

let current_time () =
  let time = Unix.time () |> Unix.gmtime in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02dZ"
    (time.tm_year + 1900) (* years since 1900 *)
    (time.tm_mon + 1) (* months 0..11 *)
    time.tm_mday time.tm_hour time.tm_min time.tm_sec

let get_uuid () =
  Uuidm.v4_gen (Random.get_state ()) ()
  |> Uuidm.to_string

let get_data_model () =
  match Machine.sizeof_ptr () with
  | 4 -> "ILP32"
  | 8 -> "LP64"
  | _ -> Common.fail "unsupported machdep for sv-witnesses: %s" (Machine.machdep_name ())


let get_architecture () =
  match Machine.sizeof_ptr () with
  | 4 -> "32bit"
  | 8 -> "64bit"
  | _ -> Common.fail "unsupported machdep for sv-witnesses: %s" (Machine.machdep_name ())

let get_files_with_hashes () =
  let open File in
  let f file =
    let path = match file with
      | NeedCPP (path, _, _, _) -> path
      | NoCPP path -> path
      | External (path, _) -> path
    in
    let path_str = Filepath.to_string_abs path in
    let file = open_in path_str in
    let hash = Sha256.input file |> Sha256.to_hex in
    close_in file;
    (path_str, hash)
  in
  List.map f (File.get_all ())
