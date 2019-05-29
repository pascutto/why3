(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Whyconf
open Theory

let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_attrs = ref false

let option_list =
  let open Getopt in
  NewArgs.common_options @
  [ KLong "list-transforms", Hnd0 (fun () -> opt_list_transforms := true),
    " list known transformations";
    KLong "list-printers", Hnd0 (fun () -> opt_list_printers := true),
    " list known printers";
    KLong "list-provers", Hnd0 (fun () -> opt_list_provers := true),
    " list known provers";
    KLong "list-formats", Hnd0 (fun () -> opt_list_formats := true),
    " list known input formats";
    KLong "list-metas", Hnd0 (fun () -> opt_list_metas := true),
    " list known metas";
    KLong "list-attributes", Hnd0 (fun () -> opt_list_attrs := true),
    " list used attributes";
    KLong "print-libdir", Hnd0 (fun () -> printf "%s@." Config.libdir; exit 0),
    " print location of binary components (plugins, etc)";
    KLong "print-datadir", Hnd0 (fun _ -> printf "%s@." Config.datadir; exit 0),
    " print location of non-binary data (modules, etc)";
    KLong "version",
    Hnd0 (fun _ -> printf "Why3 platform, version %s@." Config.version; exit 0),
    " print version information";
  ]

let command_path = match Config.localdir with
  | Some p -> Filename.concat p "bin"
  | None -> Filename.concat Config.libdir "commands"

let extra_help fmt commands =
  fprintf fmt "Available commands:@\n";
  List.iter (fun (v,_) -> fprintf fmt "  %s@\n" v) commands

let available_commands () =
  let commands = Sys.readdir command_path in
  Array.sort String.compare commands;
  let re = Str.regexp "^why3\\([^.]+\\)\\([.].*\\)?" in
  let commands = Array.fold_left (fun acc v ->
    if Str.string_match re v 0 then
      let w = Str.matched_group 1 v in
      match acc with
      | (h,_)::_ when h = w -> acc
      | _ -> (w, v) :: acc
    else acc) [] commands in
  List.rev commands

let do_usage () =
  Format.printf
    "@[Usage: %s [options] <command> [options]@\n\
     Execute the given subcommand.@\n\
     @\n%s@\n%a@]@?"
    (Filename.basename Sys.argv.(0))
    (Getopt.format option_list)
    extra_help (available_commands ());
  exit 0

let option_list =
  let open Getopt in
  (Key ('h', "help"), Hnd0 do_usage,
   " display this help and exit") ::
  option_list

let arg_index = ref 1

let command sscmd =
  let sscmd,args =
    let cur = !arg_index in
    if sscmd = "help" then begin
      if cur >= Array.length Sys.argv then do_usage ();
      let sscmd = Sys.argv.(cur) in
      sscmd, ["--help"]
    end else begin
      let args = ref [] in
      for i = 1 to Array.length Sys.argv - 1 do
        if i <> cur - 1 then args := Sys.argv.(i) :: !args;
      done;
      sscmd, List.rev !args
    end in
  let cmd =
    let scmd = "why3" ^ sscmd in
    let cmd = Filename.concat command_path scmd in
    if cmd <> "" && Sys.file_exists cmd
    then cmd
    else begin
      let commands = available_commands () in
      let scmd =
        try List.assoc sscmd commands
        with Not_found ->
          eprintf "'%s' is not a Why3 command.@\n@\n%a"
            sscmd extra_help commands;
          exit 1 in
      Filename.concat command_path scmd
    end in
  let scmd = "why3 " ^ sscmd in
  Unix.execv cmd (Array.of_list (scmd :: args))

let () = try
  let nargs = Array.length Sys.argv in
  while !arg_index < nargs do
    Getopt.parse_one ~mm:false option_list command Sys.argv arg_index;
  done;
  let config,_,_ = NewArgs.complete_initialization () in

  (* listings *)

  let sort_pair (x,_) (y,_) = String.compare x y in
  let opt_list = ref false in
  if !opt_list_transforms then begin
    opt_list := true;
    let print_trans_desc fmt (x,r) =
      fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r in
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms_l ()));
    let list_transform_with_arg =
      Trans.list_transforms_with_args () @
      Trans.list_transforms_with_args_l () in
    printf "@[<hov 2>Known transformations with arguments:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair list_transform_with_arg)
  end;
  if !opt_list_printers then begin
    opt_list := true;
    let print_printer_desc fmt (s,f) =
      fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" s Pp.formatted f in
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_printer_desc)
      (List.sort sort_pair (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l, f) =
      fprintf fmt "@[%s [%a]@\n  @[%a@]@]"
        p (Pp.print_list Pp.comma print1) l
        Pp.formatted f
    in
    printf "@[Known input formats:@\n  @[%a@]@]@."
      (Pp.print_list Pp.newline2 print)
      (List.sort Pervasives.compare (Env.list_formats Env.base_language))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let print = Pp.print_iter2 Mprover.iter Pp.newline Pp.nothing
      print_prover Pp.nothing in
    let provers = get_provers config in
    printf "@[<hov 2>Known provers:@\n%a@]@." print provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[<h 2>%s %s%a@\n@[<hov>%a@]@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "(flag) " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
      Pp.formatted m.meta_desc
    in
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print) (List.sort cmp (Theory.list_metas ()))
  end;
  if !opt_list_attrs then begin
    opt_list := true;
    let l = List.sort String.compare (Ident.list_attributes ()) in
    List.iter (fun x -> Format.eprintf "%s@." x) l
  end;
  if !opt_list then exit 0;

  do_usage ();

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
