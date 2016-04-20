(*
 * Description : sigcert.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

open Validate

(* verification mode *)
let mode = ref 0
 
(* input information *)
let src_file = ref ""
let cmp_file = ref ""

(* version information *)
let print_copyright () =
	print_string (
   "\nSigCert\n"
  ^"* Copyright (c) 2012-2013 by Van Chan Ngo.\n"
  ^"* All rights reserved.\n"
  ^"* \n"
  )
	
let start src_file cmp_file =
	begin
		if (String.compare src_file "" <> 0) then
			begin
				if (String.compare cmp_file "" <> 0) then
					begin
						match !mode with
						| 0 -> 
							let res = clk_validate src_file cmp_file in
							if (res == 0) then
								Printf.printf "\nCorrect!\n"
						| _ -> Printf.printf "\nWil be implemented!\n";
					end
				else
					begin
						Printf.printf "\nThere is no compiled file\n";
					end
			end
		else
			begin
				Printf.printf "\nThere is no source file\n";
			end
	end;
	exit 0

(* the entry point *)
let _ = 
	let usage_msg = "Formal Verification for Signal Compiler.\nUsage: sigcert [options] -src= source_file -cmp= compiled_file" in
  let speclist = [
										("-clk",
											Arg.Unit (fun () -> mode := 0),
											": Clock validation"
										);
										("-dep",
											Arg.Unit (fun () -> mode := 1),
											": Data dependency validation"
										);
										("-val",
											Arg.Unit (fun () -> mode := 2),
											": Value-graph validation"
										);
										("-src=",
                    	Arg.String (fun s -> src_file := s),
                    	": The source file name"
                   	);
										("-cmp=",
                    	Arg.String (fun s -> cmp_file := s),
                    	": The compiled file name"
                   	);
										("-debug=",
											Arg.Bool (fun b -> Errors.set_debug b),
											": The debug mode"
										);
		 								("-version",
                      Arg.Unit (fun () -> print_copyright(); exit 0),
                      ": Print version & copyright information"
                   	)
                 ]
	in
  Arg.parse speclist (fun args -> raise (Arg.Bad ("Bad argument : " ^ args))) usage_msg;
	
	start !src_file !cmp_file
