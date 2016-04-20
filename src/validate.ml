(*
 * Description : Validate.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

open Exceptions
open Sig_abs
open Errors
open Clk_model
open Clk_drivers

let reset_input_handle ftype fname =
		Input_handle.init {
		Input_handle.h_line = "";
		Input_handle.h_lineno = 0;
		Input_handle.h_pos = 0;
		Input_handle.h_out_channel = stderr;
		Input_handle.h_file = (ftype,fname);
	}

(** clock validation *)
let clk_validate (fi:string) (fo:string) =
	let in_ch_src = open_in fi in
	let in_ch_cmp = open_in fo in
  let lexbuf_src = Lexing.from_channel in_ch_src in
	let lexbuf_cmp = Lexing.from_channel in_ch_cmp in
	try
		(** reset id counter *)
		Id_counter.init_newvar_id ();
		Id_counter.init_newunint_id ();
		Id_counter.init_newconstant_id ();
		Id_counter.init_formula_id ();
		
		(** source file parsing *)
		reset_input_handle Input_handle.SOURCE_CODE fi;
		
  	let (procl_src,ptree_src) = Sig_parser.interpret Sig_lexer.token lexbuf_src in
		Parsing.clear_parser();
		close_in in_ch_src;
		
		(** compiled file parsing *)
		reset_input_handle Input_handle.COMPILED_CODE fo;
		
		let (procl_cmp,ptree_cmp) = Sig_parser.interpret Sig_lexer.token lexbuf_cmp in
		Parsing.clear_parser();
		close_in in_ch_cmp;
		
		(** print parsing result if debug mode is on *)
		if (current_debug ()) then 
			begin 
				let oc = open_out "debug.output" in
				let tproc = List.hd procl_cmp in
				(** test translate *)
				List.iter (fun sig_stm ->
									 let (c,nv) = (statement_to_yciesformula (CMP_FILE) (tproc.name) (tproc.paramenters) (tproc.inputs) (tproc.outputs) (tproc.locals) (tproc.typedefs) sig_stm) in
									 Buffer.output_buffer oc (yices_expr_to_buff c);
									 Printf.fprintf oc "\n") tproc.equations;
				List.iter (fun sig_stm ->
									 let (c,nv) = (statement_to_yciesformula (SRC_FILE) (tproc.name) (tproc.paramenters) (tproc.inputs) (tproc.outputs) (tproc.locals) (tproc.typedefs) sig_stm) in
									 Buffer.output_buffer oc (yices_expr_to_buff c);
									 Printf.fprintf oc "\n") tproc.equations;
				close_out oc
			end
		else ();
		
		(** construct clock models *)
	  (** print checking formula into file and call the prover *)

		0
	with Parsing.Parse_error ->
		display_error
				(Input_handle.curfile())
				(Input_handle.curlineno() + 1)
				(Input_handle.curline())
				(Input_handle.curoutchannel())
				"Parse error";
		close_in in_ch_src;
		close_in in_ch_cmp;
		-1

(** data dependence validation *)
let dep_validate (fi:string) (fo:string) =
	0

(** value-graph validation *)
let equ_validate (fi:string) (fo:string) =
	0
