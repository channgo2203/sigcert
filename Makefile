###########################################################################
#                              SigCert Makefile
#                  Copyright (C) 2012-2013  Chan Ngo
#
#
###########################################################################

OCAMLMAKEFILE = OCamlMakefile

SOURCES = src/errors.ml src/errors.mli \
          src/exceptions.ml src/exceptions.mli \
          src/input_handle.ml src/input_handle.mli \
          src/id_counter.ml src/id_counter.mli \
          src/hashtbls.ml src/hashtbls.mli \
          src/ptree.ml src/ptree.mli \
          src/sig_abs.ml src/sig_abs.mli \
          src/clk_model.ml src/clk_model.mli \
          src/vg_types.ml src/vg_types.mli \
          src/c_abs.ml src/c_abs.mli \
          src/sig_lexer.mll \
          src/sig_parser.mly \
          src/clk_drivers.ml src/clk_drivers.mli \
          src/dep_graph.ml src/dep_graph.mli \
          src/dep_drivers.ml src/dep_drivers.mli \
          src/vg_rules.ml src/vg_rules.mli \
          src/vg_graph.ml src/vg_graph.mli \
          src/vg_c_graph.ml src/vg_c_graph.mli \
          src/vg_drivers.ml src/vg_drivers.mli \
          src/solver_yices.ml src/solver_yices.mli \
          src/validate.ml src/validate.mli \
          src/sigcert.ml 

RESULT = sigcert

LIBS = str unix

# to ingtegrate the ocamlgraph library
#LIBS = str unix graph

#INCDIRS = lib/ocamlgraph

#LIBDIRS = lib/ocamlgraph

YFLAGS = -v

all: native-code

-include $(OCAMLMAKEFILE)
