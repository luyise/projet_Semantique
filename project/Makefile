# Cours "Semantics and applications to verification"
#
# Marc Chevalier 2018
# Ecole normale supérieure, Paris, France / CNRS / INRIA

# Feel free to change it

RESULT = main.exe

OCAMLYACC = menhir
YFLAGS = --explain --table
SOURCES = \
    libs/mapext.mli libs/mapext.ml \
    domains/value_domain.ml \
    domains/domain.ml \
    frontend/lexer.mll frontend/parser.mly \
    frontend/cfg.ml frontend/cfg_printer.ml \
    frontend/abstract_syntax_tree.ml frontend/tree_to_cfg.ml \
		frontend/parser_messages.ml \
    frontend/file_parser.ml frontend/file_parser.mli \
    iterator/iterator.ml \
    main.ml


PACKS = zarith menhirLib
LIBS = zarith
OCAMLBLDFLAGS = -I $(shell ocamlfind query zarith) -I $(shell ocamlfind query menhirLib) -g
OCAMLFLAGS = -w +a-4-9 -g

all: messages native-code

clean2:
	@rm -f *.cmi */*.cmi
	@rm -f *.cmo */*.cmo
	@rm -f *.o */*.o
	@rm -f *.cmx */*.cmx

messages: frontend/parser.messages
	$(OCAMLYACC) $(YFLAGS) frontend/parser.mly --compile-errors frontend/parser.messages > frontend/parser_messages.ml

.PHONY: messages

OCAMLMAKEFILE = OCamlMakefile
include $(OCAMLMAKEFILE)
