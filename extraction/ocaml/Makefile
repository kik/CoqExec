
all: extract

extract: Extract.vo

Extract.vo: Extract.v
	coqc -R ../../src/coq CoqExec Extract

EXTRACTED = \
  Peano.mli Peano.ml \
  Logic.mli Logic.ml \
  Specif.mli Specif.ml \
  Datatypes.mli Datatypes.ml \
  BinPos.mli BinPos.ml \
  Operator.mli Operator.ml \
  Primitive.mli Primitive.ml \
  Prelude.mli Prelude.ml

clean::
	rm -f *.vo *.glob $(EXTRACTED)

SOURCES = $(EXTRACTED)
RESULT = libcoqexec
all: native-code-library

OCAMLMAKEFILE = /usr/share/ocamlmakefile/OCamlMakefile
include $(OCAMLMAKEFILE)
