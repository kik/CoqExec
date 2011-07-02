STAMP = ../../src/.stamp

all: extract .gitignore

$(STAMP):
	$(MAKE) -C ../../src

extract: Extract.vo

Extract.vo: Extract.v $(STAMP)
	coqc -R ../../src/coq CoqExec Extract

.PHONY: $(STAMP)

EXTRACTED = \
  Peano.mli Peano.ml \
  Logic.mli Logic.ml \
  Specif.mli Specif.ml \
  Datatypes.mli Datatypes.ml \
  BinPos.mli BinPos.ml \
  Operator.mli Operator.ml \
  Primitive.mli Primitive.ml \
  Prelude.mli Prelude.ml

.gitignore:
	ls $(EXTRACTED) >$@

clean::
	rm -f *.vo *.glob $(EXTRACTED)

SOURCES = $(EXTRACTED)
RESULT = libcoqexec
all: native-code-library

OCAMLMAKEFILE = /usr/share/ocamlmakefile/OCamlMakefile
include $(OCAMLMAKEFILE)
