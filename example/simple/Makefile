COQC = coqc
COQFLAGS = -R ../../src/coq CoqExec
OCAMLOPTFLAGS = -I ../../extraction/ocaml
LIB = ../../extraction/ocaml/libcoqexec.cmxa

all: answer

answer.ml: answer.vo

answer.vo: answer.v
	$(COQC) $(COQFLAGS) $<

%.ml: %.vo
	echo "Extraction Library $(<:.vo=)." | coqtop $(COQFLAGS) -require $(<:.vo=)

%: %.ml
	ocamlopt $(OCAMLOPTFLAGS) -o $@ $(LIB) $(<:.ml=.mli) $<

clean:
	rm -f answer.ml answer.mli *.vo *.glob *.o *.cmi *.cmx
	rm -f answer
