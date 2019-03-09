.PHONY: pack all run clean
GENERATED=src/parser.mli src/parser.ml src/lexer.ml
SOURCE=deducer.ml
OCAMLC=ocamlc str.cma #ocamlopt for speed
PACKAGE=hw3.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run: main.exe
	./main.exe

compParser:
	cd src && $(OCAMLC) $(GENERATED:src/%=%)

compTree:
	cd src && $(OCAMLC) -c tree.ml

compSource:
	cd src && $(OCAMLC) -c $(SOURSE)

main.exe: $(GENERATED) compTree compParser compSource
	cd src && $(OCAMLC) tree.ml $(GENERATED:src/%=%) $(SOURCE) main.ml -o ../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src proofs

$(GENERATED): src/lexer.mll src/parser.mly
	ocamllex src/lexer.mll 
	ocamlyacc src/parser.mly

clean:
	cd src && $(DEL) $(GENERATED:src/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)