countAST: src/countAST.ml
	ocamlbuild -Is src -use-ocamlfind -package cil countAST.cma countAST.cmxs

extract: src/countAST.ml
	ocamlbuild -Is src -use-ocamlfind -package cil extract.cma extract.cmxs

countCFG: src/countCFG.ml
	ocamlbuild -Is src -use-ocamlfind -package cil countCFG.cma countCFG.cmxs

countCFGnested: src/countCFGnested.ml
	ocamlbuild -Is src -use-ocamlfind -package cil countCFGnested.cma countCFGnested.cmxs

run-countAST: countAST
	cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/countAST.cmxs  file.c 

run-countCFG: countCFG 
	cilly --gcc=/usr/bin/gcc-6 --load=_build/src/countCFG.cmxs  file.c 

run-countCFGnested: countCFGnested
	cilly --gcc=/usr/bin/gcc-6 --load=_build/src/countCFGnested.cmxs  file.c 

run-extract: extract
		cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/extract.cmxs  file.c 
		cat file.cil.c | grep -v '^#line' > output.c

clean:
	rm -rf _build
	rm a.out file.cil.c file.cil.i file.i file.o
