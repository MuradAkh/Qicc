countAST: countAST.ml
	ocamlbuild -use-ocamlfind -package cil countAST.cma countAST.cmxs

countCFG: countCFG.ml
	ocamlbuild -use-ocamlfind -package cil countCFG.cma countCFG.cmxs

countCFGnested: countCFGnested.ml
	ocamlbuild -use-ocamlfind -package cil countCFGnested.cma countCFGnested.cmxs

run-countAST: countAST
	cilly --gcc=/usr/bin/gcc-6 --load=_build/countAST.cmxs  file.c 

run-countCFG: countCFG 
	cilly --gcc=/usr/bin/gcc-6 --load=_build/countCFG.cmxs  file.c 

run-countCFGnested: countCFGnested
	cilly --gcc=/usr/bin/gcc-6 --load=_build/countCFGnested.cmxs  file.c 

clean:
	rm -rf _build
	rm a.out
