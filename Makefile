countAST: countAST.ml
	ocamlbuild -use-ocamlfind -package cil countAST.cma countAST.cmxs

countCFG: countCFG.ml
	ocamlbuild -use-ocamlfind -package cil countCFG.cma countCFG.cmxs

run-countAST: countCFG
	cilly --gcc=/usr/bin/gcc-6 --load=_build/countAST.cmxs  file.c 

run-countCFG: countCFG
	cilly --gcc=/usr/bin/gcc-6 --load=_build/countCFG.cmxs  file.c 

clean:
	rm -rf _build
	rm a.out
