countAST: src/countAST.ml
	ocamlbuild -Is src -use-ocamlfind -package cil countAST.cma countAST.cmxs

extractLoop: src/countAST.ml
	ocamlbuild -Is src -use-ocamlfind -package cil extractLoop.cma extractLoop.cmxs

extractMLC: src/countAST.ml tututil findLoops
	ocamlbuild -Is src -use-ocamlfind -package cil extractMLC.cma extractMLC.cmxs

countCFG: src/countCFG.ml 
	ocamlbuild -Is src -use-ocamlfind -package cil countCFG.cma countCFG.cmxs

countCFGnested: src/countCFGnested.ml findLoops
	ocamlbuild -Is src -use-ocamlfind -package cil countCFGnested.cma countCFGnested.cmxs

findLoops: src/findLoops.ml
	ocamlbuild -Is src -use-ocamlfind -package cil findLoops.cma findLoops.cmxs

tututil: src/tututil.ml
	ocamlbuild -Is src -use-ocamlfind -package cil tututil.cma tututil.cmxs

findFuncs: src/findFuncs.ml tututil
	ocamlbuild -Is src -use-ocamlfind -package cil findFuncs.cma findFuncs.cmxs

run-findFuncs: 
	cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/findFuncs.cmxs  output.c 

run-countAST: 
	cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/countAST.cmxs  file.c 

run-countCFG:  
	cilly --gcc=/usr/bin/gcc-6 --load=_build/src/countCFG.cmxs  file.c 

run-countCFGnested: 
	cilly --gcc=/usr/bin/gcc-6 --load=_build/src/countCFGnested.cmxs  file.c 

run-extractLoop: 
		cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/extractLoop.cmxs file.c 
		cat file.cil.c | grep -v '^#line' >| output.c

run-extractMLC: 
		cilly --gcc=/usr/bin/gcc-6 --save-temps --load=_build/src/extractMLC.cmxs  file.c 
		cat file.cil.c | grep -v '^#line' >| output.c

clean:
	rm a.out *.cil.c *.cil.i *.i *.o 