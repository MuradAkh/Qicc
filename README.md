# Check if a Program is well structured

## Prerequisites

#### Running

Basic Prerequisites 

    ocaml v4.05 (not higher)
    ocamlbuild
    ocaml-findlib
    opam

Install and compile CIL (**warning** - does not work with the version availible in opam)

    git clone https://github.com/cil-project/cil
    cd cil
    ./configure --prefix=`opam config var prefix`
    make
    make install

#### Testing

Basic Prerequisites 

    nodejs
    npm

Installing on Ubuntu 16.04 or higher:

    sudo apt update
    sudo apt install nodejs npm

After installing, navigate to the project directory and run

    npm install

## Compiling and Running

Run the cheker, target functions must located be in `file.c`
<!-- CFG: -->
    make countCFG
    make run-countCFG

<!-- AST (naiive aproach):

    make countAST
    make run-countAST -->

## Testing

    npm test
