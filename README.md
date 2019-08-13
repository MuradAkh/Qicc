# Incremental Assertions Prover

[![CircleCI](https://circleci.com/gh/MuradAkh/WellStructured.svg?style=svg)](https://circleci.com/gh/MuradAkh/WellStructured)

## Prerequisites

#### CIL Modules

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

#### CIL Module Tests and Verification tool

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

Finding Local and non-Local loops:

    make countCFGnested
    make run-countCFGnested

Extracting MLCs:

    make extractMLC
    make run-extractMLC

Verification Tool:

    make extractMLC
    make findFuncs
    npm run verify -- --file <filename.c>


## Testing

    npm test
