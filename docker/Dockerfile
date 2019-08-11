FROM ubuntu:16.04

RUN apt-get update
RUN apt-get install --yes nodejs npm
RUN apt-get install --yes perl ocaml ocaml-findlib opam 
RUN apt-get --yes install git
RUN ln -s /usr/bin/nodejs /usr/bin/node

# RUN sudo apk add perl
# RUN sudo apk add git

RUN git clone https://github.com/cil-project/cil && \
    cd cil && \
    ./configure && \
    make && \
    make install

RUN apt-get --yes install software-properties-common &&  apt-get update
RUN add-apt-repository ppa:ubuntu-toolchain-r/test && \
    apt-get update
RUN apt-get --yes install gcc-6
RUN npm install -g n
RUN n latest

RUN opam init
RUN opam install ocamlbuild

RUN apt-get --yes install cbmc