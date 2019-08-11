FROM akabe/ocaml:ubuntu16.04_ocaml4.02.3

RUN sudo apt-get update
RUN sudo apt-get install --yes nodejs npm
RUN sudo apt-get --yes install ocaml-findlib
RUN sudo apt-get --yes install git
RUN sudo opam install ocamlbuild
RUN ln -s /usr/bin/nodejs /usr/bin/node

# RUN sudo apk add perl
# RUN sudo apk add git

RUN git clone https://github.com/cil-project/cil && \
    cd cil && \
    ./configure --prefix=`opam config var prefix` && \
    make && \
    make install

RUN sudo apt-get --yes install software-properties-common && sudo apt-get update
RUN sudo add-apt-repository ppa:ubuntu-toolchain-r/test && \
    sudo apt-get update
RUN sudo apt-get --yes install gcc-6
RUN sudo npm install -g n
RUN sudo n latest