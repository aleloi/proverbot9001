FROM ubuntu:22.04
USER root
RUN apt update
RUN apt install -y software-properties-common
RUN add-apt-repository ppa:avsm/ppa
RUN apt update
RUN apt install -y git opam graphviz libgraphviz-dev libpython3-all-dev build-essentials

# Rustup:
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

COPY . /usr/src/myapp
WORKDIR /usr/src/myapp
RUN make setup
