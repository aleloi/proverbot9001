FROM ubuntu:22.04
USER root
RUN apt update
#RUN apt install -y software-properties-common
#RUN add-apt-repository ppa:avsm/ppa
RUN apt update
RUN apt install -y git opam graphviz libgraphviz-dev libpython3-all-dev build-essential curl openssh-client

# Rustup:
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup-installer.sh
RUN sh ./rustup-installer.sh -y

# Generate SSH key (otherwise git submodule init doesn't work)
RUN ssh-keygen -q -t rsa -N '' -f ~/.ssh/id_rsa

# Allow 'git@github.com'
RUN ssh-keyscan github.com >> /root/.ssh/known_hosts


COPY . /usr/src/myapp
WORKDIR /usr/src/myapp


# These take a long time, hence moving here:
RUN git submodule init
RUN git submodule update

RUN make setup
