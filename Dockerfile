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
# Ok, actually it doesn't work with this either. I changed all the
# git@github.com: into https://github.com/. Don't want to remove this because
# the next lines take much time.
# RUN ssh-keygen -q -t rsa -N '' -f ~/.ssh/id_rsa

# Allow 'git@github.com'
# RUN ssh-keyscan github.com >> /root/.ssh/known_hosts



# RUN make setup

## Opam stuff from 'src/setup.sh' and 'install_coqgym_deps.sh'
RUN opam init -a --compiler=4.07.1 --disable-sandboxing
RUN eval `opam config env`
RUN opam update
RUN opam switch create coq-8.12 4.07.1
RUN eval $(opam env --switch=coq-8.12 --set-switch)
RUN opam pin add -y coq 8.12.2
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
RUN    opam install -y coq-serapi coq-smpl=8.12 coq-metacoq-template coq-metacoq-checker coq-equations coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-field menhir


RUN apt install -y python3-pip

COPY proverbot9002/ /usr/src/myapp
WORKDIR /usr/src/myapp


# These take a long time, hence moving here:
RUN git submodule init
RUN git submodule update



RUN python3 -m pip install --user -r requirements.txt
RUN python3 -m pip install -e coq_serapy
