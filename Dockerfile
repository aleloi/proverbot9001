FROM ubuntu:22.04
USER root
RUN apt update
RUN apt install -y git opam graphviz libgraphviz-dev libpython3-all-dev build-essential curl openssh-client python3.10-venv python3-pip

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



ENV PATH="${PATH}:/root/.cargo/bin"
RUN rustup toolchain install nightly










#RUN python3 -m pip install --user -r requirements.txt
#RUN pip3 install -e coq_serapy


#RUN which rustup
#RUN echo ${PATH}
# RUN ls $HOME/.cargo/bin/rustup
# RUN ls /.cargo/bin/rustup


#RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup-installer.sh
#RUN sh ./rustup-installer.sh -y
# RUN . "$HOME/.cargo/env"
# RUN cat "$HOME/.cargo/env"

COPY requirements.txt /usr/src/myapp/
WORKDIR /usr/src/myapp

RUN python3 -m venv ./
#RUN . bin/activate

RUN . bin/activate && pip install -r requirements.txt


COPY . /usr/src/myapp

# These take a long time, hence moving here:
RUN git submodule init
RUN git submodule update


RUN . bin/activate && pip install -e coq_serapy

RUN . bin/activate && (cd dataloader/dataloader-core && maturin develop -r)



#RUN pwd  # /usr/src/myapp
#RUN ls
# RUN curl -o data/polyarg-weights.dat https://proverbot9001.ucsd.edu/downloads/weights-latest.dat
#COPY polyarg-weights.dat ./data/polyarg-weights.dat
COPY coq_serapy_init.py coq_serapy/src/coq_serapy/__init__.py
# COPY mathcomp-files.txt mathcomp-files.txt
COPY make_mathcomp.sh coq-projects/math-comp/make.sh
COPY mathcomp_scrape.sh coq-projects/math-comp/scrape.sh
# RUN ls /root/.opam -alh
ENV PATH="${PATH}:/root/.opam/coq-8.12"
# RUN (cd coq-projects/math-comp && git log)
RUN (cd coq-projects/math-comp && bash make.sh)
# RUN (cd coq-projects/math-comp && bash scrape.sh)

COPY ./run-all-mathcomp.sh .
CMD ["./run-all-mathcomp.sh"]
