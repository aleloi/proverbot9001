#!/usr/bin/env bash

eval "OPAMSWITCH='coq-8.12'; export OPAMSWITCH;
OPAM_SWITCH_PREFIX='/root/.opam/coq-8.12'; export OPAM_SWITCH_PREFIX;
CAML_LD_LIBRARY_PATH='/root/.opam/coq-8.12/lib/stublibs:/root/.opam/coq-8.12/lib/ocaml/stublibs:/root/.opam/coq-8.12/lib/ocaml'; export CAML_LD_LIBRARY_PATH;
OCAML_TOPLEVEL_PATH='/root/.opam/coq-8.12/lib/toplevel'; export OCAML_TOPLEVEL_PATH;
MANPATH=':/root/.opam/coq-8.12/man'; export MANPATH;
PATH='/root/.opam/coq-8.12/bin:/root/.local/bin:/root/.opam/default/bin:/root/.opam/default/bin:/root/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin'; export PATH;"
make -j16 -C mathcomp
