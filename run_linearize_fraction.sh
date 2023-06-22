#!/usr/bin/env bash
# ~/opam-scripts/read-opam.sh
eval "OPAMSWITCH='coq-8.12'; export OPAMSWITCH;
OPAM_SWITCH_PREFIX='/root/.opam/coq-8.12'; export OPAM_SWITCH_PREFIX;
CAML_LD_LIBRARY_PATH='/root/.opam/coq-8.12/lib/stublibs:/root/.opam/coq-8.12/lib/ocaml/stublibs:/root/.opam/coq-8.12/lib/ocaml'; export CAML_LD_LIBRARY_PATH;
OCAML_TOPLEVEL_PATH='/root/.opam/coq-8.12/lib/toplevel'; export OCAML_TOPLEVEL_PATH;
MANPATH=':/root/.opam/coq-8.12/man'; export MANPATH;
PATH=$PATH:'/root/.opam/coq-8.12/bin:/root/.local/bin:/root/.opam/default/bin:/root/.opam/default/bin:/root/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin'; export PATH;"
# cd ../../
source ./bin/activate

pip install ~/aleloi_parsing_serapi/

#basename=$( echo $1 | sed s/.v$// )

rm coq-projects/math-comp/mathcomp/algebra/fraction.v.scrape
rm -f coq-projects/math-comp/mathcomp/algebra/fraction.v.lin
rm -f coq-projects/math-comp/mathcomp/algebra/fraction.v.scrape
python ./src/linearize_semicolons.py  --prelude=./coq-projects/math-comp -v mathcomp/algebra/fraction.v --hardfail
cp coq-projects/math-comp/mathcomp/algebra/fraction.v.lin ./
cp coq-projects/math-comp/mathcomp/algebra/fraction.v_after_transform.lin ./
#./src/scrape.py -c --prelude=./coq-projects/math-comp  mathcomp/algebra/fraction.v

# ./src/scrape.py -c --prelude=./ $1

# python ./src/linearize_semicolons.py  -vvvv $1
