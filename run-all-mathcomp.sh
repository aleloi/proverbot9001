#!/bin/bash
source ./bin/activate

# ./src/proverbot9001.py search-report -j 10 --weightsfile=data/polyarg-weights.dat --prelude=./coq-projects/ --search-depth=6  --search-width=5 --splits-file=mathcomp_proj_split.json  -P ./math-comp/mathcomp/ssreflect/choice.v

rm mathcomp-outputs/*
i=0
for fl in $(cat mathcomp-files.txt);
do
    i=$((i+1))
    touch mathcomp-outputs/file"$i"-stderr.out
    touch mathcomp-outputs/file"$i"-stdout.out
    echo "FILE" $fl > mathcomp-outputs/file"$i"-stderr.out
    echo "FILE" $fl > mathcomp-outputs/file"$i"-stdout.out
    echo
    echo "Running file $i $fl"
    echo "[ { \"project_name\": \"math-comp\", \"test_files\": [ \"$fl\" ], \"switch\": \"coq-8.12\"}]" > mathcomp-jsons/"$i".json
    echo "Running command: "
    echo ./src/proverbot9001.py search-report -j 16 --weightsfile=data/polyarg-weights.dat --prelude=./coq-projects/ --search-depth=2  --search-width=2 --splits-file=mathcomp-jsons/"$i".json  -P ./math-comp/mathcomp/ssreflect/choice.v --no-generate-report "2>" mathcomp-outputs/file"$i"-stderr.out ">" mathcomp-outputs/file"$i"-stdout.out
    ./src/proverbot9001.py search-report -j 16 --weightsfile=data/polyarg-weights.dat --prelude=./coq-projects/ --search-depth=2  --search-width=2 --splits-file=mathcomp-jsons/"$i".json  -P ./math-comp/mathcomp/ssreflect/choice.v --no-generate-report  2>> mathcomp-outputs/file"$i"-stderr.out >> mathcomp-outputs/file"$i"-stdout.out

done
