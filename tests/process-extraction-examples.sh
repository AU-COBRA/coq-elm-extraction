#!/bin/bash

ELM_PATH=./extracted-code/elm-extract
ELM_WEB_PATH=./extracted-code/elm-web-extract
ELM_TESTS=$ELM_PATH/tests
ELM_WEB_SRC=$ELM_WEB_PATH/src

echo "Processing Elm extraction"
for f in $ELM_PATH/*.elm.out;
do
    if [[ ! -e "$f" ]]; then continue; fi
    echo $f "--->" $ELM_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/module/,/suite/p' $f > $ELM_TESTS/$(basename ${f%.out})
done

WEB_APP_OUT=UserList.elm.out

echo "Processing Elm web-app extraction"
echo $WEB_APP_OUT "+ views.elm"  "--->" $ELM_WEB_SRC/Main.elm;
cat $ELM_WEB_PATH/$WEB_APP_OUT $ELM_WEB_SRC/views.elm > $ELM_WEB_SRC/Main.elm
