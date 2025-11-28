all: tests process-extraction-examples
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

tests: RocqMakefile
	+@make -f RocqMakefile
.PHONY: plugin

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
.PHONY: clean

install: RocqMakefile
	+@make -f RocqMakefile install
.PHONY: install

uninstall: RocqMakefile
	+@make -f RocqMakefile uninstall
.PHONY: uninstall

# Forward most things to Rocq makefile. Use 'force' to make this phony.
%: RocqMakefile force
	+@make -f RocqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: tests
	./process-extraction-examples.sh
.PHONY: process-extraction-examples

ELM_DIR=./extracted-code/elm-extract
ELM_WEB_APP_DIR=./extracted-code/elm-web-extract

test-extraction: clean-compiled-extraction
	mkdir -p $(ELM_DIR)/src
	cd $(ELM_DIR); elm-test
	cd $(ELM_WEB_APP_DIR); elm make src/Main.elm

clean-compiled-extraction:
	rm -f -r $(ELM_WEB_APP_DIR)/elm-stuff
	rm -f -r $(ELM_WEB_APP_DIR)/index.html
	rm -f -r $(ELM_DIR)/elm-stuff
.PHONY: clean-compiled-extraction

clean-extraction-out-files:
	rm -f $(ELM_WEB_APP_DIR)/*.elm.out
	rm -f $(ELM_DIR)/*.elm.out

clean-extraction-sources:
	rm -f $(ELM_DIR)/tests/*.elm
	rm -f $(ELM_WEB_APP_DIR)/src/main.elm
.PHONY:clean-extraction-sources

clean-extraction-examples: clean-compiled-extraction clean-extraction-out-files clean-extraction-sources
	rm ./thories/*.vo # to force recompilation of examples (a bit ad-hoc though)
.PHONY: clean-compiled-extraction clean-extraction-out-files clean-extraction-sources
