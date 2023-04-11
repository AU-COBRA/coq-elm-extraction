all: tests process-extraction-examples
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

tests: CoqMakefile
	+@make -f CoqMakefile
.PHONY: plugin

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
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
