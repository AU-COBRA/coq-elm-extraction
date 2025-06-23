all: theory tests
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

tests: theory
	+make -C tests
.PHONY: tests

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
	+@make -C tests clean
	rm -rf docs
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
all: theory

# Do not forward these files
Makefile _CoqProject: ;

html: all
	rm -rf docs
	mkdir docs
	rocq doc --html --interpolate --parse-comments \
		--with-header extra/header.html --with-footer extra/footer.html \
		--toc \
		--coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
    	--external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
		--external https://metarocq.github.io/html MetaRocq \
		-R theories ElmExtraction \
		-R tests/theories ElmExtraction.Tests \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*test/*" \) -name "*.v" ! -wholename "./_opam/*"`
	cp extra/resources/coqdocjs/*.js docs
	cp extra/resources/coqdocjs/*.css docs
	cp extra/resources/toc/*.js docs
	cp extra/resources/toc/*.css docs
.PHONY: html
