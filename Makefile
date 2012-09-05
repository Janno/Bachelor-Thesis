
.PHONY : all definitions thesis

CHPTS_TEX = $(shell for c in `cd thesis; ls chpt_*.tex`; do echo thesis/chapters/$$c; done)
CHPTS = $(subst .tex,.pdf,${CHPTS_TEX})

COQ_FILES = $(shell ls *.v)
COQ_TARGETS = $(subst .v,.vo,${COQ_FILES})

all: ${COQ_TARGETS} 
	#tactics.vo base.vo misc.vo glue.vo regexp.vo automata.vo transitive_closure.vo myhill_nerode.vo

%.vo: %.v
	coqc $(subst .vo,.v,$@)

thesis/chapters/%.pdf: thesis/%.tex
	j=$(shell basename $@); cd thesis; pdflatex -jobname=chapters/$$j "\includeonly{$$j,includes.tex}\input{thesis}"

html_doc: all
	mkdir -p docs/html
	coqdoc -d docs/html automata.v misc.v transitive_closure.v

html_doc_beautiful: html_doc
	mv docs/html/index.html docs/html/index.html.old
	docs/undup.sh docs/html/index.html.old docs/html/index.html
	rm docs/html/index.html.old
	python2.6 docs/beautifier.py docs/html/transitive_closure.html > docs/html/transitive_closure.html.tmp
	mv docs/html/transitive_closure.html.tmp docs/html/transitive_closure.html
	python2.6 docs/beautifier.py docs/html/automata.html > docs/html/automata.html.tmp
	mv docs/html/automata.html.tmp docs/html/automata.html
	python2.6 docs/beautifier.py docs/html/misc.html > docs/html/misc.html.tmp
	mv docs/html/misc.html.tmp docs/html/misc.html

docs/definitions: ${COQ_TARGETS} docs/extract_definitions.py
	mkdir -p docs/definitions
	rm -f docs/definitions/*
	find -type f -name '*.v' -exec sh -c 'cat "{}" | python docs/extract_definitions.py `basename "{}" .v` docs/definitions' \; 

definitions: docs/definitions

thesis/thesis.pdf: definitions ${CHPTS}
	cd thesis; latexmk -pdf thesis

thesis: thesis/thesis.pdf


#chapters: thesis 
#	cd thesis; bash -c 'for i in chpt_*.tex chpt_*.tex; do j=$${i%.tex}; ; done'

doc: html_doc_beautiful definitions

clean:
	rm -r *.vo docs/html/*
