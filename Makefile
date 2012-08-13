
all: tactics.vo base.vo misc.vo glue.vo regexp.vo automata.vo transitive_closure.vo myhill_nerode.vo

%.vo: %.v
	coqc $(subst .vo,.v,$@)

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

definitions: all
	mkdir -p docs/definitions
	find -type f -name '*.v' -exec sh -c 'cat "{}" | python docs/extract_definitions.py `basename "{}" .v` docs/definitions' \; 

doc: html_doc_beautiful definitions

clean:
	rm -r *.vo docs/html/*
