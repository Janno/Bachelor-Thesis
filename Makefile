
%.vo: %.v
	coqc $(subst .vo,.v,$@)

all: misc.vo automata.vo transitive_closure.vo

doc: all 
	coqdoc -d docs/html automata.v misc.v transitive_closure.v
	mv docs/html/index.html docs/html/index.html.old
	docs/undup.sh docs/html/index.html.old docs/html/index.html
	rm docs/html/index.html.old
	python2.6 docs/beautifier.py docs/html/transitive_closure.html > docs/html/transitive_closure.html.tmp
	mv docs/html/transitive_closure.html.tmp docs/html/transitive_closure.html
	python2.6 docs/beautifier.py docs/html/automata.html > docs/html/automata.html.tmp
	mv docs/html/automata.html.tmp docs/html/automata.html
	python2.6 docs/beautifier.py docs/html/misc.html > docs/html/misc.html.tmp
	mv docs/html/misc.html.tmp docs/html/misc.html

clean:
	rm -rf *.vo docs/*
