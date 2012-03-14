
%.vo: %.v
	coqc $(subst .vo,.v,$@)

all: misc.vo automata.vo

doc: all 
	coqdoc -d docs/html automata.v
	mv docs/html/index.html docs/html/index.html.old
	docs/undup.sh docs/html/index.html.old docs/html/index.html
	rm docs/html/index.html.old

clean:
	rm -rf *.vo docs/*
