
%.vo: %.v
	coqc $(subst .vo,.v,$@)

all: automata.vo

doc: automata.vo
	coqdoc -d docs automata.v

clean:
	rm -rf *.vo docs/*
