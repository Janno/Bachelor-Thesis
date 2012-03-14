
%.vo: %.v
	coqc $(subst .vo,.v,$@)

all: misc.vo automata.vo

doc: all 
	coqdoc -d docs automata.v

clean:
	rm -rf *.vo docs/*
