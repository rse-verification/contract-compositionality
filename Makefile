default: spec

spec:
	Holmake -r -I semantics

fol:
	Holmake -r -I fol

clean:
	cd semantics && Holmake clean
	cd fol && Holmake clean

.PHONY: default clean spec fol
