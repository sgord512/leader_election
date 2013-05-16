# Makefile for my proof

all : 
	coqc Correctness.v

Correctness.vo : Correctness.v Lang.vo Leader.vo Misc.vo SfLib.vo ListExt.vo Cases.vo
	coqc Correctness.v

Cases.vo : 
	coqc Cases.v

Leader.vo : Leader.v Lang.vo Misc.vo SfLib.vo ListExt.vo
	coqc Leader.v

Misc.vo : Misc.v Lang.vo
	coqc Misc.v

Lang.vo : Lang.v SfLib.vo 
	coqc Lang.v

SfLib.vo : SfLib.v
	coqc SfLib.v

ListExt.vo : ListExt.v
	coqc ListExt.v

clean : 
	rm -f *.vo *.v~
