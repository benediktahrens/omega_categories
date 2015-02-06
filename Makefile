COQDOCOPTS=--utf8 -g --interpolate --body-only -R . OmegaCategories -coqlib http://coq.inria.fr/stdlib/ 

all: coqcompile ${TARGETS}

coqcompile:
	coq_makefile -R . OmegaCategories *.v -o Makefile_coq
	$(MAKE) -f Makefile_coq

%.vo: %.v
	time ${COQBIN}coqc ${COQOPTS} $<

clean: 
	$(MAKE) -f Makefile_coq clean
	rm -f ${TARGETS}
