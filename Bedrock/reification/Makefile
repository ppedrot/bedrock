PREFIX  := Bedrock.reification
MODULES := extlib.mli extlib.ml reif.ml4 example.v

.PHONY: coq quick vio2vo clean install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq quick

vio2vo: Makefile.coq
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq vio2vo

Makefile.coq: Makefile $(MODULES)
	$(COQBIN)coq_makefile -R . $(PREFIX) -I $(ROOT)/src/reification \
		     $(MODULES) -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install install-natdynlink

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
