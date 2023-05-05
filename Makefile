all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f extraction/lib/*.ml extraction/lib/*.mli
	rm -f extraction/*.tr
	rm -rf extraction/_build extraction/__pycache__

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all default quick install clean
