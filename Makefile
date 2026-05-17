ROCQ_APP  := /Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources
COQBIN    := $(ROCQ_APP)/bin/
ROCQLIB   := $(ROCQ_APP)/lib/coq

export COQBIN
export ROCQLIB

.PHONY: all clean Makefile.coq

all: Makefile.coq
	$(MAKE) -f Makefile.coq COQBIN=$(COQBIN) ROCQLIB=$(ROCQLIB)

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
