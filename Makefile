COQBIN ?=
ROCQLIB ?=

# Use tools from PATH by default. COQBIN may name an installation-specific
# binary directory; normalize it so callers need not include a trailing slash.
ROCQ_BIN_DIR := $(if $(strip $(COQBIN)),$(patsubst %/,%,$(strip $(COQBIN)))/,)
COQMAKEFILE := $(ROCQ_BIN_DIR)coq_makefile
ROCQ_ENV := $(if $(strip $(ROCQLIB)),ROCQLIB="$(ROCQLIB)",)

.PHONY: all clean

all: Makefile.coq
	$(ROCQ_ENV) $(MAKE) -f Makefile.coq COQBIN="$(ROCQ_BIN_DIR)"

Makefile.coq: _CoqProject
	$(ROCQ_ENV) $(COQMAKEFILE) -f _CoqProject -o Makefile.coq

clean:
	@if [ -f Makefile.coq ]; then \
		$(ROCQ_ENV) $(MAKE) -f Makefile.coq COQBIN="$(ROCQ_BIN_DIR)" clean; \
	fi
	$(RM) Makefile.coq Makefile.coq.conf
