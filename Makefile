HAVE_OPAM_BBV=$(shell if opam config var coq-bbv:share >/dev/null 2>/dev/null; then echo yes; else echo no; fi)
HAVE_OPAM_COQSAIL=$(shell if opam config var coq-sail:share >/dev/null 2>/dev/null; then echo yes; else echo no; fi)

ifeq ($(HAVE_OPAM_BBV),no)
BBV_DIR?=../bbv
endif
ifeq ($(HAVE_OPAM_COQSAIL),no)
SAIL_DIR?=../sail
endif

ARM_DIR=../sail-arm/arm-v8.5-a

COQ_LIBS = -R "$(ARM_DIR)" ''

ifdef BBV_DIR
COQ_LIBS += -Q "$(BBV_DIR)/src/bbv" bbv
endif

ifdef SAIL_DIR
COQ_LIBS += -Q "$(SAIL_DIR)/lib/coq" Sail
endif

SRC=Mword.v AArch64_Trivia.v AArch64_Aux.v Address_Translation_Orig.v Address_Translation_Pure.v Address_Translation_Soundness.v

TARGETS=$(SRC:.v=.vo)

.PHONY: all clean *.ide

all: $(TARGETS)
clean:
	rm -f -- $(TARGETS) $(TARGETS:.vo=.glob) $(TARGETS:%.vo=.%.aux) deps

$(TARGETS): %.vo: %.v
	coqc $(COQ_LIBS) $<

%.ide: %.v
	coqide $(COQ_LIBS) $<

deps: $(SRC)
	coqdep $(COQ_LIBS) $(SRC) > deps

-include deps
