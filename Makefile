#BBV_DIR=/home/bcampbe2/afs/rems/github/bbv
#SAIL_DIR=/home/bcampbe2/afs/rems/github/sail
#ARM_DIR=/home/bcampbe2/sail-arm-compute
BBV_DIR=../bbv
SAIL_DIR=../sail
ARM_DIR=/disk/scratch/bcampbe2/sail-arm

COQ_LIBS = -R "$(BBV_DIR)/theories" bbv -R "$(SAIL_DIR)/lib/coq" Sail -R "$(ARM_DIR)/arm-v8.5-a" ''

SRC=Mword.v AArch64_Trivia.v AArch64_Aux.v Address_Translation_Orig.v Address_Translation_Pure.v

TARGETS=$(SRC:.v=.vo)

.PHONY: all clean *.ide

all: $(TARGETS)
clean:
	rm -f -- $(TARGETS) $(TARGETS:.vo=.glob) $(TARGETS:%.vo=.%.aux) deps

%.vo: %.v
	coqc $(COQ_LIBS) $<

%.ide: %.v
	coqide $(COQ_LIBS) $<

deps: $(SRC)
	coqdep $(COQ_LIBS) $(SRC) > deps

-include deps
