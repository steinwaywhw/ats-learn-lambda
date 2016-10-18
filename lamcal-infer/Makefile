PARCC=$(HOME)/Git/ats-parcc/cps
UTIL=$(HOME)/Git/ats-utils
PATSCC=patscc -IATS $(PARCC) -IATS $(UTIL) -L$(PARCC) -L$(UTIL) -DATS_MEMALLOC_LIBC -lm -latslib -latsparcc -latsutils --tlcalopt-disable
RMF=rm -rf



all: test

clean: 
	$(RMF) *ats.c

tc: 
	$(PATSCC) -tcats easy_base.dats unifier.dats unionfind.dats

test: 
	$(PATSCC) easy_base.dats unifier.dats unionfind.dats
