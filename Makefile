PARCC=$(HOME)/Git/ats-parcc/cps
UTIL=$(HOME)/Git/ats-utils
PATSCC=patscc -g -IATS $(PARCC) -IATS $(UTIL) -L$(PARCC) -L$(UTIL) -DATS_MEMALLOC_LIBC -lm -latslib -latsparcc -latsutils --tlcalopt-disable
RMF=rm -rf


all: test



tc: 
	$(PATSCC) -tcats untyped.sats

clean: 
	$(RMF) *ats.c *.o

test: untyped.sats untyped.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# test: simple.sats simple.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
	$(PATSCC) $^