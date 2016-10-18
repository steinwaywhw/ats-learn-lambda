PARCC=$(HOME)/Git/ats-parcc/cps
UTIL=$(HOME)/Git/ats-utils
PATSCC=patscc -g -IATS $(PARCC) -IATS $(UTIL) -L$(PARCC) -L$(UTIL) -DATS_MEMALLOC_LIBC -lm -latslib -latsparcc -latsutils --tlcalopt-disable
RMF=rm -rf
PATSOPT=patsopt -IATS $(PARCC) -IATS $(UTIL) 

all: test



tc: 
	$(PATSOPT) -tc -d f.dats

clean: 
	$(RMF) *ats.c *.o a.out*

# test: untyped.sats untyped.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# test: simple.sats simple.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# test: infer.sats infer.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
	# $(PATSCC) $^
	# 
	# 

test: 
	$(PATSCC) f.dats