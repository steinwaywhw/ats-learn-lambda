PARCC=$(HOME)/Git/ats-parcc/cps
UTIL=$(HOME)/Git/ats-utils
PATSCC=patscc -g -IATS $(PARCC) -IATS $(UTIL) -L$(PARCC) -L$(UTIL) -DATS_MEMALLOC_LIBC -lm -latslib -latsparcc -latsutils --tlcalopt-disable
RMF=rm -rf
PATSOPT=patsopt -IATS $(PARCC) -IATS $(UTIL) 

all: systemf 



# tc: 
# 	$(PATSOPT) -tc -d f.dats

# clean: 
# 	$(RMF) *ats.c *.o a.out*

# # test: untyped.sats untyped.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# # test: simple.sats simple.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# # test: infer.sats infer.dats testall.dats $(PARCC)/sexp.sats $(PARCC)/sexp.dats
# 	# $(PATSCC) $^
# 	# 
# 	# 

# test: 
# 	$(PATSCC) f.dats

cleanall: 
	$(RMF) */*ats.c */*.o */a.out*


systemf: systemf/*
	cd systemf && $(PATSCC) *.dats

untyped: lambda_untyped/*
	cd lambda_untyped && $(PATSCC) *.dats

simple: lambda_simple/*
	cd lambda_simple && $(PATSCC) *.dats

letinfer: lambda_let_infer/*
	cd lambda_let_infer && $(PATSCC) *.dats

letbaseinfer: lambda_let_base_infer/*
	cd lambda_let_base_infer && $(PATSCC) *.dats