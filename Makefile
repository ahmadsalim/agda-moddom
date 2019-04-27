SUBDIRS := $(wildcard */.)

check: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ AGDA=/home/sas2019/agda-moddom/.cabal-sandbox/bin/agda

.PHONY: check $(SUBDIRS)	
