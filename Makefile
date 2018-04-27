SUBDIRS := $(wildcard */.)

check: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

.PHONY: check $(SUBDIRS)	
