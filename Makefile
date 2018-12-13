JSRES=resources/coqdocjs/extra/resources/
DOCRES=resources/coqdoc.css $(JSRES)coqdocjs.css $(JSRES)coqdocjs.js $(JSRES)config.js

all: libs ctl kstar k

libs:
	$(MAKE) -C libs

ctl: libs
	$(MAKE) -C CTL

kstar: libs
	$(MAKE) -C Kstar

k: libs
	$(MAKE) -C K

clean:
	$(MAKE) -C libs clean
	$(MAKE) -C CTL clean
	$(MAKE) -C Kstar clean
	$(MAKE) -C K clean
	rm -rf libs/.*.aux K/.*.aux Kstar/.*.aux CTL/.*.aux \
	libs/CoqMakefile.conf K/CoqMakefile.conf Kstar/CoqMakefile.conf CTL/CoqMakefile.conf

website: all
# clear all HTML
	rm -rf website/html
	mkdir website/html
# generate HTML using coqdoc
	$(MAKE) -C libs html
	$(MAKE) -C CTL html
	$(MAKE) -C Kstar html
	$(MAKE) -C K html
# copy HTML
	cp -r libs/html website/html/libs
	mv website/html/libs/index.html website/html/libs/indexpage.html
	cp -r K/html website/html/K
	cp -r Kstar/html website/html/Kstar
	cp -r CTL/html website/html/CTL
# copy JS and Styles
	cp ${DOCRES} website/html/libs
	cp ${DOCRES} website/html/K
	cp ${DOCRES} website/html/Kstar
	cp ${DOCRES} website/html/CTL

pack:
	tar -C website -czf website.tgz {gallina,}html

.PHONY: libs k kstar ctl clean graph website
