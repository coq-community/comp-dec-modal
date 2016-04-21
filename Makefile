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
	rm -rf website/html website/gallinahtml
	rm -rf libs/.*.aux K/.*.aux Kstar/.*.aux CTL/.*.aux

graph:
	$(MAKE) -C CTL graph
	$(MAKE) -C Kstar graph
	$(MAKE) -C K graph

website: all
#clear website	
	rm -rf website/html website/gallinahtml
#regenerate html (with proofs)
	rm -rf libs/html K/html Kstar/html CTL/html 
	$(MAKE) -C libs html
	$(MAKE) -C K html
	$(MAKE) -C Kstar html
	$(MAKE) -C CTL html
	mkdir website/html
#copy html
	cp website/pslab.css website/html/
	cp -r libs/html website/html/libs
	cp -r K/html website/html/K
	cp -r Kstar/html website/html/Kstar
	cp -r CTL/html website/html/CTL
#regenerate gallinahtml (without proofs)
	rm -rf libs/html K/html Kstar/html CTL/html 
	$(MAKE) -C libs gallinahtml
	$(MAKE) -C K gallinahtml
	$(MAKE) -C Kstar gallinahtml
	$(MAKE) -C CTL gallinahtml
	mkdir website/gallinahtml
# copy gallinahtml
	cp website/pslab.css website/gallinahtml/
	cp -r libs/html website/gallinahtml/libs
	cp -r K/html website/gallinahtml/K
	cp -r Kstar/html website/gallinahtml/Kstar
	cp -r CTL/html website/gallinahtml/CTL

pack:
	tar -C website -czf website.tgz {gallina,}html

.PHONY: libs k kstar ctl clean graph website
