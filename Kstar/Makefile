all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html
	cp ../resources/coqdoc.css html/

gallinahtml: Makefile.coq
	+make -f Makefile.coq gallinahtml
	cp ../resources/coqdoc.css html/

graph:
	coqdep -noglob -I . *.v >depend 2>/dev/null
	makedot depend && mv depend.dot depend.gv
	sed -i 's/node .*;/node [fontsize=18, shape=rect, color="#000000"]; edge [color="#0000ff"];/' depend.gv 
	dot -Tsvg -o depend.svg depend.gv
	dot depend.gv >depend.dot
	dot2tex --codeonly -f tikz -o depend.tex depend.dot


clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq depend.*

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html gallinahtml clean
