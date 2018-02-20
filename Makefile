OTT_COQ = ott -coq_lngen true -coq_names_in_rules false
OTT_TEX = ott -tex_show_meta false
LNGEN   = lngen
SED     = 's/Metatheory/Metalib.Metatheory/g;s/LibLNgen/Metalib.LibLNgen/g'

FILES = ucps_ott.v ucps_inf.v

all: Makefile.coq $(FILES) note.pdf
	$(MAKE) -f $<

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

%_ott.v: %.ott
	$(OTT_COQ) -o $@ $<
	sed -i "" $(SED) $@

%_inf.v: %_ott.v
	$(LNGEN) --coq-stdout --coq-ott FTop.$*_ott $*.ott | sed $(SED) > $@

%.pdf: %.tex
	latexmk -pdf $*

note.pdf: ucps.tex

ucps.tex: ucps.ott
	$(OTT_TEX) -o $@ $<
	sed -i "" -e "/begin.document/,/end.document/d" ucps.tex

clean: Makefile.coq
	$(MAKE) -f $< clean
	latexmk -c -f ucps note

distclean: clean
	latexmk -C -f ucps note
	rm -f ucps*.v*
	rm -f Makefile.coq*
