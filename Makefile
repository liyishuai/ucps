OTT_COQ = ott -coq_lngen true -coq_names_in_rules false
OTT_TEX = ott -tex_show_meta false
LNGEN   = lngen
SED     = 's/Metatheory/Metalib.Metatheory/g;s/LibLNgen/Metalib.LibLNgen/g'

FILES = ucps_ott.v ucps_inf.v

all: Makefile.coq $(FILES) ucps.pdf
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

%.tex: %.ott
	$(OTT_TEX) -o $@ $<

clean: Makefile.coq
	$(MAKE) -f $< clean
	latexmk -c -f ucps

distclean: clean
	latexmk -C -f ucps
	rm -f ucps*.v*
	rm -f Makefile.coq*
