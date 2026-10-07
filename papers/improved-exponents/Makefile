# Build the paper.  Requires pdflatex and bibtex.
#
#   make            build main.pdf
#   make check      check that every cited Lean name exists in the sources
#   make clean      remove the auxiliary files
#   make distclean  also remove main.pdf

MAIN = main
SECTIONS = $(wildcard sections/*.tex)

.PHONY: all check clean distclean

all: $(MAIN).pdf

# One pass to collect the citations, bibtex, then pdflatex until it stops
# asking for another run.  The build fails if the cross-references do not
# converge or if a reference or a citation stays undefined.
$(MAIN).pdf: $(MAIN).tex preamble.tex notation.tex results.tex references.bib $(SECTIONS)
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  || { tail -n 40 $(MAIN).log; exit 1; }
	bibtex $(MAIN)
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  || { tail -n 40 $(MAIN).log; exit 1; }
	@for i in 1 2 3 4; do \
	  grep -q 'Rerun to get cross-references right' $(MAIN).log || break; \
	  echo "pdflatex: rerun $$i"; \
	  pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null; \
	done
	@! grep -q 'Rerun to get cross-references right' $(MAIN).log \
	  || { echo "paper: cross-references did not converge"; exit 1; }
	@! grep -E 'LaTeX Warning: (Reference|Citation) .* undefined|There were undefined (references|citations)' $(MAIN).log \
	  || { echo "paper: unresolved references"; exit 1; }
	@! grep -q 'multiply defined' $(MAIN).log \
	  || { echo "paper: multiply defined labels"; exit 1; }
	@grep -c '^Overfull' $(MAIN).log | sed 's/^/paper: overfull boxes: /'
	@grep '^Output written' $(MAIN).log

check:
	python3 check_lean_names.py

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out \
	      $(MAIN).toc $(MAIN).synctex.gz

distclean: clean
	rm -f $(MAIN).pdf
