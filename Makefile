.PHONY: all paper verify clean

PYTHON ?= python3

all: verify paper

paper:
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	cp main.pdf paper.pdf
	pdflatex -interaction=nonstopmode -halt-on-error paper-amsart.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper-amsart.tex

verify:
	$(PYTHON) -m pytest -q

clean:
	rm -f main.aux main.log main.out main.toc main.synctex.gz
	rm -f paper-amsart.aux paper-amsart.log paper-amsart.out paper-amsart.synctex.gz
