PROJET = projet_rocq_passeron_rousseau.v
COQDOC = coqdoc
PDFLATEX = pdflatex
LATEXMK = latexmk
SRC = $(wildcard *.v)
BODY = coq_body.tex
OUT = rapport.pdf
WRAPPER = rapport.tex
COQC = coqc 

.PHONY: all clean

all: $(OUT)

$(BODY): $(SRC)
	$(COQC) $(PROJET)
	$(COQDOC) --latex --body-only -o $(BODY) $(SRC)

$(OUT): $(BODY) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER)

clean:
	rm -f $(BODY) *.aux *.log *.toc *.out *.idx *.ilg *.ind *.vok *.glob *.vos *.fdb_latexmk *.sty *.fls *.vo rapport.pdf

