COQDOC = coqdoc
PDFLATEX = pdflatex
SRC = $(wildcard *.v)
BODY = coq_body.tex
OUT = rapport.pdf
WRAPPER = rapport.tex

.PHONY: all clean

all: $(OUT)

$(BODY): $(SRC)
	$(COQDOC) --latex --body-only -o $(BODY) $(SRC)

$(OUT): $(BODY) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER)
	mv $(basename $(WRAPPER)).pdf $(OUT)

clean:
	rm -f $(BODY) *.aux *.log *.toc *.out *.idx *.ilg *.ind rapport.pdf

