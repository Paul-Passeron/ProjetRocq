PROJET = projet_rocq_passeron_rousseau.v
COQDOC = coqdoc
PDFLATEX = pdflatex
LATEXMK = latexmk
SRC = $(wildcard *.v)
BODY = coq_body.tex
OUT = rapport.pdf
WRAPPER = rapport.tex
COQC = coqc 

.PHONY: all clean_aux archive

all: $(OUT) archive

$(BODY): $(SRC)
	$(COQC) $(PROJET)
	$(COQDOC) --latex --body-only -o $(BODY) $(SRC)

$(OUT): $(BODY) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER)

clean:
	rm -f $(BODY) *.aux *.log *.toc *.out *.idx *.ilg *.ind *.vok *.glob *.vos *.fdb_latexmk *.sty *.fls *.vo rapport.pdf .projet_rocq_passeron_rousseau.aux *.tar.gz

# ===============================
#   ARCHIVAGE DU PROJET
# ===============================
archive: $(OUT)
	@echo "Création de l'archive projet.tar.gz..."
	tar --exclude='*.aux' \
	    --exclude='*.log' \
	    --exclude='*.toc' \
	    --exclude='*.out' \
	    --exclude='*.idx' \
	    --exclude='*.ilg' \
	    --exclude='*.ind' \
	    --exclude='*.vok' \
	    --exclude='*.glob' \
	    --exclude='*.vos' \
	    --exclude='*.fdb_latexmk' \
	    --exclude='*.sty' \
	    --exclude='*.fls' \
	    --exclude='*.vo' \
	    --exclude='.projet_rocq_passeron_rousseau.aux' \
	    -czf projet.tar.gz \
	    $(SRC) $(WRAPPER) $(OUT) Makefile
	@echo "Archive créée : projet.tar.gz"
