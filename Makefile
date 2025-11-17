PROJET = projet_rocq_passeron_rousseau.v
COQDOC = coqdoc
PDFLATEX = pdflatex
LATEXMK = latexmk
SRC = $(wildcard *.v)
BODY = coq_body.tex
OUT = passeron_rousseau.pdf
WRAPPER = rapport.tex
COQC = coqc 

.PHONY: all clean_aux archive

all: pdf archive
pdf: $(OUT)
$(BODY): $(SRC)
	$(COQC) $(PROJET)
	$(COQDOC) --latex --body-only -o $(BODY) $(SRC)

$(OUT): $(BODY) $(WRAPPER)
	$(PDFLATEX) $(WRAPPER) 
	$(PDFLATEX) $(WRAPPER)
	mv rapport.pdf passeron_rousseau.pdf

clean:
	rm -f $(BODY) *.aux *.log *.toc *.out *.idx *.ilg *.ind *.vok *.glob *.vos *.fdb_latexmk *.sty *.fls *.vo rapport.pdf .projet_rocq_passeron_rousseau.aux *.tar.gz

# ===============================
#   ARCHIVAGE DU PROJET
# ===============================
archive: $(OUT)
	@echo "Création de l'archive passeron_rousseau.tar.gz..."
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
	    -czf passeron_rousseau.tar.gz \
	    $(SRC) $(WRAPPER) $(OUT) Makefile
	@echo "Archive créée : passeron_rousseau.tar.gz"
