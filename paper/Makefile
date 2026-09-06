.PHONY: all clean

all: k.pdf

k.pdf: k.tex
	pdflatex -interaction=nonstopmode k.tex
	pdflatex -interaction=nonstopmode k.tex
	pdflatex -interaction=nonstopmode k.tex

clean:
	rm -f k.aux k.log k.out k.toc k.pdf
