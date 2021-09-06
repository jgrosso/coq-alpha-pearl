#!/bin/sh

latexmk -C README.tex
latexmk -pdflatex=lualatex -pdf --synctex=1 -interaction=nonstopmode --shell-escape -file-line-error README.tex
