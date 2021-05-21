#!/bin/sh

stack build diagrams diagrams-builder diagrams-contrib palette &&\
    stack exec -- pdflatex --enable-write18 fenwick-plclub.tex
