#!/bin/sh

stack build diagrams diagrams-builder diagrams-contrib palette &&\
    lhs2TeX --poly fenwick-ICFP.lhs -o fenwick-ICFP.tex &&\
    stack exec -- pdflatex --enable-write18 fenwick-ICFP.tex
