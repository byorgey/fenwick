#!/bin/sh

stack build diagrams diagrams-builder palette &&\
    lhs2TeX --poly Fenwick.lhs -o Fenwick.tex &&\
    stack exec -- pdflatex --enable-write18 Fenwick.tex
