#!/bin/sh

stack build diagrams diagrams-builder palette &&\
    lhs2TeX --poly fenwick.lhs -o fenwick.tex &&\
    stack exec -- pdflatex --enable-write18 fenwick.tex
