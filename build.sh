#!/bin/sh

stack build diagrams diagrams-builder palette && stack exec -- pdflatex --enable-write18 *.tex
