#!/bin/sh

stack build diagrams diagrams-builder palette && stack exec -- rubber -d --unsafe *.tex
