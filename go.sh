#!/bin/sh

DEP=definitions.tex
TEX=poly.tex
PDF=${TEX%.tex}.pdf

compile() {
	pdflatex $TEX < /dev/null
}

[ -e $PDF ] || compile
xpdf -remote view $PDF &

while inotifywait -qr -o /dev/null -e modify $TEX $DEP
do
	compile
	xpdf -remote view -reload
done
