slides.pdf: slides.tex
	pdflatex $< > /dev/null

slides.tex: slides.lhs haskell.xml
	liquid --diff --short-names $< &&\
	pandoc --to=beamer\
		   --from=markdown+lhs\
		   --syntax-definition haskell.xml\
		   --output=$@\
		   --standalone\
		   $<

clean:
	rm -f slides.pdf slides.tex *.aux *.log *.nav *.snm *.vrb *.toc
