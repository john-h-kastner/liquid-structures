slides.pdf: slides.tex
	pdflatex $< > /dev/null

slides.tex: slides.md
	pandoc --to=beamer\
		   --from=markdown\
		   --output=$@\
		   --standalone\
		   $<

clean:
	rm -f slides.pdf slides.tex *.aux *.log *.nav *.snm *.vrb *.toc
