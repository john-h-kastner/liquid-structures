slides.pdf: slides.lhs haskell.xml
	liquid --diff --short-names $< &&\
	pandoc --to=beamer\
		   --from=markdown+lhs\
		   --syntax-definition haskell.xml\
		   --output=$@\
		   --standalone\
		   $<

clean:
	rm -f slides.pdf
