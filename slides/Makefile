all: slides.pdf

slides.pdf: slides.lhs haskell.xml liquid_logo.png red-black.pdf
	pandoc --to=beamer\
		   --from=markdown+lhs\
		   --syntax-definition haskell.xml\
		   --output=$@\
		   --standalone\
		   $<

clean:
	rm -f slides.pdf
