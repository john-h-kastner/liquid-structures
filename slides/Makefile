slides_lhs = slides.lhs
slides_all = $(slides_lhs) haskell.xml liquid_logo.png red-black.pdf

all: .check slides.pdf README.md

.check: $(slides_lhs)
	liquid --short-names $<
	touch .check

slides.pdf: $(slides_all)
	pandoc --to=beamer\
		   --from=markdown+lhs\
		   --syntax-definition haskell.xml\
		   --output=$@\
		   --standalone\
		   $<

README.md: $(slides_all)
	pandoc --to=gfm\
		   --from=markdown+lhs\
		   --syntax-definition haskell.xml\
		   --strip-comments\
		   $< | sed 's/ sourceCode literate haskell/haskell/' > $@

clean:
	rm -f slides.pdf README.md .check
