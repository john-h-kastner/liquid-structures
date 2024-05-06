all: build/index.html

build/index.html: build/ README.rewrite_links.md
	sed 's!src/!https://github.com/john-h-kastner/liquid-structures/blob/master/src/!g' README.md > README.rewrite_links.md
	pandoc -s -t html -f markdown --css='/pandoc.css' --metadata title="Liquid Structures" -o build/index.html README.rewrite_links.md
	rm README.rewrite_links.md

build/:
	mkdir -p build

clean:
	rm -rf build
