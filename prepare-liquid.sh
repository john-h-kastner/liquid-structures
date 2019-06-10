#! /bin/sh
stack test
mkdir -p _liquid-markdown
find src/ -name "*.lhs.markdown" -exec cp {} _liquid-markdown \;
