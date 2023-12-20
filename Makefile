AGDA = $(wildcard *.agda)
AGDAI = $(AGDA:.agda=.agdai)

all: build

build: $(AGDAI)

clean:
	rm -f *.agdai

website:
	mkdir -p $@
	agda --html --html-dir=$@ Everything.agda
	cd $@ && rm -f index.html && ln -s Everything.html index.html

%.agdai: %.agda
	agda $<

.PHONY: website
