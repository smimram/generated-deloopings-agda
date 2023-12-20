AGDA = $(wildcard *.agda)
AGDAI = $(AGDA:.agda=.agdai)

all: build

build: $(AGDAI)

clean:
	rm -f *.agdai

%.agdai: %.agda
	agda $<
