bin := nil
ghc := --with-compiler=ghc-8.10.7
opts := "--ghc-options=-Wall \
                       -threaded \
                       -rtsopts \
                       -with-rtsopts=-N \
                       -feager-blackholing \
                       -dynamic"
fast := $(ghc) $(opts) "--ghc-options=-O0"
release := $(ghc) $(opts) "--ghc-options=-O2 -fexpose-all-unfoldings"
test-opts := $(fast) --test-show-details=direct
path := ${HOME}/.local/bin

.PHONY: build
build:
	cabal build $(fast)

.PHONY: release
release:
	cabal build $(release)

.PHONY: install
install:
	make release
	make deploy

.PHONY: deploy
deploy:
	cp -f $(shell cabal list-bin $(bin)) app
	/usr/bin/strip app/$(bin)
	mkdir -p $(path)
	rm -f $(path)/$(bin)
	cp -f app/$(bin) $(path)

.PHONY: clean
clean:
	git clean -xdf
	cabal clean

.PHONY: test
test:
	cabal test test $(test-opts) --test-option=--match --test-option="$(match)"

.PHONY: doc
doc:
	cabal haddock --haddock-hyperlink-source

.PHONY: opendoc
opendoc:
	open $(shell /usr/bin/find dist-newstyle -name "index.html")

.PHONY: guide
guide:
	jupyter nbconvert --to html notebook/tutorial.ipynb
