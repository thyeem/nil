bin := nil
path := ${HOME}/.local/bin

.PHONY: build
build:
	stack build

.PHONY: release
release:
	stack build $(ghc) $(opts) $(release)

.PHONY: install
install:
	make release
	make deploy

.PHONY: deploy
deploy:
	cp -f $(shell stack path --local-install-root)/bin/$(bin) app
	/usr/bin/strip app/$(bin)
	mkdir -p $(path)
	rm -f $(path)/$(bin)
	cp -f app/$(bin) $(path)

.PHONY: clean
clean:
	git clean -xdf
	stack clean --full

.PHONY: test
test:
	stack test

.PHONY: doc
doc:
	stack haddock

.PHONY: opendoc
opendoc:
	open $(shell /usr/bin/find dist-newstyle -name "index.html")

.PHONY: guide
guide:
	jupyter nbconvert --to html notebook/tutorial.ipynb
