bin := nil
path := ${HOME}/.local/bin

.PHONY: build
build:
	stack build

.PHONY: install
install:
	make build
	cp -f $(shell stack path --local-install-root)/bin/$(bin) app
	/usr/bin/strip app/$(bin)
	mkdir -p $(path)
	rm -f $(path)/$(bin)
	cp -f app/$(bin) $(path)

.PHONY: clean
clean:
	git clean -xdf
	stack clean --full

.PHONY: doc
doc:
	stack haddock --open $(bin)

.PHONY: guide
guide:
	jupyter nbconvert --to html notebook/tutorial.ipynb
