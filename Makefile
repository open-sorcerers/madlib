TIX_FILE := $(shell stack path --local-hpc-root)/combined/custom/custom.tix

lint:
  brittany src/*.hs -c

prettify:
  brittany src/*.hs --write-mode inplace --suppress-output && brittany test/*.hs --write-mode inplace --suppress-output

test:
	stack test

test-watch:
	stack test --file-watch --fast

test-coverage:
	stack test --coverage && stack hpc report .

coverage-lcov:
	stack exec -- hpc-lcov --file $(TIX_FILE) --main-package madlib
