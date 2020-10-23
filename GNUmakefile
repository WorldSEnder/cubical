AGDA_EXEC=agda
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
EVERYTHINGS=runhaskell ./Everythings.hs

.PHONY : all
all : check

.PHONY : test
test: check-whitespace check-longfiles gen-and-check-everythings check-README check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	cabal exec -- fix-whitespace

.PHONY : check-whitespace
check-whitespace:
	cabal exec -- fix-whitespace --check

# checking for files with long lines

.PHONY : check-longfiles
check-longfiles:
# Limit is set to 100 characters. Due to a lot of files actually hitting that, currently this is
# not a hard error, but simply a warning
	@long_files=$$(rg -n --color always '.{101,}' -g "**/*.agda" -g "!**/Everything.agda") ; \
	if [ -n "$$long_files" ] ; then \
	  printf "%s\n%s\n" \
	        "Warning! The following source files contain lines longer than 100 characters:" \
	        "$$long_files" ; \
	fi

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except Experiments

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments

.PHONY : gen-and-check-everythings
gen-and-check-everythings:
	$(EVERYTHINGS) gen-except Core Foundations Codata Experiments
	$(EVERYTHINGS) check Core Foundations Codata

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

# typechecking and generating listings for all files imported in README

.PHONY : check
check: gen-everythings
	$(AGDA) Cubical/README.agda
	$(AGDA) Cubical/WithK.agda

.PHONY : timings
timings: clean gen-everythings
	$(AGDA) -v profile.modules:10 Cubical/README.agda

.PHONY : listings
listings: $(wildcard Cubical/**/*.agda)
	$(AGDA) -i. -isrc --html Cubical/README.agda -v0

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
