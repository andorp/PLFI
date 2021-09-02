idris2 = idris2

build: src plfi.ipkg FORCE
	$(idris2) --build plfi.ipkg

FORCE:

clean:
	$(idris2) --clean plfi.ipkg
	rm -r .build

typecheck:
	$(idris2) --typecheck plfi.ipkg
