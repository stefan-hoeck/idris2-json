export IDRIS2 ?= idris2

lib_pkg = json.ipkg

test_pkg = test.ipkg

doc_pkg  = doc.ipkg

.PHONY: all lib install clean clean-install

all: lib docs test

clean-install: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

docs:
	${IDRIS2} --build ${doc_pkg}

test:
	${IDRIS2} --build ${test_pkg} && build/exec/runTest -n 1000

install:
	${IDRIS2} --install ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${doc_pkg}
	${IDRIS2} --clean ${test_pkg}
	${RM} -r build

# Start a REPL in rlwrap
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/JSON.idr
