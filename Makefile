all :: install

test :: binaries/osx/yices
	env PATH=./binaries/osx:$$PATH genex "a(b|c)d{2,3}e*"

binaries/osx/yices ::
	curl 'http://yices.csl.sri.com/cgi-bin/yices-newdownload.cgi?file=yices2smt09-x86_64-apple-darwin9.8.0-static-gmp.tgz&accept=I+accept' | tar zxf -
	cp yices2smt09/bin/yices binaries/osx/yices
	rm -rf yices2smt09

install ::
	cabal install
	cp ~/.cabal/bin/genex binaries/osx/
	strip binaries/osx/genex
