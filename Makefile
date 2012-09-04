all :: install

test :: binaries/osx/z3 binaries/osx/genex
	env PATH=./binaries/osx:$$PATH genex "a(b|c)d{2,3}e*"
	env PATH=./binaries/osx:$$PATH genex "a(b|c)d{2,3}e*\1"

binaries/osx/z3 :
	curl https://research.microsoft.com/en-us/um/redmond/projects/z3/z3-osx-4.1-x64.tar.gz | tar zxf -
	cp z3/bin/z3 binaries/osx/
	rm -rf z3

binaries/osx/yices :
	curl 'http://yices.csl.sri.com/cgi-bin/yices-newdownload.cgi?file=yices2smt09-x86_64-apple-darwin9.8.0-static-gmp.tgz&accept=I+accept' | tar zxf -
	cp yices2smt09/bin/yices binaries/osx/
	rm -rf yices2smt09

binaries/osx/genex :
	cabal configure
	cabal build
	cp dist/build/genex/genex binaries/osx/
	strip binaries/osx/genex

install ::
	cabal install
	cp dist/build/genex/genex binaries/osx/
	strip binaries/osx/genex

ghci ::
	ghci -isrc Main.hs
