#!/bin/bash

set -e

echo `pwd`

pushd satisfaction-core

echo `pwd`

cabal sandbox init --sandbox=.test-sandbox
cabal install --only-dep --enable-tests
cabal configure --enable-tests
cabal build
cabal test

popd
