#!/bin/bash

set -e

pushd satisfaction-core

cabal sandbox init --sandbox=.test-sandbox
cabal install --only-dep --enable-tests
cabal configure --enable-tests
cabal build
cabal test

popd
