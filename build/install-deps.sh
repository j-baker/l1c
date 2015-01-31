#!/bin/bash

set -e

pushd $HOME

# Poly/ML

if [ -d "polyml" ]; then
    echo "Dependencies already appear to be present."
    exit 0
fi

svn checkout --quiet svn://svn.code.sf.net/p/polyml/code/trunk polyml
pushd polyml/polyml
./configure --prefix=$HOME --enable-shared
make
make compiler
make install
popd

export PATH=$PATH:$HOME/bin
export LD_LIBRARY_PATH=$HOME/lib

# HOL

git clone --quiet https://github.com/mn200/HOL.git
pushd HOL
git checkout tags/kananaskis-10
poly < tools/smart-configure.sml
bin/build -nograph
popd

popd
