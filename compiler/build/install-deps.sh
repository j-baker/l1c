#!/bin/bash

set -e

ulimit -Sv 2900000

pushd $HOME

# Poly/ML

export PATH=$PATH:$HOME/polyml/bin
export LD_LIBRARY_PATH=$HOME/polyml/lib

if which poly >/dev/null; then
    echo "Dependencies already appear to be present. Not rebuilding them."
    exit 0
fi

# HOL

git clone --quiet https://github.com/mn200/HOL.git
pushd HOL
poly < tools/smart-configure.sml
bin/build -nograph
popd

popd

ls -a
