#!/bin/bash

set -e

ulimit -Sv 2900000

pushd $HOME

if which hol >/dev/null; then
    echo "Dependencies already appear to be present. Not rebuilding them."
    exit 0
fi

# HOL

git clone --quiet https://github.com/mn200/HOL.git
pushd HOL
poly < tools/smart-configure.sml
bin/build -nograph
popd

# latexmk
wget http://users.phys.psu.edu/~collins/software/latexmk-jcc/latexmk-443a.zip
unzip latexmk-443a.zip
pushd latexmk
mv latexmk.pl latexmk
popd

popd

ls -a
