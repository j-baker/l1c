#!/bin/bash

ulimit -Sv 2900000

set -e

HOLDIR=$(heapname | xargs dirname) || exit $?
echo "HOL revision: $(cd $HOLDIR; git rev-parse --short HEAD)"
echo "Machine: $(uname -nmo)"

#if ([ "$TRAVIS_BRANCH" = "master" ] || ["$TRAVIS_BRANCH" = "develop"]) && (grep -q -R cheat compiler || grep -q -R cheat semantics || grep -q -R cheat parser || grep -q -R cheat printer)
#then
#  echo "FAILED: Found a cheat!"
#  exit 1
#else
#  echo "No cheats were found."
#fi

git clean -xdf


while read i
do
  if [ ! -d $i ]
  then
      echo "Ignoring non-existent directory $i"
      continue
  fi
  pushd $i
  Holmake cleanAll &&
  if Holmake
  then
      if [ -x selftest.exe ]
      then
        ./selftest.exe || {
          echo "FAILED: $i selftest"
          exit 1
        }
      fi
  else
      echo "FAILED: $i"
      exit 1
  fi
  popd
done < build/build-sequence
