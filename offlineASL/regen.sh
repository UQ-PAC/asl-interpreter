#!/bin/bash -xe

# this script boostraps the dune.generated files entirely from scratch.
# it can be used to make sure the dune.generated files are correct and unmodified

rm -rfv offlineASL{,-pc}/dune.generated
touch offlineASL{,-pc}/dune.generated
ASLP_OFFLINE_BOOTSTRAP=true dune build @offlineASL-pc/runtest @offlineASL/runtest --auto-promote || true
dune build @offlineASL-pc/runtest @offlineASL/runtest --auto-promote || true
dune build @offline "$@"
