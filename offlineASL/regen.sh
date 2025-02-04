#!/bin/bash -xe

truncate -s0 offlineASL{,-pc}/dune.generated
ASLP_OFFLINE_BOOTSTRAP=true dune build @offlineASL-pc/runtest @offlineASL/runtest --auto-promote || true
dune build @offlineASL-pc/runtest @offlineASL/runtest --auto-promote || true
dune build @offline
