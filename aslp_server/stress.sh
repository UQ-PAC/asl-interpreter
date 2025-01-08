#!/bin/bash

dune exec aslp_server --profile=release -- --threads 4 & 
sleep 5
wrk2 -t 8 -c64 -d 30s -s stress.lua -R10000 --latency http://localhost:8000
dune exec aslp_server --profile=release -- --killserver
