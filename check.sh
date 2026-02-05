#!/bin/bash


depth=18
if [ -n "$1" ]; then
    tlc -simulate -deadlock -dumpTrace json traces/trace.json -depth $depth -workers 10 -seed "$1" SnapshotIsolation | tee logout
else
    tlc -simulate -deadlock -dumpTrace json traces/trace.json -depth $depth -workers 10 SnapshotIsolation | tee logout
fi
python3 viz.py traces/trace.json
python3 tla_to_transaction_history.py traces/trace.json
