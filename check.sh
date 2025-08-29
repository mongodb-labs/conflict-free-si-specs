#!/bin/bash

tlc -simulate -deadlock -dumpTrace json traces/trace.json -depth 15 -workers 10 SnapshotIsolation | tee logout
python3 viz.py traces/trace.json
python3 tla_to_transaction_history.py traces/trace.json