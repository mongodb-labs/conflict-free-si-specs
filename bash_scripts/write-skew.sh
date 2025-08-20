#!/bin/bash

# Script to run TLC model checker with a specific invariant
# Compatible with older bash versions

# Define the invariant to test
INVARIANT="WriteSkewAnomaly"

echo "Running TLC for invariant: ${INVARIANT}"
# Create config file for this invariant
cat > "SnapshotIsolation.cfg" << EOF
INIT Init
NEXT Next
CONSTANTS
    Empty = Empty
    txnIds = {t0, t1}
    keys = {k1, k2, k3, k4, k5, k6}  
    values = {v1, v2}
INVARIANT ${INVARIANT}
ALIAS Alias
EOF

echo "Created SnapshotIsolation.cfg with invariant: ${INVARIANT}"
echo "Running TLC model checker..."

# Clean up any existing trace files before running
echo "Cleaning up existing trace files..."
rm -f SnapshotIsolation_TTrace_*.bin SnapshotIsolation_TTrace_*.tla
rm -f ../SnapshotIsolation_TTrace_*.bin ../SnapshotIsolation_TTrace_*.tla
rm -f *_TTrace_*.bin *_TTrace_*.tla
rm -f ../*_TTrace_*.bin ../*_TTrace_*.tla
rm -f ../traces/read_only_anomaly.txt

# Run TLC directly with cleanup flag
./tlc -simulate -cleanup -gzip -workers 10 -deadlock -dumpTrace json ../traces/trace-${INVARIANT}.json -config SnapshotIsolation.cfg ../SnapshotIsolation.tla

# Check if trace file was generated and run visualization
TRACE_FILE="../traces/trace-${INVARIANT}.json"
VIZ_OUTPUT_DIR="../output/graphs"

if [ -f "${TRACE_FILE}" ]; then    
    # Create visualization directory if it doesn't exist
    mkdir -p "${VIZ_OUTPUT_DIR}"
    
    # Run visualization script
    echo "Running visualization script..."
    cd ..
    python3 viz.py "traces/trace-${INVARIANT}.json" "output/graphs/${INVARIANT}"
    
    if [ $? -eq 0 ]; then
        echo "Visualization completed successfully!"
        echo "Output saved to: output/graphs/${INVARIANT}.png"
    else
        echo "Visualization failed!"
    fi
    
    # Run tla_to_transaction_history.py to generate db_diag format files
    echo "Running tla_to_transaction_history.py..."
    python3 /Users/sai.achalla/Desktop/snapshot-isolation-reexecution/tla_to_transaction_history.py "/Users/sai.achalla/Desktop/snapshot-isolation-reexecution/traces/trace-${INVARIANT}.json"
    
    cd bash_scripts
    
    if [ $? -eq 0 ]; then
        echo "Transaction history analysis completed successfully!"
    else
        echo "Transaction history analysis failed!"
    fi
else
    echo "No trace file generated - the invariant was not violated"
fi

# Clean up any trace files generated during this run
echo "Cleaning up trace files generated during this run..."
rm -f SnapshotIsolation_TTrace_*.bin SnapshotIsolation_TTrace_*.tla
rm -f ../SnapshotIsolation_TTrace_*.bin ../SnapshotIsolation_TTrace_*.tla
rm -f *_TTrace_*.bin *_TTrace_*.tla
rm -f ../*_TTrace_*.bin ../*_TTrace_*.tla
rm -f ../traces/read_only_anomaly.txt