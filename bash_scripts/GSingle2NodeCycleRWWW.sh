#!/bin/bash

# Script to run TLC model checker with a specific invariant
# Compatible with older bash versions

# Define the invariant to test
INVARIANT="GSingle2Inv2NodeCycleRWWW"

echo "Running TLC for invariant: ${INVARIANT}"
# Create config file for this invariant
cat > "SnapshotIsolation.cfg" << EOF
INIT Init
NEXT Next
CONSTANTS
    Empty = Empty
    txnIds = {t0, t1, t2}
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
rm -f ../traces/read_only_anomaly.txt

# Run TLC directly with cleanup flag
./tlc -simulate -cleanup -gzip -workers 10 -dumpTrace json ../traces/trace-${INVARIANT}.json -config SnapshotIsolation.cfg ../SnapshotIsolation.tla

# Check if trace file was generated and run visualization
TRACE_FILE="../traces/trace-${INVARIANT}.json"
VIZ_OUTPUT_DIR="../db_diagram/output/graphs"

if [ -f "${TRACE_FILE}" ]; then
    echo "Trace file generated successfully: ${TRACE_FILE}"
    
    # Create visualization directory if it doesn't exist
    mkdir -p "${VIZ_OUTPUT_DIR}"
    
    # Run visualization script
    echo "Running visualization script..."
    cd ..
    python3 viz.py "traces/trace-${INVARIANT}.json" "db_diagram/output/graphs/ccgraph-${INVARIANT}"
    
    if [ $? -eq 0 ]; then
        echo "Visualization completed successfully!"
        echo "Output saved to: db_diagram/output/graphs/ccgraph-${INVARIANT}.png"
    else
        echo "Visualization failed!"
    fi
    
    cd bash_scripts
else
    echo "No trace file generated - the invariant was not violated"
fi

# Clean up any trace files generated during this run
echo "Cleaning up trace files generated during this run..."
rm -f ../SnapshotIsolation_TTrace_*.bin ../SnapshotIsolation_TTrace_*.tla
rm -f ../traces/read_only_anomaly.txt