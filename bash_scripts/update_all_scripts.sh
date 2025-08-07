#!/bin/bash

# Script to update all TLC runner scripts to include visualization

echo "Updating all bash scripts to include visualization step..."

# Find all .sh files that contain the TLC command pattern
for script in *.sh; do
    # Skip this script and the template
    if [[ "$script" == "update_all_scripts.sh" || "$script" == "run_with_viz.sh" ]]; then
        continue
    fi
    
    # Check if the script contains TLC command
    if grep -q "tlc -simulate" "$script"; then
        echo "Updating $script..."
        
        # Check if visualization code already exists
        if grep -q "viz.py" "$script"; then
            echo "  - Already contains visualization code, skipping"
            continue
        fi
        
        # Add visualization code before the final cleanup
        # First, create a temporary file with the new content
        awk '
        /^# Clean up any trace files generated during this run/ {
            print "# Check if trace file was generated and run visualization"
            print "TRACE_FILE=\"../traces/trace-${INVARIANT}.json\""
            print "VIZ_OUTPUT_DIR=\"../db_diagram/output/graphs\""
            print ""
            print "if [ -f \"${TRACE_FILE}\" ]; then"
            print "    echo \"Trace file generated successfully: ${TRACE_FILE}\""
            print "    "
            print "    # Create visualization directory if it doesn'\''t exist"
            print "    mkdir -p \"${VIZ_OUTPUT_DIR}\""
            print "    "
            print "    # Run visualization script"
            print "    echo \"Running visualization script...\""
            print "    cd .."
            print "    python3 viz.py \"traces/trace-${INVARIANT}.json\" \"db_diagram/output/graphs/ccgraph-${INVARIANT}\""
            print "    "
            print "    if [ $? -eq 0 ]; then"
            print "        echo \"Visualization completed successfully!\""
            print "        echo \"Output saved to: db_diagram/output/graphs/ccgraph-${INVARIANT}.png\""
            print "    else"
            print "        echo \"Visualization failed!\""
            print "    fi"
            print "    "
            print "    cd bash_scripts"
            print "else"
            print "    echo \"No trace file generated - the invariant was not violated\""
            print "fi"
            print ""
        }
        { print }
        ' "$script" > "${script}.tmp"
        
        # Replace the original file
        mv "${script}.tmp" "$script"
        chmod +x "$script"
        
        echo "  - Updated successfully"
    fi
done

echo "All scripts updated!"
echo ""
echo "To run any script with visualization:"
echo "  cd bash_scripts"
echo "  ./<script_name>.sh"
echo ""
echo "Visualizations will be saved to: ../db_diagram/output/graphs/"