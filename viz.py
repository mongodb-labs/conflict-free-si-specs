import json
import graphviz

#
# Can run TLC with something like:
#
# tlc -workers 10 -deadlock -simulate -seed 5 -dumpTrace json trace.json -depth 20 SnapshotIsolation
#
# to generation JSON trace file parse-able by this script to generate Graphviz
# version of serialization graph.
#

def visualize_sergraph(trace_file="traces/trace-ThreeNodeCycle.json", output_name="ccgraph"):
    # Read and parse the trace file
    with open(trace_file, 'r') as f:
        trace = json.load(f)["state"]
    
    # Get the last state from trace
    last_state = trace[-1][1]
    print(last_state)
    
    # Create a new directed graph
    dot = graphviz.Digraph(comment='Serialization Graph')
    dot.attr(rankdir='LR')
    
    # Extract sergraph edges from the last state
    ccgraph = last_state['ccgraph']
    print(ccgraph)
    
    # Add nodes and edges
    for edge in ccgraph:
        src = edge[0]
        target = edge[1]
        etype = edge[2]
        cclabel = edge[3]
        dot.node(src)
        dot.node(target)
        if cclabel == "concurrent":
            label = etype + "(C)"
        else:
            label = etype + "(NC)"
        dot.edge(src, target, label=label)
    
    # Save the graph (only PNG, no DOT file)
    dot.render(output_name, format='png', cleanup=True)

if __name__ == '__main__':
    import sys
    
    if len(sys.argv) > 1:
        trace_file = sys.argv[1]
        output_name = sys.argv[2] if len(sys.argv) > 2 else "ccgraph"
        visualize_sergraph(trace_file, output_name)
    else:
        visualize_sergraph()