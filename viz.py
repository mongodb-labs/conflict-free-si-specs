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

def visualize_sergraph(trace_file, output_name="ccgraph"):
    # Read and parse the trace file
    with open(trace_file, 'r') as f:
        trace = json.load(f)["state"]
    
    # Get the last state from trace
    last_state = trace[-1][1]
    print(last_state)
    # Create a new directed graph
    dot = graphviz.Digraph(comment='Serialization Graph')
    dot.attr(rankdir='LR')
    
    # Set higher DPI for better resolution
    dot.attr(dpi='300')
    
    # Extract sergraph edges from the last state
    ccgraph = last_state['ccgraph']
    print(ccgraph)
    
    # Add nodes and edges
    for edge in ccgraph:
        src = edge[0]
        target = edge[1]
        
        # Handle different edge formats
        if len(edge) >= 4:
            # Full format: <<src, target, etype, cclabel>>
            etype = edge[2]
            cclabel = edge[3]
            rwlabel = edge[4]
            if cclabel == "concurrent":
                style = "dashed"
            else:
                style = "solid"
            label = etype
            color = "orange" if rwlabel == "hazardous" else "black"
        elif len(edge) >= 3:
            # Edge with type: <<src, target, etype>>
            etype = edge[2]
            label = etype
            style = "solid"
            color = "black"
        else:
            # Basic edge: <<src, target>>
            label = ""
            style = "solid"
            color = "black"
        
        # Add nodes with larger size and fonts
        dot.node(src, fontsize='14', width='0.5', height='0.5')
        dot.node(target, fontsize='14', width='0.5', height='0.5')
        
        # Add edge with larger font
        dot.edge(src, target, label=label, style=style, color=color, fontsize='12', penwidth='2.0')
    
    # Save the graph in high resolution (only PNG, no DOT file)
    dot.render(output_name, format='png', cleanup=True)

if __name__ == '__main__':
    import sys
    
    if len(sys.argv) > 1:
        trace_file = sys.argv[1]
        output_name = sys.argv[2] if len(sys.argv) > 2 else "ccgraph"
        visualize_sergraph(trace_file, output_name)
    else:
        visualize_sergraph()