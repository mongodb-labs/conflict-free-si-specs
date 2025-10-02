---- MODULE SnapshotIsolation_anim ----
EXTENDS TLC, SnapshotIsolation



\* 
\* Animation stuff.
\* 


\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    \* Text element.'x' and 'y' should be given as integers, and 'text' given as a string.
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* Graphviz attributes
nodeAttrsFn(n) == [
    label |-> ToString(n),
    style |-> "filled", 
    fillcolor |-> IF n \in CommittedTxns(txnHistory) THEN "lightgreen" ELSE "lightgray"
]

edgeAttrsFn(e) == [
    label |-> e[3],
    color |-> IF e[5] = "hazardous" THEN "orange" ELSE "black",
    fontsize |-> "8",
    style |-> IF e[4] = "concurrent" THEN "dashed" ELSE "solid"
]

txnGraph == SerializationGraph(txnHistory)

allCommittedTxnIds == CommittedTxns(txnHistory)

\* Alternate def of above.
txnGraphWithEdgeTypes == 
    {e \in (allCommittedTxnIds \X allCommittedTxnIds \X {"WW", "WR", "RW"}):
        /\ e[1][1] /= e[1][2]
        /\ \/ (e[2] = "WW" /\ WWDependency(txnHistory, e[1][1], e[1][2]))
           \/ (e[2] = "WR" /\ WRDependency(txnHistory, e[1][1], e[1][2]))
           \/ (e[2] = "RW" /\ RWDependency(txnHistory, e[1][1], e[1][2]))}
txnGraphEdges == {<<e[1][1], e[1][2], e[2], IF AreConcurrent(txnHistory, e[1][1], e[1][2]) THEN "concurrent" ELSE "not_concurrent", IF HazardousRWEdge(<<e[1][1], e[1][2], "RW">>) THEN "hazardous" ELSE "benign">> : e \in txnGraphWithEdgeTypes}
AnimView == Group(<<DiGraph(txnIds,txnGraphEdges,[n \in txnIds |-> nodeAttrsFn(n)], [e \in txnGraphEdges |-> edgeAttrsFn(e)])>>, [transform |-> "translate(40, 40) scale(1.5)"])



====