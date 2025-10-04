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

Line(x1, y1, x2, y2, attrs) == 
    (**************************************************************************)
    (* Line element.  'x1', 'y1', 'x2', and 'y2' should be given as integers. *)
    (**************************************************************************)
    LET svgAttrs == [x1 |-> x1, 
                     y1 |-> y1, 
                     x2 |-> x2,
                     y2 |-> y2] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

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
txnGraphWithEdgeTypes == SerializationGraphWithEdgeTypes(txnHistory)
txnGraphEdges == {<<e[1][1], e[1][2], e[2], IF AreConcurrent(txnHistory, e[1][1], e[1][2]) THEN "concurrent" ELSE "not_concurrent", IF HazardousRWEdge(<<e[1][1], e[1][2], "RW">>) THEN "hazardous" ELSE "benign">> : e \in txnGraphWithEdgeTypes}

SerGraphElem == Group(<<DiGraph(txnIds,txnGraphEdges,[n \in txnIds |-> nodeAttrsFn(n)], [e \in txnGraphEdges |-> edgeAttrsFn(e)])>>, [transform |-> "translate(10, 140) scale(0.6)"])

IndexOf(seq, elem) == CHOOSE i \in DOMAIN seq : seq[i] = elem

\* Create a fixed mapping from transaction IDs to y positions
yPos(tid) == IndexOf(SetToSeq(txnIds), tid) - 1


TimelineElem(txnId) ==
    LET txnEvents == SelectSeq(txnHistory, LAMBDA op: op.txnId = txnId)
        eventToElem(event, idx) ==
            LET x == idx * 45
                y == yPos(txnId) * 40 + 10 \* Use the mapped y position
                color == CASE event.type = "begin" -> "blue"
                          [] event.type = "read" -> "gray" 
                          [] event.type = "write" -> "orange"
                          [] event.type = "commit" -> "green"
                          [] OTHER -> "black"
                label == CASE event.type = "begin" -> "B"
                          [] event.type = "read" -> "r(" \o ToString(event.key) \o "," \o ToString(event.val) \o ")"
                          [] event.type = "write" -> "w(" \o ToString(event.key) \o "," \o ToString(event.val) \o ")"
                          [] event.type = "commit" -> "c"
                          [] OTHER -> "?"
            IN Group(<<
                Circle(x, y, 4, ("fill" :> color @@ "z-index" :> "10")),
                Text(x, y + 20, label, ("text-anchor" :> "middle" @@ "font-size" :> "8px"))
            >>, <<>>)
        events == [i \in DOMAIN txnEvents |-> eventToElem(txnEvents[i], IndexOf(txnHistory, txnEvents[i]))]
        \* Find start and end x coordinates for timeline
        startX == IndexOf(txnHistory, CHOOSE op \in Range(txnHistory): op.type = "begin" /\ op.txnId = txnId) * 45
        endX == IF txnId \in CommittedTxns(txnHistory)
                THEN IndexOf(txnHistory, CHOOSE op \in Range(txnHistory): op.type = "commit" /\ op.txnId = txnId) * 45
                ELSE IndexOf(txnHistory, CHOOSE op \in Range(txnHistory): op.txnId = txnId) * 45
        y == yPos(txnId) * 40 + 10
    IN 
    Group(
        (IF (txnId \in CommittedTxns(txnHistory))
    THEN <<Line(startX, y, endX, y, ("stroke" :> "gray" @@ "stroke-width" :> "1"))>>
    ELSE <<>>) \o
        <<
        Text(0, y, ToString(txnId), ("text-anchor" :> "end" @@ "font-size" :> "10px")),
        Group([i \in DOMAIN events |-> events[i]], <<>>)
    >>
    , <<>>)

TimelinesElem == Group(SetToSeq({TimelineElem(txnId) : txnId \in txnIds}), [transform |-> "translate(10, 5) scale(0.7)"])

AnimView == Group(<<
    SerGraphElem
    , 
    TimelinesElem
    >>, 
    [transform |-> "translate(20, 20) scale(1.6)"]
    ) 



====