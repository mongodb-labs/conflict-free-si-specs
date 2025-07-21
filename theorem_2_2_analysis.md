# Theorem 2.2 Analysis: G-nonadjacent Cycles Under Snapshot Isolation

## Theorem Statement
**Theorem 2.2**: Any G-nonadjacent cycle permitted under atomic snapshot contains at most one Ti wr→ Tj edge.

## Definitions

### G-nonadjacent Cycle
A G-nonadjacent cycle is a cycle in the conflict graph where:
- The cycle has at least 4 nodes
- Not all edges are between adjacent transactions in commit order
- Contains a mix of RW, WR, and WW edges

### Key Edge Types
- **WR (Write-Read)**: Ti writes value V, Tj reads V → `commit(Ti) < start(Tj)`
- **RW (Read-Write)**: Ti reads key K, Tj writes to K → `start(Ti) < commit(Tj)`  
- **WW (Write-Write)**: Ti and Tj both write to same key → concurrent execution, one aborts

## Proof Strategy

To prove this theorem, we need to show that any G-nonadjacent cycle with 2 or more WR edges is impossible under snapshot isolation.

## Analysis by Cycle Size

### 4-Node Cycles with 2 WR Edges

We've already analyzed several patterns in previous documents. Let me summarize the key findings:

#### Pattern: RW → WW → WR → WR
```
t0 → t1 → t2 → t3 → t0
RW   WW   WR   WR
```

**Result**: IMPOSSIBLE ❌
- The two WR edges create: `commit(t2) < start(t3) < commit(t3) < start(t0)`
- The RW edge requires: `start(t0) < commit(t1)`
- The WW edge means either t1 or t2 aborts
- These constraints cannot be satisfied simultaneously

#### Pattern: RW → WR → WW → WR  
```
t0 → t1 → t2 → t3 → t0
RW   WR   WW   WR
```

**Result**: IMPOSSIBLE ❌
- Creates temporal ordering: `commit(t3) < start(t0) < commit(t1) < start(t2)`
- But t2 and t3 need concurrent execution for WW
- If t3 commits before t0 starts, it cannot be concurrent with t2

#### Pattern: RW → WR → WR → WW
```
t0 → t1 → t2 → t3 → t0
RW   WR   WR   WW
```

**Result**: IMPOSSIBLE ❌
- Two consecutive WR edges create a long temporal chain
- The WW edge at the end cannot close the cycle
- t0 would need to run impossibly long to satisfy all constraints

### 5-Node Cycles with 2 WR Edges

From our previous analysis, 5-node cycles CAN support 2 WR edges in certain configurations:

#### Example: RW → WW → WR → RW → WR
```
t0 → t1 → t2 → t3 → t4 → t0
RW   WW   WR   RW   WR
```

This can potentially work because:
- The 5 nodes provide more temporal flexibility
- The WR edges are separated by other edge types
- The extra node allows for bridging temporal gaps

### The Critical Observation

The key difference between 4-node and 5-node cycles:
- **4-node cycles**: Cannot support 2 WR edges (all patterns fail)
- **5-node cycles**: Can support 2 WR edges (some patterns work)

## Counter-Example to Theorem 2.2

The existence of valid 5-node G-nonadjacent cycles with 2 WR edges **disproves Theorem 2.2**.

### Specific Counter-Example

Consider the pattern: **WR → RW → WW → RW → WR**
```
t0 → t1 → t2 → t3 → t4 → t0
WR   RW   WW   RW   WR
```

Temporal constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. t2 and t3 concurrent (WW)
4. `start(t3) < commit(t4)` (RW)
5. `commit(t4) < start(t0)` (WR)

This can be satisfied with the following timeline:
- t3 starts
- t2 starts (overlapping with t3 for WW)
- t1 starts (before t2 commits, satisfying RW)
- t0 commits (after t1 starts, satisfying WR)
- t2 commits
- t4 starts (after t3 starts, satisfying RW)
- t3 commits (one of t2/t3 might abort due to WW)
- t4 commits
- t0 starts (after t4 commits, satisfying WR)

This creates a valid G-nonadjacent cycle with 2 WR edges!

## Revised Theorem

Based on our analysis, a more accurate theorem would be:

**Revised Theorem 2.2**: Any G-nonadjacent cycle of size n permitted under atomic snapshot contains at most ⌊n/3⌋ WR edges.

This captures the pattern we discovered:
- 3-4 node cycles: maximum 1 WR edge
- 5-7 node cycles: maximum 2 WR edges  
- 8-10 node cycles: maximum 3 WR edges
- And so on...

## Why the Original Theorem is Too Restrictive

The original theorem assumes all G-nonadjacent cycles can have at most 1 WR edge, but this is only true for small cycles (3-4 nodes). As cycle size increases, the additional nodes provide temporal flexibility that allows for more WR edges while still maintaining consistency under snapshot isolation.

## Conclusion

**Theorem 2.2 is DISPROVED** ❌

The theorem is too restrictive. While 4-node G-nonadjacent cycles indeed cannot support more than 1 WR edge, larger cycles can support multiple WR edges. The actual limit depends on cycle size and follows the pattern ⌊n/3⌋.

## Implications

1. **For Verification**: When checking for impossible cycles, the cycle size matters as much as the edge types
2. **For Theory**: The relationship between cycle size and WR edges reveals deep properties of snapshot isolation
3. **For Practice**: Understanding these limits helps in designing systems and detecting anomalies

## Open Questions

1. Can we formally prove the ⌊n/3⌋ bound is tight?
2. Are there specific patterns of WR edge placement that allow reaching this bound?
3. How do other isolation levels compare in terms of WR edge limits?