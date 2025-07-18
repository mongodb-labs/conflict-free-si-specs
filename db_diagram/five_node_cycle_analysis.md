# Analysis: Two WR Edges in 5-Node Cycles Under Snapshot Isolation

## Question
Does the impossibility of 2 WR edges in a 4-node cycle extend to 5-node cycles? Or does the extra node provide enough "temporal flexibility" to make such cycles possible?

## Initial Hypothesis
With 5 nodes, we have more edges and potentially more ways to arrange the temporal constraints. The key question is whether the additional node provides enough temporal "buffer" to bridge the gaps created by two WR edges.

## Key Insight from 4-Node Analysis
In 4-node cycles, two WR edges fail because:
1. WR edges create strict temporal separation (commit before start)
2. Two WR edges create a long temporal chain
3. The remaining edges cannot bridge this temporal gap to close the cycle

## 5-Node Cycle Analysis

### Total Edge Combinations
In a 5-node cycle, we have:
- 5 edges total
- 2 are WR edges (given)
- At least 1 must be RW edge (required for any SI cycle)
- 2 remaining edges can be: RW, WW, or additional WR

### Case 1: Non-Adjacent WR Edges
Let's analyze a pattern like: RW → WW → WR → RW → WR

```
t0 → t1 → t2 → t3 → t4 → t0
RW   WW   WR   RW   WR
```

**Temporal Constraints:**
1. t0 → t1 (RW): `start(t0) < commit(t1)`
2. t1 → t2 (WW): One must abort
3. t2 → t3 (WR): `commit(t2) < start(t3)`
4. t3 → t4 (RW): `start(t3) < commit(t4)`
5. t4 → t0 (WR): `commit(t4) < start(t0)`

**Analysis:**
- From WR edges: `commit(t2) < start(t3)` and `commit(t4) < start(t0)`
- From RW edges: `start(t0) < commit(t1)` and `start(t3) < commit(t4)`
- Combined: `commit(t4) < start(t0) < commit(t1)`
- And: `commit(t2) < start(t3) < commit(t4)`
- This gives us: `commit(t2) < start(t3) < commit(t4) < start(t0) < commit(t1)`

For the WW edge (t1 → t2), we need t1 and t2 to have concurrent execution. But our constraints show t1 commits after t0 starts, while t2 must commit before t3 starts. The question is whether t1 and t2 can overlap.

This is **POSSIBLE** if t2 starts early enough and t1 starts late enough. The extra node provides the temporal flexibility needed.

### Case 2: Adjacent WR Edges
Pattern: RW → WR → WR → WW → RW

```
t0 → t1 → t2 → t3 → t4 → t0
RW   WR   WR   WW   RW
```

**Temporal Constraints:**
1. t0 → t1 (RW): `start(t0) < commit(t1)`
2. t1 → t2 (WR): `commit(t1) < start(t2)`
3. t2 → t3 (WR): `commit(t2) < start(t3)`
4. t3 → t4 (WW): Concurrent execution required
5. t4 → t0 (RW): `start(t4) < commit(t0)`

**Analysis:**
- Adjacent WR edges create: `commit(t1) < start(t2) < commit(t2) < start(t3)`
- From first RW: `start(t0) < commit(t1)`
- From last RW: `start(t4) < commit(t0)`

For this to work, we need:
- t3 and t4 to be concurrent (for WW)
- t4 to start before t0 commits
- t0 to start before t1 commits
- t3 to start after t2 commits

The challenge is that t3 starts very late (after the WR chain), but needs to be concurrent with t4, which must start before t0 commits. But t0 started before t1 commits, which is before the WR chain even begins.

This creates a temporal span requirement: t0 must run from before t1 commits all the way until after t4 starts. Meanwhile, t4 must be concurrent with t3, which doesn't start until after t2 commits.

This is **POTENTIALLY POSSIBLE** with very long-running transactions, but highly constrained.

### Case 3: Three WR Edges in 5-Node Cycle
What if we had 3 WR edges? Pattern: WR → WR → WR → RW → RW

```
t0 → t1 → t2 → t3 → t4 → t0
WR   WR   WR   RW   RW
```

**Temporal Constraints:**
1. t0 → t1 (WR): `commit(t0) < start(t1)`
2. t1 → t2 (WR): `commit(t1) < start(t2)`
3. t2 → t3 (WR): `commit(t2) < start(t3)`
4. t3 → t4 (RW): `start(t3) < commit(t4)`
5. t4 → t0 (RW): `start(t4) < commit(t0)`

**Analysis:**
The WR chain creates: `commit(t0) < start(t1) < commit(t1) < start(t2) < commit(t2) < start(t3)`

From the RW edges:
- `start(t3) < commit(t4)` 
- `start(t4) < commit(t0)`

But we also have `commit(t0) < start(t1) < ... < start(t3)`, which means:
`commit(t0) < start(t3)`

Combined with the RW constraints:
`start(t4) < commit(t0) < start(t3) < commit(t4)`

This gives us `start(t4) < start(t3)` AND `start(t3) < commit(t4)`, which means t3 starts after t4 starts but before t4 commits. This is fine.

But now consider: we need `start(t4) < commit(t0) < start(t1)`. This means t4 starts before t0 commits, and t0 commits before t1 starts. Given the long WR chain from t0 to t3, and then t3 feeds into t4, we need to check if this is possible.

Actually, this is **IMPOSSIBLE** because we have a cycle:
- t0 must commit before t1 starts (WR)
- Eventually through the chain, t3 starts after all the WR edges
- t4 starts before t0 commits (RW)
- But t3 must start before t4 commits (RW)

The ordering `start(t4) < commit(t0) < ... < start(t3) < commit(t4)` means t4 would need to start before t3 starts but commit after t3 starts. Combined with the long WR chain, this creates a temporal loop that cannot be satisfied.

## Key Findings

### 5-Node Cycles CAN Support 2 WR Edges!

Unlike 4-node cycles, 5-node cycles can potentially support 2 WR edges because:

1. **Extra Temporal Flexibility**: The additional node provides more "room" in the temporal ordering
2. **More Edge Combinations**: With 5 edges total, there are more ways to arrange the non-WR edges
3. **Buffering Effect**: The extra edges can act as temporal "buffers" between the WR edges

### But 3 or More WR Edges Likely Remain Impossible

When you have 3 or more WR edges in a 5-node cycle:
- The WR chain becomes too long
- The temporal separation becomes unbridgeable
- The remaining edges cannot close the cycle

### Critical Difference from 4-Node Cycles

In 4-node cycles with 2 WR edges:
- You only have 2 remaining edges to work with
- These 2 edges cannot bridge the temporal gap created by 2 WR edges

In 5-node cycles with 2 WR edges:
- You have 3 remaining edges to work with
- At least 1 must be RW (required for cycles in SI)
- The remaining 2 edges provide additional flexibility
- This combination provides enough flexibility to potentially bridge the gap
- Long-running transactions become more feasible with the extra node

## Conclusion

The impossibility of 2 WR edges is **specific to 4-node cycles** and does not necessarily extend to 5-node cycles. The extra node and additional edge provide enough temporal flexibility to potentially accommodate 2 WR edges, though the specific arrangement matters.

This suggests that the "magic number" for WR edges in cycles is related to the cycle length:
- 4-node cycles: Maximum 1 WR edge
- 5-node cycles: Maximum 2 WR edges (potentially)
- n-node cycles: Maximum ⌊(n-1)/2⌋ WR edges (hypothesis)

The fundamental constraint remains: WR edges create temporal separation, and too many of them relative to the cycle size will make it impossible to close the cycle.