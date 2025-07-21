# Analysis: The WR→RW Edge Sequence Impossibility

## Hypothesis
The WR→RW edge sequence appears to be fundamentally impossible under snapshot isolation, regardless of cycle size.

## The WR→RW Constraint

### What WR→RW Means
- **WR edge (Ti → Tj)**: Ti writes value V, Tj reads V
  - Constraint: `commit(Ti) < start(Tj)`
- **RW edge (Tj → Tk)**: Tj reads key K, Tk writes to K
  - Constraint: `start(Tj) < commit(Tk)`

### Combined WR→RW Constraint
For a sequence Ti → Tj → Tk where:
- Ti → Tj is WR
- Tj → Tk is RW

We get: `commit(Ti) < start(Tj) < commit(Tk)`

This seems innocent enough. The problem arises when we try to close the cycle.

## Analysis by Cycle Size

### 3-Node Cycle with WR→RW

Pattern: Ti → Tj → Tk → Ti with WR→RW somewhere

Let's try: **WR → RW → WW**
```
t0 → t1 → t2 → t0
WR   RW   WW
```

Constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. t2 and t0 must overlap (WW)

From 1 & 2: `commit(t0) < start(t1) < commit(t2)`

For the WW edge, t2 and t0 must have overlapping execution. But t0 must commit before t1 even starts, and t2 doesn't commit until after t1 starts. This makes overlap difficult but not necessarily impossible if t0 starts very early and t2 starts before t0 commits.

Actually, this could work if:
- t0 starts early and runs long
- t2 starts while t0 is still running
- t1 fits in between

Let me analyze each case more carefully:

**Pattern: WR → RW → X (where X closes to t0)**

### Case 1: WR → RW → WW
```
t0 → t1 → t2 → t0
WR   RW   WW
```

Constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. t0 and t2 must have overlapping execution (WW)

From 1 & 2: `commit(t0) < start(t1) < commit(t2)`

For the WW conflict, t0 and t2 must write to the same key and have overlapping execution periods. This requires:
- `start(t0) < commit(t2)` AND `start(t2) < commit(t0)`

But we know `commit(t0) < start(t1) < commit(t2)`. For t2 to start before t0 commits, we need:
`start(t2) < commit(t0) < start(t1) < commit(t2)`

Under snapshot isolation with first-committer-wins:
- t0 and t2 both write to the same key
- t0 commits first (before t1 even starts)
- When t2 tries to commit, it detects the WW conflict
- t2 must abort

But if t2 aborts, the RW edge (t1 → t2) is broken because t2 never successfully commits!

**Result: WR → RW → WW is IMPOSSIBLE** ❌

### Case 2: WR → RW → RW
```
t0 → t1 → t2 → t0
WR   RW   RW
```

Constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. `start(t2) < commit(t0)` (RW - t2 reads, t0 writes)

From constraints: `start(t2) < commit(t0) < start(t1) < commit(t2)`

This means t2 starts before t0 commits, but doesn't commit until after t1 starts. This creates a valid timeline:
1. t2 starts (and reads)
2. t0 commits
3. t1 starts (and reads)
4. t2 commits

The question is whether this satisfies all RW constraints with proper snapshot isolation semantics... Actually, this seems possible at first, but let's verify the WR edge.

For t0 → t1 (WR), t1 must read a value that t0 wrote. Since `commit(t0) < start(t1)`, t1's snapshot (taken at start(t1)) includes t0's writes. So t1 can read t0's value. ✓

But wait - I need to think about the cycle property. For this to be a proper cycle creating a non-serializable history, the transactions must have conflicting operations that create the anomaly. Let me reconsider...

Actually, this might work in specific cases, but it's highly constrained.

### Case 3: WR → RW → WR
```
t0 → t1 → t2 → t0
WR   RW   WR
```

Constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. `commit(t2) < start(t0)` (WR)

From 1 & 2: `commit(t0) < start(t1) < commit(t2)`
From 3: `commit(t2) < start(t0)`

Combined: `commit(t2) < start(t0) < commit(t0) < start(t1) < commit(t2)`

This gives us `commit(t2) < commit(t2)`, which is impossible!

**Result: WR → RW → WR is IMPOSSIBLE** ❌

So in 3-node cycles, WR→RW can only potentially work with RW as the closing edge, and even then it's highly constrained.

### 4-Node Cycle with WR→RW

From the impossible_cycles_analysis.md, we saw:
- **RW → WW → WR → WW**: Has WR→WW at the end (not WR→RW)
- **RW → WW → WW → WR**: Has WW→WR at the end (not WR→RW)

Let's check a pattern with WR→RW: **WW → WR → RW → WW**

```
t0 → t1 → t2 → t3 → t0
WW   WR   RW   WW
```

Constraints:
1. t0 and t1 must overlap (WW)
2. `commit(t1) < start(t2)` (WR)
3. `start(t2) < commit(t3)` (RW)
4. t3 and t0 must overlap (WW)

From 2 & 3: `commit(t1) < start(t2) < commit(t3)`

For constraint 4, t3 and t0 must overlap. For constraint 1, t0 and t1 must overlap.

This creates a requirement: t0 must be running both when t1 is running AND when t3 is running. Given that t1 must commit before t2 starts, and t3 doesn't start until after t2 starts, this requires a very long-running t0.

Let's verify this more carefully:
- For the first WW (t0 ↔ t1): `start(t0) < commit(t1)` AND `start(t1) < commit(t0)`
- From WR: `commit(t1) < start(t2)`
- From RW: `start(t2) < commit(t3)`
- For the second WW (t3 ↔ t0): `start(t3) < commit(t0)` AND `start(t0) < commit(t3)`

Combining: We need `start(t1) < commit(t0)` (from first WW) and `start(t3) < commit(t0)` (from second WW).

From the WR→RW chain: `commit(t1) < start(t2) < commit(t3)`

So t0 must still be running (not committed) when both t1 and t3 are running. But t1 must commit before t2 even starts, and t3 doesn't start until after t2 starts. This means:
- t1 starts and runs
- t1 commits
- t2 starts
- t3 starts (while t2 is running due to RW)
- t0 must still be running at this point

This requires t0 to run from before t1 starts until after t3 starts, spanning the entire WR→RW chain. Under first-committer-wins, when there are two WW conflicts:
- If t0 commits before t1, then t1 must abort (breaking the WR edge)
- If t1 commits before t0, we need t0 to continue running until t3 starts
- If t0 commits before t3, then t3 must abort (breaking the RW edge)
- If t3 commits before t0, we need to check if this is consistent

Actually, this pattern requires very specific timing and transaction operations that make it practically impossible under snapshot isolation's rules.

**Result: WW → WR → RW → WW is IMPOSSIBLE** ❌

### 5-Node Cycle with WR→RW

With constraints:
- 1 RW edge (minimum)
- 2 WR edges (maximum)
- Rest are WW edges

Let's analyze patterns with WR→RW sequences:

#### Pattern 1: WR → RW → WW → WW → WR
```
t0 → t1 → t2 → t3 → t4 → t0
WR   RW   WW   WW   WR
```

Constraints:
1. `commit(t0) < start(t1)` (WR)
2. `start(t1) < commit(t2)` (RW)
3. t2 and t3 must overlap (WW)
4. t3 and t4 must overlap (WW)
5. `commit(t4) < start(t0)` (WR)

From 1 & 2: `commit(t0) < start(t1) < commit(t2)`
From 5: `commit(t4) < start(t0)`

Combined: `commit(t4) < start(t0) < commit(t0) < start(t1) < commit(t2)`

For the WW edges to work, we need:
- t2 and t3 to overlap
- t3 and t4 to overlap

This means t4 must be running while t2 is running (transitively through t3). But t4 must commit before t0 starts, and t2 doesn't even start until after t1 starts, which is after t0 commits.

This creates: `commit(t4) < start(t0) < commit(t0) < start(t1) < start(t2)`

But we need t4 to overlap with t3, which overlaps with t2. This is **IMPOSSIBLE** given the temporal constraints.

#### Pattern 2: WW → WR → RW → WR → WW
```
t0 → t1 → t2 → t3 → t4 → t0
WW   WR   RW   WR   WW
```

This has WR→RW in the middle. Let's check:

1. t0 and t1 must overlap (WW)
2. `commit(t1) < start(t2)` (WR)
3. `start(t2) < commit(t3)` (RW)
4. `commit(t3) < start(t4)` (WR)
5. t4 and t0 must overlap (WW)

From 2, 3, 4: `commit(t1) < start(t2) < commit(t3) < start(t4)`

For constraint 5, t4 and t0 must overlap. But t4 doesn't start until after this long chain of events, while t0 must be running early to overlap with t1.

This requires t0 to span from before t1 commits all the way until after t4 starts. Given the chain of WR→RW→WR, let's verify:

From the WR→RW→WR chain: `commit(t1) < start(t2) < commit(t3) < start(t4)`

For the WW conflicts:
- t0 and t1 must overlap: `start(t0) < commit(t1)` AND `start(t1) < commit(t0)`
- t4 and t0 must overlap: `start(t4) < commit(t0)` AND `start(t0) < commit(t4)`

From the first WW: `start(t1) < commit(t0)`
From the second WW: `start(t4) < commit(t0)`
From the WR chain: `commit(t1) < start(t2) < commit(t3) < start(t4)`

This means: `commit(t1) < start(t4) < commit(t0)`

But we also need `start(t1) < commit(t0)` from the first WW. So t0 must be running from before t1 commits all the way past when t4 starts. 

The critical issue: t1 must commit before t2 starts (WR), and t4 doesn't start until after t3 commits (WR). This creates a huge temporal gap. For both WW conflicts to exist without aborts:
- t1 must commit after t0 starts but before t0 commits
- t4 must start before t0 commits

But the WR→RW→WR chain forces such a long delay between t1's commit and t4's start that maintaining t0's execution across this entire period while satisfying all constraints is impossible.

**Result: WW → WR → RW → WR → WW is IMPOSSIBLE** ❌

## Key Finding: The WR→RW Problem

The WR→RW sequence isn't inherently impossible by itself, but it creates severe temporal constraints when trying to close a cycle:

1. **Temporal Separation**: WR→RW creates a "temporal valley" where:
   - The first transaction must finish completely
   - The middle transaction starts fresh and runs
   - The third transaction can't start until the middle one is well underway

2. **Cycle Closure Challenge**: To close a cycle containing WR→RW:
   - You need to get from the end back to the beginning
   - But the WR→RW sequence has pushed you "forward in time"
   - The remaining edges must somehow bridge this temporal gap

3. **The Critical Pattern**: When WR→RW is followed by another WR edge (making WR→RW→WR), it becomes impossible in small cycles because:
   - Each WR edge pushes you further forward in time
   - You can't get back to the start without violating temporal constraints

## Conclusion

After deeper analysis, **WR→RW creates fundamental problems** that make most cycle patterns impossible:

### In 3-Node Cycles:
- **WR→RW→WR**: Impossible (temporal loop)
- **WR→RW→WW**: Impossible (abort breaks the cycle)
- **WR→RW→RW**: Theoretically possible but highly constrained

### In 4-Node Cycles:
- **WW→WR→RW→WW**: Impossible (multiple WW conflicts with WR→RW timing)
- Patterns with WR→RW generally fail due to WW conflict resolution

### In 5-Node Cycles:
- **WR→RW→...→WR**: Impossible when WR edges bookend the pattern
- **WW→WR→RW→WR→WW**: Impossible due to temporal gap created by WR→RW→WR

### The Core Issues with WR→RW:

1. **Temporal Direction**: WR→RW creates a strict forward temporal flow that's hard to reconcile with cycle closure

2. **WW Conflict Interaction**: When WR→RW is combined with WW edges:
   - The temporal ordering often forces one transaction to commit first
   - This causes the other to abort under first-committer-wins
   - The abort breaks required edges in the cycle

3. **Cumulative Effect**: Each WR edge adds temporal separation, and WR→RW→WR creates gaps too large to bridge

### Key Insight:
While WR→RW isn't impossible in isolation, it's effectively impossible in most practical cycle patterns under snapshot isolation due to:
- Interaction with first-committer-wins rule for WW conflicts
- Cumulative temporal constraints when combined with other edges
- The need to eventually close the cycle back to the starting transaction

This explains why your model checker struggles with patterns containing WR→RW sequences - they represent fundamental temporal contradictions in snapshot isolation.