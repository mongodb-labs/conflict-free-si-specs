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

So WR→RW in a 3-node cycle isn't inherently impossible!

Wait, let me reconsider. In a 3-node cycle, we need to close back to t0. Let's check all possibilities:

**Pattern: WR → RW → X (where X closes to t0)**

For X to close the cycle from t2 to t0:
- **X = WW**: Possible (as analyzed above)
- **X = RW**: Would need t2 to read before t0 commits, but t0 commits before t1 starts, and t2 starts after t1. This is tight but possible.
- **X = WR**: Would need `commit(t2) < start(t0)`, but we have `commit(t0) < start(t1) < commit(t2)`, giving us `commit(t0) < commit(t2) < start(t0)` - **IMPOSSIBLE!**

So in 3-node cycles, WR→RW→WR is impossible, but WR→RW→WW and WR→RW→RW might be possible!

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

This is possible but highly constrained!

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

This requires t0 to span from before t1 commits all the way until after t4 starts. Given the chain of WR→RW→WR, this is extremely constrained and likely **IMPOSSIBLE**.

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

**WR→RW is not inherently impossible**, but it creates severe constraints that often lead to impossible cycles when combined with:
- Additional WR edges (especially WR→RW→WR)
- Multiple WW edges that require careful timing
- Small cycle sizes that don't provide enough temporal flexibility

The pattern becomes increasingly difficult as:
1. More WR edges are added to the cycle
2. The cycle size is smaller
3. The WR→RW sequence appears near the end of the cycle (making it harder to close back to the start)

In larger cycles with more WW edges and better placement of the WR→RW sequence, it might be possible to create valid instances. But in the cases you've been testing (4-node cycles with specific patterns), the WR→RW sequence, when present, tends to create impossible temporal constraints.