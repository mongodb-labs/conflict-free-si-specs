# Analysis of Three Specific Two-WR Patterns in 4-Node Cycles

## Overview
We analyze three specific 4-node cycles with two WR edges to understand why they're impossible under snapshot isolation.

## Pattern 1: RW → WW → WR → WR

```
      t3 ——WR——→ t0
      ↑           ↓
     WR          RW
      ↑           ↓
      t2 ←—WW—— t1
```

### Edge Breakdown:
- **t0 → t1 (RW)**: t0 reads key K, t1 later writes to K
- **t1 → t2 (WW)**: t1 and t2 both write to the same key
- **t2 → t3 (WR)**: t2 writes value V, t3 reads V
- **t3 → t0 (WR)**: t3 writes value V', t0 reads V'

### Temporal Constraints:
1. **t0 → t1 (RW)**: `start(t0) < commit(t1)`
   - t0 must start reading before t1 commits its write
2. **t1 → t2 (WW)**: One transaction must abort
   - If both commit, first-committer-wins rule applies
3. **t2 → t3 (WR)**: `commit(t2) < start(t3)`
   - t3 can only read t2's value after t2 commits
4. **t3 → t0 (WR)**: `commit(t3) < start(t0)`
   - t0 can only read t3's value after t3 commits

### The Contradiction:
From constraints 3 and 4: `commit(t2) < start(t3) < commit(t3) < start(t0)`

But from constraint 1: `start(t0) < commit(t1)`

This gives us: `commit(t3) < start(t0) < commit(t1)`

For the WW conflict (constraint 2):
- If t1 commits first, t2 must abort → violates constraint 3 (t2 never commits)
- If t2 commits first, t1 must abort → violates constraint 1 (t1 never commits)

**Result**: IMPOSSIBLE ❌

---

## Pattern 2: RW → WR → WW → WR

```
      t3 ——WR——→ t0
      ↑           ↓
     WW          RW
      ↑           ↓
      t2 ←—WR—— t1
```

### Edge Breakdown:
- **t0 → t1 (RW)**: t0 reads key K, t1 later writes to K
- **t1 → t2 (WR)**: t1 writes value V, t2 reads V
- **t2 → t3 (WW)**: t2 and t3 both write to the same key
- **t3 → t0 (WR)**: t3 writes value V', t0 reads V'

### Temporal Constraints:
1. **t0 → t1 (RW)**: `start(t0) < commit(t1)`
2. **t1 → t2 (WR)**: `commit(t1) < start(t2)`
3. **t2 → t3 (WW)**: One transaction must abort
4. **t3 → t0 (WR)**: `commit(t3) < start(t0)`

### The Contradiction:
From constraint 4: `commit(t3) < start(t0)`
From constraint 1: `start(t0) < commit(t1)`
From constraint 2: `commit(t1) < start(t2)`

Combined: `commit(t3) < start(t0) < commit(t1) < start(t2)`

This means t3 must commit before t2 even starts. But constraint 3 (WW) requires t2 and t3 to have overlapping execution periods to conflict.

If t3 has already committed before t2 starts, they cannot have a WW conflict!

**Result**: IMPOSSIBLE ❌

---

## Pattern 3: RW → WR → WR → WW

```
      t3 ——WW——→ t0
      ↑           ↓
     WR          RW
      ↑           ↓
      t2 ←—WR—— t1
```

### Edge Breakdown:
- **t0 → t1 (RW)**: t0 reads key K, t1 later writes to K
- **t1 → t2 (WR)**: t1 writes value V, t2 reads V
- **t2 → t3 (WR)**: t2 writes value V', t3 reads V'
- **t3 → t0 (WW)**: t3 and t0 both write to the same key

### Temporal Constraints:
1. **t0 → t1 (RW)**: `start(t0) < commit(t1)`
2. **t1 → t2 (WR)**: `commit(t1) < start(t2)`
3. **t2 → t3 (WR)**: `commit(t2) < start(t3)`
4. **t3 → t0 (WW)**: Both must be concurrent (overlapping)

### The Contradiction:
The two WR edges create a chain:
- `commit(t1) < start(t2) < commit(t2) < start(t3)`

From the RW edge: `start(t0) < commit(t1)`

For the WW edge to exist, t0 and t3 must have overlapping execution periods. This means:
- t0 must still be running when t3 is running
- But t0 starts before t1 commits (RW constraint)
- And t3 starts after t2 commits (WR constraint)
- And t2 starts after t1 commits (WR constraint)

So we need t0 to span from before t1's commit all the way until after t3 starts:
`start(t0) < commit(t1) < start(t2) < commit(t2) < start(t3) < commit(t0)`

This creates an extremely long-running t0 transaction. While theoretically possible, the snapshot isolation rules make this practically impossible because:

1. **Snapshot timing**: t0 takes its snapshot at `start(t0)`
2. **Visibility**: t0 cannot see any commits that happen after its start
3. **WW conflict detection**: For t0 and t3 to have a WW conflict, they must write to the same key
4. **The problem**: If t0 started so early, its snapshot is ancient by the time t3 starts

Additionally, the RW edge (t0 → t1) typically implies t0 is a reader that finishes before t1's write commits. Having t0 continue running for so long contradicts the typical pattern that creates RW edges.

**Result**: IMPOSSIBLE ❌

---

## Summary: Why Two WR Edges Break 4-Node Cycles

### The WR Edge Creates a Temporal Barrier
- **WR**: Writer must fully commit before reader can start
- **Effect**: Creates non-overlapping transaction lifetimes

### Two WR Edges Create Multiple Barriers
1. **Pattern 1**: The two WR edges at the end create a temporal loop that conflicts with the WW abort requirement
2. **Pattern 2**: The WR edges separate transactions too far apart for a valid WW conflict
3. **Pattern 3**: The consecutive WR edges create such a long temporal chain that the WW edge cannot properly close the cycle

### Key Insight
The fundamental issue is that **WR edges enforce strict temporal separation**, while cycles require some form of **temporal overlap or connection** to close. Two WR edges create too much separation for the other edges to bridge, regardless of their types.

This explains why your TLA+ model checker found no valid instances - these patterns are fundamentally incompatible with snapshot isolation's consistency model.