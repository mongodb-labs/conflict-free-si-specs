# Analysis: Why RW→WW→WR→WW and RW→WW→WW→WR Are Impossible

## Overview
These two 4-node cycle patterns have been explored for over 200 million states without finding a valid instance. Let's analyze why they're impossible under snapshot isolation.

## Pattern 1: RW → WW → WR → WW

```
      t3 ——WW——→ t0
      ↑           ↓
     WR          RW
      ↑           ↓
      t2 ←—WW—— t1
```

### Edge Breakdown:
- **t0 → t1 (RW)**: t0 reads key K, t1 later writes to K
- **t1 → t2 (WW)**: t1 and t2 both write to the same key
- **t2 → t3 (WR)**: t2 writes value V, t3 reads V
- **t3 → t0 (WW)**: t3 and t0 both write to the same key

### Temporal Constraints:
1. **t0 → t1 (RW)**: `start(t0) < commit(t1)`
   - t0 must start before t1 commits
   
2. **t1 → t2 (WW)**: Both transactions write to same key
   - Under SI: first-committer-wins rule applies
   - They must have overlapping execution periods
   - One must abort
   
3. **t2 → t3 (WR)**: `commit(t2) < start(t3)`
   - t3 can only read t2's value after t2 commits
   
4. **t3 → t0 (WW)**: Both transactions write to same key
   - They must have overlapping execution periods
   - One must abort

### The Core Contradiction:

From constraint 3: `commit(t2) < start(t3)` (t2 must finish before t3 starts)

For the WW edge (t3 → t0) to exist, t3 and t0 must have overlapping execution periods.

But from constraint 1: `start(t0) < commit(t1)`

If t1 and t2 have a WW conflict:
- **Case A**: If t1 commits first, then t2 aborts
  - But then t2 never commits, violating the WR edge (t2 → t3)
  
- **Case B**: If t2 commits first, then t1 aborts
  - But then t1 never commits, violating the RW edge (t0 → t1)

Additionally, even if we could resolve the WW conflicts, we'd need:
- t0 to start early (before t1 commits)
- t0 to still be running when t3 is running (for their WW conflict)
- But t3 doesn't start until after t2 commits
- And t2 can't commit until after its WW conflict with t1 is resolved

This creates an impossible temporal chain where t0 would need to span an unreasonably long time while other transactions abort or complete in sequence.

**Result: IMPOSSIBLE** ❌

---

## Pattern 2: RW → WW → WW → WR

```
      t3 ——WR——→ t0
      ↑           ↓
     WW          RW
      ↑           ↓
      t2 ←—WW—— t1
```

### Edge Breakdown:
- **t0 → t1 (RW)**: t0 reads key K, t1 later writes to K
- **t1 → t2 (WW)**: t1 and t2 both write to the same key
- **t2 → t3 (WW)**: t2 and t3 both write to the same key
- **t3 → t0 (WR)**: t3 writes value V, t0 reads V

### Temporal Constraints:
1. **t0 → t1 (RW)**: `start(t0) < commit(t1)`
   
2. **t1 → t2 (WW)**: Overlapping execution, one must abort
   
3. **t2 → t3 (WW)**: Overlapping execution, one must abort
   
4. **t3 → t0 (WR)**: `commit(t3) < start(t0)`
   - t0 can only read t3's value after t3 commits

### The Fatal Contradiction:

From constraint 4: `commit(t3) < start(t0)`
From constraint 1: `start(t0) < commit(t1)`

This gives us: `commit(t3) < start(t0) < commit(t1)`

Now consider the two WW edges:
- t1 and t2 must have overlapping execution for their WW conflict
- t2 and t3 must have overlapping execution for their WW conflict

But we've established that t3 must commit before t0 even starts, and t0 starts before t1 commits.

So we need: `commit(t3) < start(t0) < commit(t1)`

For the WW conflicts to exist:
- t1 and t2 must overlap
- t2 and t3 must overlap

This would require a chain where:
- t3 is running (before it commits)
- t2 is running (overlapping with t3)
- t1 is running (overlapping with t2)
- But t3 must commit before t0 starts
- And t0 must start before t1 commits

This creates a temporal impossibility: we need t3 to commit before t1 commits (via the chain t3 < t0 < t1), but also need them to be connected via overlapping WW conflicts through t2.

**Result: IMPOSSIBLE** ❌

---

## Key Insights

### Why These Patterns Fail

1. **WW Edges Require Concurrency**: Unlike WR edges that create clean temporal breaks, WW edges require transactions to be running simultaneously.

2. **The WR Edge Creates a Barrier**: In both patterns, the single WR edge creates a strict temporal ordering that conflicts with the concurrency requirements of multiple WW edges.

3. **Abort Cascades**: WW conflicts under snapshot isolation mean one transaction must abort. In these patterns, any abort breaks other required edges.

### Pattern Comparison

Both patterns share a critical flaw:
- They try to combine multiple WW edges (requiring concurrency) with edges that enforce strict temporal ordering (RW and WR)
- The temporal constraints become over-constrained, making the patterns impossible

### Why TLC Can't Find Instances

Your TLC model checker has explored 200+ million states without finding a valid instance because these patterns are mathematically impossible under snapshot isolation's consistency rules. The constraints simply cannot be satisfied simultaneously.

## General Rule

These analyses suggest a general principle:
- **Multiple WW edges in a cycle create complex concurrency requirements**
- **When combined with WR edges (strict temporal ordering), the patterns often become impossible**
- **The specific arrangement matters**: some combinations of 2 WW + 1 WR might work, but these specific patterns don't

This explains why your model checker continues searching without success - it's looking for something that cannot exist under snapshot isolation's fundamental rules.