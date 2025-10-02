------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(*                                                                                                *)
(* This is a specification for Snapshot Isolation. It is based on ongoing work by Will Schultz    *)
(* and Sai Achalla on the topic of re-defining snapshot isolation in terms of re-execution.       *)
(* This spec refers to the following papers for definitions and implementation ideas:             *)
(*                                                                                                *)
(* "Serializable Snapshot Isolation" - https://arxiv.org/pdf/1208.4179                            *)
(*                                                                                                *)
(* "Analyzing Snapshot Isolation" - https://software.imdea.org/~gotsman/papers/si-podc16.pdf      *)
(*                                                                                                *)
(* "Transaction Healing - Scaling Optimistic Concurrency Control on multicores" -                 *)
(* https://yingjunwu.github.io/papers/sigmod2016.pdf                                              *)
(*                                                                                                *)
(* "Morty: Scaling Concurrency Control with Re-execution" -                                       *)
(* https://www.cs.cornell.edu/~matthelb/papers/morty-eurosys23.pdf                                *)
(*                                                                                                *)
(* The idea behind a re-execution based approach to Snapshot Isolation is so that we can avoid    *)
(* aborting transactions and instead only re-execute parts of them by re-doing reads that are     *)
(* found to be stale at commit time.                                                              *)
(**************************************************************************************************)


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks) 
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The full history of all transaction operations. It is modeled as a linear 
\* sequence of events. Such a history would likely never exist in a real implementation, 
\* but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

\* (NOT NECESSARY)
\* The key-value data store. In this spec, we model a data store explicitly, even though it is not actually
\* used for the verification of any correctness properties. This was added initially as an attempt the make the
\* spec more intuitive and understandable. It may play no important role at this point, however. If a property
\* check was ever added for view serializability, this, and the set of transaction snapshots, may end up being
\* useful.
VARIABLE dataStore

\* (NOT NECESSARY)
\* The set of snapshots needed for all running transactions. Each snapshot 
\* represents the entire state of the data store as of a given point in time. 
\* It is a function from transaction ids to data store snapshots. This, like the 'dataStore' variable, may 
\* now be obsolete for a spec at this level of abstraction, since the correctness properties we check do not 
\* depend on the actual data being read/written.
VARIABLE txnSnapshots

\* All the variables that are used in the new RW edge detection definition of Snapshot Isolation are defined below.

\* The set of all incoming edges to a given transaction. Used to detect dangerous edge sequences in the algorithm.
VARIABLE incomingEdges

\* The set of all outgoing edges from a given transaction. Used to detect dangerous edge sequences in the algorithm.
VARIABLE outgoingEdges

\* The set of transactions that are concurrent with a given transaction.
VARIABLE concurrentTxns


vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, incomingEdges, outgoingEdges, concurrentTxns>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant == 
    \* /\ txnHistory \in Seq(AnyOpType) seems expensive to check with TLC, so disable it.
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                 startTime  : Nat, 
                                 commitTime : Nat \cup {Empty}]
    /\ incomingEdges \in [txnIds -> SUBSET (txnIds \X {"WW", "WR", "RW"})] \* Map from transaction id to set of (incoming transaction, edge type) pairs.
    /\ outgoingEdges \in [txnIds -> SUBSET (txnIds \X {"WW", "WR", "RW"})] \* Map from transaction id to set of (outgoing transaction, edge type) pairs.
    /\ concurrentTxns \in [txnIds -> SUBSET txnIds] \* Map from transaction id to set of concurrent transaction ids. Set at begin time.

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]
    /\ incomingEdges = [id \in txnIds |-> {}] \* Initially no incoming edges.
    /\ outgoingEdges = [id \in txnIds |-> {}] \* Initially no outgoing edges.
    /\ concurrentTxns = [id \in txnIds |-> {}] \* Initially no concurrent transactions.

(**************************************************************************************************)
(* Helpers for querying transaction histories.                                                    *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* The set of all read or write ops done by a given transaction.                   
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* The set of all keys read or written to by a given transaction.                   
KeysReadByTxn(h, txnId)    == { op.key : op \in ReadsByTxn(txnHistory, txnId)}
KeysWrittenByTxn(h, txnId) == { op.key : op \in WritesByTxn(txnHistory, txnId)}

\* The index of a given operation in the transaction history sequence.
IndexOfOp(h, op) == CHOOSE i \in DOMAIN h : h[i] = op

RunningTxnIds == {txn.id : txn \in runningTxns}

\* Checks if two transactions are concurrent (their lifetimes overlap).
\* Two transactions are concurrent if they were running at the same time.
\* Uses commit time if available, otherwise considers the transaction as still running.
AreConcurrent(h, t1Id, t2Id) ==
    /\ t1Id /= t2Id
    /\ \E t1BeginOp \in Range(h) : t1BeginOp.txnId = t1Id /\ t1BeginOp.type = "begin"
    /\ \E t2BeginOp \in Range(h) : t2BeginOp.txnId = t2Id /\ t2BeginOp.type = "begin"
    /\ LET t1Start == BeginOp(h, t1Id).time
           t2Start == BeginOp(h, t2Id).time
           \* Get commit time if transaction committed, otherwise use a very large number
           t1End == IF t1Id \in CommittedTxns(h) THEN CommitOp(h, t1Id).time ELSE 999999
           t2End == IF t2Id \in CommittedTxns(h) THEN CommitOp(h, t2Id).time ELSE 999999
       IN
       \* Check if intervals [t1Start, t1End] and [t2Start, t2End] overlap
       /\ t1Start <= t2End
       /\ t2Start <= t1End

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would not be literally      *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(**************************************************************************************************)
StartTxn(newTxnId) == 
    LET newTxn == 
        [ id |-> newTxnId, 
            startTime |-> clock+1, 
            commitTime |-> Empty] IN
    \* Must choose an unused transaction id. There must be no other operation
    \* in the history that already uses this id.
    /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
    \* Save a snapshot of current data store for this transaction, and
    \* and append its 'begin' event to the history.
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = dataStore]
    /\ LET beginOp == [ type  |-> "begin", 
                        txnId |-> newTxnId, 
                        time  |-> clock+1 ] IN
        txnHistory' = Append(txnHistory, beginOp)
    \* Add transaction to the set of active transactions.
    /\ runningTxns' = runningTxns \cup {newTxn}
    \* Tick the clock.
    /\ clock' = clock + 1
    \* Add to this transaction's set of concurrent transactions, all the running transactions.
    /\ concurrentTxns' = [concurrentTxns EXCEPT ![newTxnId] = RunningTxnIds]
    /\ UNCHANGED <<dataStore, incomingEdges, outgoingEdges>>
                                                  
(**************************************************************************************************)
(* When a transaction T0 is ready to commit, we check for the presence of "dangerous edge"        *)
(* sequences in the serialization graph. This follows our definition of snapshot isolation as the *)
(* exclusion of G-nonadjacent cycles (https://jepsen.io/consistency/phenomena/g-nonadjacent).     *)
(* This term refers to cycles in the serialization graph that have atleast one RW edge between    *)
(* transactions and where no two RW edges are adjacent to each other. The algorithm is as follows:*)
(*                                                                                                *)
(* We first divide the check into two parts:                                                      *)
(* (1) We check T0's incoming edge sets and then run the detection algorithm                      *)
(* (2) We check T0's outgoing edge sets and then run the detection algorithm                      *)
(*                                                                                                *)
(* In each part, we check if the RW edge has any adjacent RW edges. If not, then this function    *)
(* returns False indicating that T0 cannot commit. However, if we find at least one adjacent RW   *)
(* edge, then this function returns True, indicating that T0 can commit.                          *)
(*                                                                                                *)
(* When a transaction tries to commit, we perform RW and WW edge detection and update the         *)
(* incoming and outgoing edge sets accordingly.                                                   *)
(**************************************************************************************************)



(**************************************************************************************************)
(*                                                                                                *)
(* Verifying Serializability                                                                      *)
(*                                                                                                *)
(* ---------------------------------------                                                        *)
(*                                                                                                *)
(* For checking serializability of transaction histories we use the "Conflict Serializability"    *)
(* definition.  This is slightly different than what is known as "View Serializability", but is   *)
(* suitable for verification, since it is efficient to check, whereas checking view               *)
(* serializability of a transaction schedule is known to be NP-complete.                          *)
(*                                                                                                *)
(* The definition of conflict serializability permits a more limited set of transaction           *)
(* histories.  Intuitively, it can be viewed as checking whether a given schedule has the         *)
(* "potential" to produce a certain anomaly, even if the particular data values for a history     *)
(* make it serializable.  Formally, we can think of the set of conflict serializable histories as *)
(* a subset of all possible serializable histories.  Alternatively, we can say that, for a given  *)
(* history H ConflictSerializable(H) => ViewSerializable(H).  The converse, however, is not true. *)
(* A history may be view serializable but not conflict serializable.                              *)
(*                                                                                                *)
(* In order to check for conflict serializability, we construct a multi-version serialization     *)
(* graph (MVSG).  Details on MVSG can be found, among other places, in Cahill's thesis, Section   *)
(* 2.5.1.  To construct the MVSG, we put an edge from one committed transaction T1 to another     *)
(* committed transaction T2 in the following situations:                                          *)
(*                                                                                                *)
(*   (WW-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 produces a later version of x.                            *)
(*                                                                                                *)
(*   (WR-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 reads this (or a later) version of x.                     *)
(*                                                                                                *)
(*   (RW-Dependency)                                                                              *)
(*   T1 reads a version of x, and T2 produces a later version of x. This is                       *)
(*   the only case where T1 and T2 can run concurrently.                                          *)
(*                                                                                                *)
(**************************************************************************************************)

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule implies
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < CommitOp(h, t2Id).time

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in ReadsByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < BeginOp(h, t2Id).time   

\* T1 read a key that T2 then later wrote to. T1 must start before T2 commits, since this implies that T1 read  
\* a version of the key and T2 produced a later version of that ke, i.e. when it commits. T1, however, read 
\* an earlier version of that key, because it started before T2 committed.
RWDependency(h, t1Id, t2Id) == 
    \E op1 \in ReadsByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ BeginOp(h, t1Id).time < CommitOp(h, t2Id).time  \* T1 starts before T2 commits. This means that T1 read
        \* For simplicity, we also only consider anti-dependencies to occur between
        \* concurrent transactions. If I read a key and then some time later, a
        \* non-concurrent transaction writes to that key, we don't worry about such a RW edge, since the later 
        \* transaction won't be installing the "immediate successor" of that key's version.
        \* This is formally discussed in Remark 2.1 of "Making Snapshot Isolation Serializable" 
        \* (https://dsf.berkeley.edu/cs286/papers/ssi-tods2005.pdf)
        /\ BeginOp(h, t2Id).time < CommitOp(h, t1Id).time

\* Produces the serialization graph as defined above, for a given history. This graph is produced 
\* by defining the appropriate set comprehension, where the produced set contains all the edges of the graph.
SerializationGraph(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {tedge \in (committedTxnIds \X committedTxnIds):
        /\ tedge[1] /= tedge[2]
        /\ \/ WWDependency(history, tedge[1], tedge[2])
           \/ WRDependency(history, tedge[1], tedge[2])
           \/ RWDependency(history, tedge[1], tedge[2])}

\* Returns the serialization graph with edge types.
\* Output format: <<t1, t2, edgeType>>
SerializationGraphWithEdgeTypes(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2, edgeType>> \in (committedTxnIds \X committedTxnIds \X {"WW", "WR", "RW"}):
        /\ t1 /= t2
        /\ \/ (edgeType = "WW" /\ WWDependency(history, t1, t2))
           \/ (edgeType = "WR" /\ WRDependency(history, t1, t2))
           \/ (edgeType = "RW" /\ RWDependency(history, t1, t2))}


\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommitWWConflict(txnId) ==
    \E txn \in runningTxns : 
        /\ txn.id = txnId
        /\ ~\E op \in Range(txnHistory) :
            /\ op.type = "commit" 
            \* Did another transaction start after me.
            /\ txn.id = txnId /\ op.time > txn.startTime 
            /\ KeysWrittenByTxn(txnHistory, txnId) \cap op.updatedKeys /= {} \* Must be no conflicting keys.


\* Load locally:
\* http://127.0.0.1:8000/#!/home?specpath=%2Flocal_dir%2FSnapshotIsolation.tla&initPred=Init&nextPred=Next&constants%5BtxnIds%5D=%7Bt1%2Ct2%2Ct3%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=Empty

\* 
\* T1 -> T2 - RW - > T3 -> T4
\* 
\* Check A (T2 commits last)
\* 
\* Need to check if this transaction (would be T2) has an outgoing RW edge to T3 but no incoming RW edges,
\* and that T3 has no outgoing RW edges.
\* 

IncomingEdgeTypes(incoming, txnId) == {edgeType \in {"WW", "WR", "RW"} : \E <<inTxnId, e>> \in incoming[txnId] : e = edgeType}


\* Incoming edges for a transaction based on direct inspection of the global transaction history.
IncomingEdgesGlobal(txnId, hist) == 
    {<<t1, t2, edgeType>> \in SerializationGraphWithEdgeTypes(hist) : t2 = txnId}
    
OutgoingEdgesGlobal(txnId, hist) == 
    {<<t1, t2, edgeType>> \in SerializationGraphWithEdgeTypes(hist) : t1 = txnId}

TxnMustAbort(txnId, incoming, outgoing, hist) ==
    \* If txnId has no incoming RW edges, and an outgoing hazardous RW edge, we must abort.
    /\ \E <<t, outTxnId, edgeType>> \in OutgoingEdgesGlobal(txnId, hist) : 
        /\ edgeType = "RW"
        \* /\ CommitOp(txnHistory, txnId).time > CommitOp(txnHistory, outTxnId).time
        \* Is hazardous RW edge.
        /\ \E op \in Range(hist) : op.txnId = outTxnId /\ op.type = "commit"

    \* Note that any edge between transactions can be a "multi-edge" i.e. there may be multiple
    \* edges of different dependency types between two transactions. If this is the case, then
    \* we must abort specifically if there exists an incoming edge that is strictly a non-RW edge.
    \* For example, if we there is an incoming edge that is a multi-edge of {WW, RW}, then 
    \* we can allow this, since any cycle formed via this edge will not be G-nonadjacent. If,
    \* however, there exists some incoming edge that is strictly RW, and a different incoming edge
    \* that is strictly non-RW, then we must abort.

    \* (a) there exists an incoming edge that is strictly non-RW.
    /\ \E <<inTxnId, t, edgeType>> \in IncomingEdgesGlobal(txnId, hist) : 
        /\ edgeType \in {"WW", "WR"}
        /\ \A <<ti,tj,etype>> \in IncomingEdgesGlobal(txnId, hist) : ti = inTxnId => etype \in {"WW", "WR"}



    \* There is not a distinct incoming edge the is RW.
    \* /\ ~\E <<inTxnId, edgeType>> \in incoming[txnId] : 
        \* /\ edgeType = "RW"


    \* /\ \E <<outTxnId, edgeType>> \in outgoing[txnId] : 
        \* /\ edgeType = "RW"
        \* /\ ~\E <<nextOutTxnId, nextEdgeType>> \in outgoing[outTxnId] : nextEdgeType = "RW"

\* Checks whether a given transaction is allowed to commit based on RW edge cycle prevention
TxnCanCommit(txnId, incoming, outgoing) ==
    \/ incoming[txnId] = {}  \* If incoming edge set is empty, return True
    \/ ~(\E <<inTxnId, edgeType>> \in incoming[txnId] : edgeType = "RW")  \* If no RW edges in incoming, return True
    \/ \E <<inTxnId, edgeType>> \in incoming[txnId] : 
        /\ edgeType = "RW"
        /\ (\/ (/\ incoming[inTxnId] /= {} 
               /\ \E <<src, et>> \in incoming[inTxnId] : et = "RW")
            \/ (/\ outgoing[txnId] /= {} 
               /\ \E <<dst, et>> \in outgoing[txnId] : et = "RW"))

    \/ outgoing[txnId] = {}  \* If outgoing edge set is empty, return True
    \/ ~(\E <<outTxnId, edgeType>> \in outgoing[txnId] : edgeType = "RW")  \* If no RW edges in outgoing, return True
    \/ \E <<outTxnId, edgeType>> \in outgoing[txnId] : 
        /\ edgeType = "RW"
        /\ (\/ (/\ incoming[outTxnId] /= {} 
               /\ \E <<src, et>> \in incoming[outTxnId] : et = "RW")
            \/ (/\ outgoing[outTxnId] /= {} 
               /\ \E <<dst, et>> \in outgoing[outTxnId] : et = "RW"))
    
        
CommitTxn(txnId) == 
    \* Transaction must be able to commit i.e. have no "dangerous edge" sequences
    \* in the serialization graph.
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}  
    \* RW EDGE DETECTION
    \* Update concurrent transactions to include:
    \* 1. Current concurrent transactions set
    \* 2. Currently running transactions (except self)
    \* 3. Committed transactions that started after this transaction started
    \* 4. Aborted transactions dont matter since they are essentially invisible to the current transaction.
    /\ LET myStartTime == BeginOp(txnHistory, txnId).time
           committedAfterMyStart == {tid \in CommittedTxns(txnHistory) : 
                                      BeginOp(txnHistory, tid).time > myStartTime}
           updatedConcurrentSet == concurrentTxns[txnId] 
                                  \cup (RunningTxnIds \ {txnId}) 
                                  \cup committedAfterMyStart
           keysReadByMe == KeysReadByTxn(txnHistory, txnId)
           \* Find concurrent transactions that wrote to keys that txnId read
           \* Of those, only consider the ones that have already committed since those are the only ones txnId can form RW edges with.
        \*    exclusiveCommitSet == updatedConcurrentSet \cap CommittedTxns(txnHistory)
           rwTargets == {otherTxn \in updatedConcurrentSet : 
                           KeysWrittenByTxn(txnHistory, otherTxn) \cap keysReadByMe /= {}}
           \* Create new RW edges
           newOutgoingRW == {<<target, "RW">> : target \in rwTargets}
           \* Update outgoing edges for this transaction
           updatedOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingRW]
           \* Update incoming edges for the target transactions
           updatedIncoming == [tid \in txnIds |->
                                IF tid \in rwTargets
                                THEN incomingEdges[tid] \cup {<<txnId, "RW">>}
                                ELSE incomingEdges[tid]]
           \* Update the global concurrent transactions mapping
           updatedConcurrentTxns == [concurrentTxns EXCEPT ![txnId] = updatedConcurrentSet]
           
           \* WW EDGE DETECTION
           \* Find concurrent transactions that wrote to keys that txnId also wrote to
           keysWrittenByMe == KeysWrittenByTxn(txnHistory, txnId)
           wwTargets == {otherTxn \in updatedConcurrentSet : 
                           KeysWrittenByTxn(txnHistory, otherTxn) \cap keysWrittenByMe /= {}}
           \* Create new WW edges
           newOutgoingWW == {<<target, "WW">> : target \in wwTargets}
           \* Update outgoing edges for this transaction (combining RW and WW edges)
           finalOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingRW \cup newOutgoingWW]
           \* Update incoming edges for the target transactions (combining RW and WW targets)
           \* TODO: These updating of incoming edge types may need to be amended. For initial prototype, we can directly
           \* check global transaction history for in/out dep edges.
           finalIncoming == [tid \in txnIds |->
                                IF tid \in rwTargets
                                THEN (IF tid \in wwTargets 
                                      THEN incomingEdges[tid] \cup {<<txnId, "RW">>, <<txnId, "WW">>}
                                      ELSE incomingEdges[tid] \cup {<<txnId, "RW">>})
                                ELSE (IF tid \in wwTargets
                                      THEN incomingEdges[tid] \cup {<<txnId, "WW">>}
                                      ELSE incomingEdges[tid])]
       IN
       /\ outgoingEdges' = finalOutgoing
       /\ incomingEdges' = finalIncoming
       /\ concurrentTxns' = updatedConcurrentTxns

    \* We can leave the snapshot around, since it won't be used again.
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txnId, 
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txnId)] IN
       txnHistory' = Append(txnHistory, commitOp)       

    \* 
    \* Check if the transaction can commit.
    \*

    \* /\ TxnCanCommit(txnId, incomingEdges', outgoingEdges')
    \* /\ TxnCanCommitWWConflict(txnId)
    /\ ~TxnMustAbort(txnId, incomingEdges', outgoingEdges', txnHistory')
     
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txnId) 
                                        THEN txnSnapshots[txnId][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set. 
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1

    /\ UNCHANGED <<txnSnapshots>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to dangerous edge      *)
(* sequences in the serialization graph.                                                          *)
(**************************************************************************************************)
AbortTxn(txnId) ==
    \* If a transaction can't commit due to dangerous edge sequences, then it
    \* must abort.
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}
    /\ ~TxnCanCommit(txnId, incomingEdges, outgoingEdges)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txnId, 
                        time   |-> clock + 1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = {r \in runningTxns : r.id # txnId} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots, incomingEdges, outgoingEdges, concurrentTxns>>

(***************************************************************************************************)
(* Read and write operations executed by transactions.                                            *)
(*                                                                                                *)
(* As a simplification, and to limit the size of potential models, we allow transactions to only  *)
(* read or write to the same key once.  The idea is that it limits the state space without loss   *)
(* of generality.                                                                                 *)
(**************************************************************************************************)

TxnRead(txnId, k) == 
    \* Read from this transaction's snapshot.
    \* Update the transaction's incoming and outgoing edges based on RW edge detection.
    /\ txnId \in RunningTxnIds
    /\ LET valRead == txnSnapshots[txnId][k]
           readOp == [ type  |-> "read", 
                       txnId |-> txnId, 
                       key   |-> k, 
                       val   |-> valRead]
           \* WR EDGE DETECTION
           \* Update the transactions's concurrent transactions set.
           myStartTime == BeginOp(txnHistory, txnId).time
           committedAfterMyStart == {tid \in CommittedTxns(txnHistory) : 
                                     BeginOp(txnHistory, tid).time > myStartTime}
           updatedConcurrentSet == concurrentTxns[txnId] 
                                  \cup (RunningTxnIds \ {txnId}) 
                                  \cup committedAfterMyStart
           keysReadByMe == KeysReadByTxn(txnHistory, txnId)
           \* Find transactions that wrote to the keys that this transaction read. From the set of transactions that committed before this transaction started.
           exclusiveCommitSet == {tid \in CommittedTxns(txnHistory) :
                                  CommitOp(txnHistory, tid).time < myStartTime}
           rwTargets == {otherTxn \in exclusiveCommitSet : 
                         KeysWrittenByTxn(txnHistory, otherTxn) \cap keysReadByMe /= {}}
           \* Create new WR edges
           newOutgoingWR == {<<target, "WR">> : target \in rwTargets}
           \* Update outgoing edges for this transaction
           updatedOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingWR]
           \* Update incoming edges for the target transactions
           updatedIncoming == [tid \in txnIds |->
                               IF tid \in rwTargets
                               THEN incomingEdges[tid] \cup {<<txnId, "WR">>}
                               ELSE incomingEdges[tid]]
           \* Update the global concurrent transactions mapping
           updatedConcurrentTxns == [concurrentTxns EXCEPT ![txnId] = updatedConcurrentSet]
       IN
       /\ k \notin KeysReadByTxn(txnHistory, txnId)   
       /\ txnHistory' = Append(txnHistory, readOp)
       /\ outgoingEdges' = updatedOutgoing
       /\ incomingEdges' = updatedIncoming
       /\ concurrentTxns' = updatedConcurrentTxns
       /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txnId, k, v) == 
    /\ txnId \in RunningTxnIds
    /\ LET writeOp == [ type  |-> "write", 
                        txnId |-> txnId, 
                        key   |-> k, 
                        val   |-> v] IN  
        /\ k \notin KeysWrittenByTxn(txnHistory, txnId)
        \* We update the transaction's snapshot, not the actual data store.
        /\ LET updatedSnapshot == [txnSnapshots[txnId] EXCEPT ![k] = v] IN
            txnSnapshots' = [txnSnapshots EXCEPT ![txnId] = updatedSnapshot]
        /\ txnHistory' = Append(txnHistory, writeOp)
        /\ UNCHANGED <<dataStore, runningTxns, clock, concurrentTxns, incomingEdges, outgoingEdges>>

(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it is desirable to have TLC check for deadlock, which may indicate bugs in the spec or   *)
(* in the algorithm, we want to explicitly define what a "valid" termination state is.  If all    *)
(* transactions have run and either committed or aborted, we consider that valid termination, and *)
(* is allowed as an infinite suttering step.                                                      *)
(**************************************************************************************************)           

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds
    
Next == 
    \/ \E tid \in txnIds : StartTxn(tid)
    \* Ends a given transaction by either committing or aborting it. To exclude uninteresting 
    \* histories, we require that a transaction does at least one operation before committing or aborting. 
    \* Assumes that the given transaction is currently running.
    \/ \E tid \in txnIds : CommitTxn(tid)
    \/ \E tid \in txnIds : AbortTxn(tid)
    \* Transaction reads or writes a key. We limit transactions
    \* to only read or write the same key once.
    \/ \E tid \in txnIds, k \in keys : TxnRead(tid, k)
    \/ \E tid \in txnIds, k \in keys, v \in values : TxnUpdate(tid, k, v)
    \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


----------------------------------------------------------------------------------------------------


(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties and Tests                                                               *)
(*                                                                                                *)
(**************************************************************************************************)



(**************************************************************************************************)
(* Operator for computing cycles in a given graph, defined by a set of edges.                     *)
(*                                                                                                *)
(* Returns a set containing all elements that participate in any cycle (i.e.  union of all        *)
(* cycles), or an empty set if no cycle is found.                                                 *)
(*                                                                                                *)
(* Source:                                                                                        *)
(* https://github.com/pron/amazon-snapshot-spec/blob/master/serializableSnapshotIsolation.tla.    *)
(**************************************************************************************************)
FindAllNodesInAnyCycle(edges) ==

    LET RECURSIVE findCycleNodes(_, _)   (* startNode, visitedSet *)
        (* Returns a set containing all elements of some cycle starting at startNode,
           or an empty set if no cycle is found. 
         *)
        findCycleNodes(node, visitedSet) ==
            IF node \in visitedSet THEN
                {node}  (* found a cycle, which includes node *)
            ELSE
                LET newVisited == visitedSet \union {node}
                    neighbors == {to : <<from, to>> \in 
                                           {<<from, to>> \in edges : from = node}}
                IN  (* Explore neighbors *)
                    UNION {findCycleNodes(neighbor, newVisited) : neighbor \in neighbors}
                    
        startPoints == {from : <<from, to>> \in edges}  (* All nodes with an outgoing edge *)
    IN 
        UNION {findCycleNodes(node, {}) : node \in startPoints}
       
IsCycle(edges) == FindAllNodesInAnyCycle(edges) /= {}



\* The key property to verify i.e. serializability of transaction histories.
IsConflictSerializable(h) == ~IsCycle(SerializationGraph(h))


BSeq(S, b) == {<<>>} \cup UNION {[1..n -> S] : n \in 1..b}

\* Record path as a sequence of edges.
Path(V, E) == {p \in BSeq(E, Cardinality(V)) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : p[i][2] = p[i+1][1]}

Cycles(V, E) == 
    LET cyclePaths == {p \in Path(V, E) : Len(p) > 1 /\ p[1][1] = p[Len(p)][2]} IN
    {Range(p) : p \in cyclePaths}
        
    \* LET cyclePaths == {p \in Path(V, E) : Len(p) > 1 /\ p[1][1] = p[Len(p)][2]} IN
    \* {{<<cpath[i],cpath[i+1]>> : i \in 1..(Len(cpath)-1)} : cpath \in cyclePaths}

AllCycles == Cycles(txnIds, SerializationGraphWithEdgeTypes(txnHistory))

\* Given a set of edges which form a cycle, check whether this is a G-nonadjacent cycle.
IsGnonadjacentCycle(cycleEdges) == 
    \A e1,e2 \in cycleEdges : 
        \* Adjacent edges cannot both be RW.
        (e1[2] = e2[1]) => ~(e1[3] = "RW" /\ e2[3] = "RW")

\* 
\* We define a RW edge <<t1,t2>> as "hazardous" if the commit order between t1
\* and t2 is opposite the direction of the RW edge. 
\* 
\* We refer to the inverse case as a "benign" RW edge.
\* 
HazardousRWEdge(e) == e[3] = "RW" /\ CommitOp(txnHistory, e[1]).time > CommitOp(txnHistory, e[2]).time
BenignRWEdge(e) == e[3] = "RW" /\ CommitOp(txnHistory, e[1]).time < CommitOp(txnHistory, e[2]).time

\* States that no G-nonadjacent cycles are possible.
NoGnonadjacent == \A c \in AllCycles : ~IsGnonadjacentCycle(c)

\* 
\* Seems like we may actually want to state a slightly more accurate property which is something like,
\* check that there are no cases where we have *only* G-nonadjacent cycles i.e. where those cycles
\* are not also accompanied by some G-adjacent cycles (e.g. general G2 cycles). If we have an appearance
\* of a G-nonjadjacent cycle only when also in presence of a G-adjacent cycle, then we may actually
\* consider that to be acceptable.
\* 
\* e.g. this accounts for cases when we have something like both a WW and RW edge between two transactions,
\* in a way that could form both a G-adjacent and G-nonadjacent cycle.
\* 
NoGnonadjacentGeneral == 
    (\E c \in AllCycles : IsGnonadjacentCycle(c)) => 
        \E c2 \in AllCycles : ~IsGnonadjacentCycle(c2)

\* States that all G-nonadjacent cycles contain at least one "hazardous" RW edge.
AllGnonadjacentContainHazardousRWEdge == 
    \A c \in AllCycles : IsGnonadjacentCycle(c) => (\E e \in c : HazardousRWEdge(e))




LargerGnonadjacentWitness == \A c \in AllCycles : ~(
    /\ IsGnonadjacentCycle(c) 
    /\ Cardinality(c) = 4
    /\ Cardinality({e[1] : e \in c }) = 4
    \* /\ Cardinality(AllCycles) = 1
)

Test == 
\*     /\ TRUE
\*     \* /\ PrintT(AllCycleNodes)
\*     \* /\ PrintT(Path(txnIds, SerializationGraph(txnHistory)))
    /\ PrintT(AllCycles)
\*     /\ PrintT({IsGnonadjacentCycle(c) : c \in Cycles(txnIds, SerializationGraph(txnHistory))})




\* Examples of each dependency type.
HistWW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "write"  , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {"k1"}]>>

HistWR == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "read"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {}]>>

HistRW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "read"   , txnId |-> 0 , key  |-> "k1" , val |-> "empty"],
             [type |-> "begin"  , txnId |-> 1 , time |-> 1],
             [type |-> "write"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 2, updatedKeys |-> {}],
             [type |-> "commit" , txnId |-> 0 , time |-> 3, updatedKeys |-> {"k1"}]>>

\* A simple invariant to test the correctness of dependency definitions.
WWDependencyCorrect == WWDependency(HistWW, 0, 1)
WRDependencyCorrect == WRDependency(HistWR, 0, 1)
RWDependencyCorrect == RWDependency(HistRW, 0, 1)
MVSGDependencyCorrect == WWDependencyCorrect /\ WRDependencyCorrect /\ RWDependencyCorrect
   
     
(**************************************************************************************************)
(* Examples of concurrency phenomena under Snapshot Isolation.  These are for demonstration       *)
(* purposes and can be used for checking the above definitions of serializability.                *)
(*                                                                                                *)
(* Write Skew:                                                                                    *)
(*                                                                                                *)
(* Example history from Michael Cahill's Phd thesis:                                              *)
(*                                                                                                *)
(* Section 2.5.1, pg.  16                                                                         *)
(* https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf           *)
(*                                                                                                *)
(* H: r1(x=50) r1(y=50) r2(x=50) r2(y=50) w1(x=-20) w2(y=-30) c1 c2                               *)
(*                                                                                                *)
(*                                                                                                *)
(* Read-Only Anomaly:                                                                             *)
(*                                                                                                *)
(* "A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete, O'Neil, O'Neil             *)
(* https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                      *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

WriteSkewAnomalyTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1],                       
    [type |-> "begin",  txnId |-> 2, time |-> 2],
    [type |-> "read",   txnId |-> 1, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 1, key |-> "Y", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "Y", val |-> "Empty"],                    
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> 30],           
    [type |-> "write",  txnId |-> 2, key |-> "Y", val |-> 20],        
    [type |-> "commit", txnId |-> 1, time |-> 3, updatedKeys |-> {"X"}],
    [type |-> "commit", txnId |-> 2, time |-> 4, updatedKeys |-> {"Y"}]>>

ReadOnlyAnomalyTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_X", val |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_Y", val |-> 0], 
    [type |-> "commit", txnId |-> 0, time |-> 1, updatedKeys |-> {"K_X", "K_Y"}],
    
    (* the history from the paper *) 
                     [type |-> "begin",  txnId |-> 2, time |-> 2], 
    (* R2(X0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_X", ver |-> "T_0"], 
    (* R2(Y0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_Y", ver |-> "T_0"],
                      
                     [type |-> "begin",  txnId |-> 1, time |-> 3], 
    (* R1(Y0,0)   *) [type |-> "read",   txnId |-> 1, key |-> "K_Y"], 
    (* W1(Y1,20)  *) [type |-> "write",  txnId |-> 1, key |-> "K_Y", val |-> 20],
    (* C1         *) [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {"K_Y"}],
     
                     [type |-> "begin",  txnId |-> 3, time |-> 5], 
    (* R3(X0,0)   *) [type |-> "read",   txnId |-> 3, key |-> "K_X", ver |-> "T_0"], 
    (* R3(Y1,20)  *) [type |-> "read",   txnId |-> 3, key |-> "K_Y", ver |-> "T_1"], 
    (* C3         *) [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}],
                      
    (* W2(X2,-11) *) [type |-> "write",  txnId |-> 2, key |-> "K_X", val |-> (0 - 11)], 
    (* C2         *) [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {"K_X"}]
    >>

(**************************************************************************************************)
(* Checks if a given history contains a "read-only" anomaly.  In other words, is this a           *)
(* non-serializable transaction history such that it contains a read-only transaction T, and      *)
(* removing T from the history makes the history serializable.                                    *)
(**************************************************************************************************)

ReadOnlyAnomaly(h) == 
    /\ ~IsConflictSerializable(h)
    /\ \E txnId \in CommittedTxns(h) :
        \* Transaction only did reads.
        /\ WritesByTxn(h, txnId) = {}
        \* Removing the transaction makes the history serializable
        /\ LET txnOpsFilter(t) == (t.txnId # txnId)
           hWithoutTxn == SelectSeq(h, txnOpsFilter) IN
           IsConflictSerializable(hWithoutTxn)

\* Invariant definitions.
IsConflictSerializableInv == IsConflictSerializable(txnHistory)
NoReadOnlyAnomaly == ~ReadOnlyAnomaly(txnHistory)


(**************************************************************************************************)
(* View Serializability (Experimental).                                                           *)
(*                                                                                                *)
(* A transaction history is view serializable if the reads and writes of all transaction          *)
(* oeprations are equivalent the reads and writes of some serial schedule.  View serializability  *)
(* encodes a more intuitive notion of serializability i.e.  the overall effect of a sequence of   *)
(* interleaved transactions is the same as if it they were executed in sequential order.          *)
(**************************************************************************************************)

Maximum(S) == CHOOSE x \in S : \A y \in S : y <= x

\* The set of all permutations of elements of a set S whose length are the cardinality of S.
SeqPermutations(S) == LET D == 1..Cardinality(S) IN {f \in [D -> S] : \A w \in S : \E v \in D : f[v]=w}

\* Flattens a sequence of sequences.
RECURSIVE Flatten(_)
Flatten(seq) == IF Len(seq) = 0 THEN <<>> ELSE Head(seq) \o Flatten(Tail(seq))

\* The subsequence of all operations executed by a given transaction id in a history. The original ordering 
\* of the operations is maintained.
OpsForTxn(h, txnId) == SelectSeq(h, LAMBDA t : t.txnId = txnId)
SerialHistories(h) == 
    LET serialOrderings == SeqPermutations({ OpsForTxn(h, tid) : tid \in CommittedTxns(h) }) IN
    {Flatten(o) : o \in serialOrderings}

\* We "execute" a given serial history. To do this, we really only need to determine what the new values of the 
\* 'read' operations are, since writes are not changed. To do this, we simply replace the value of each read operation
\* in the history with the appropriate one.
ExecuteSerialHistory(h) ==
    [i \in DOMAIN h |-> 
        IF h[i].type = "read" 
            \* We need to determine what value to read for this operation; we use the
            \* the value of the last write to this key.
            THEN LET prevWriteOpInds == {ind \in DOMAIN h : 
                                                /\  ind < i 
                                                /\  h[ind].type = "write"
                                                /\  h[ind].key = h[i].key} IN
                     IF prevWriteOpInds = {} 
                        THEN [h[i] EXCEPT !.val = Empty]
                        ELSE LET latestWriteOpToKey == h[Maximum(prevWriteOpInds)] IN
                             [h[i] EXCEPT !.val = latestWriteOpToKey.val] 
            ELSE h[i]]

IsViewEquivalent(h1, h2) == 
    \A tid \in CommittedTxns(h1) : OpsForTxn(h1, tid) = OpsForTxn(h2, tid)

ViewEquivalentHistory(h) == {ExecuteSerialHistory(serial) : serial \in 
                                {h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))}}

IsViewSerializable(h) == \E h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))


(**************************************************************************************************)
(* Experiments for G-Single and G-Nonadjacent Anomaly Cycle detection                             *)
(**************************************************************************************************)

GSingle3NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2],
    [type |-> "begin",  txnId |-> 2, time |-> 3],

    \* T2 reads k1 early (for T0→RW T2)
    [type |-> "read",   txnId |-> 2, key |-> "k1", val |-> "Empty"],

    \* T0 writes k1 and k2, commits first
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    [type |-> "write",  txnId |-> 0, key |-> "k2", val |-> "v1"],
    [type |-> "commit", txnId |-> 0, time |-> 4, updatedKeys |-> {"k1", "k2"}],

    \* T1 writes k2 after T0 (creates T0→WW T1) and k3
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v2"],
    [type |-> "write",  txnId |-> 1, key |-> "k3", val |-> "v1"],
    [type |-> "commit", txnId |-> 1, time |-> 5, updatedKeys |-> {"k2", "k3"}],

    \* T2 writes k3 after T1 (creates T1→WW T2) - k1 write creates T2→RW T0
    [type |-> "write",  txnId |-> 2, key |-> "k3", val |-> "v2"],
    [type |-> "commit", txnId |-> 2, time |-> 6, updatedKeys |-> {"k3"}]
>>


GSingle4NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2], 
    [type |-> "begin",  txnId |-> 2, time |-> 3],
    
    \* T2 reads k1 early (for T2→RW T0)
    [type |-> "read",   txnId |-> 2, key |-> "k1", val |-> "Empty"],
    
    \* T0 writes k2 and k1, commits once
    [type |-> "write",  txnId |-> 0, key |-> "k2", val |-> "v1"],
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    [type |-> "commit", txnId |-> 0, time |-> 4, updatedKeys |-> {"k2", "k1"}],
    
    \* T3 begins AFTER T0 commits (for T0→WR T3)
    [type |-> "begin",  txnId |-> 3, time |-> 5],
    [type |-> "read",   txnId |-> 3, key |-> "k2", val |-> "v1"],
    [type |-> "write",  txnId |-> 3, key |-> "k3", val |-> "v1"],
    [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {"k3"}],
    
    \* T1 writes k3 after T3 commits (creates T3→WW T1)
    [type |-> "write",  txnId |-> 1, key |-> "k3", val |-> "v2"],
    [type |-> "write",  txnId |-> 1, key |-> "k4", val |-> "v1"],
    [type |-> "commit", txnId |-> 1, time |-> 7, updatedKeys |-> {"k3", "k4"}],
    
    \* T2 writes k4 after T1 commits (creates T1→WW T2)
    [type |-> "write",  txnId |-> 2, key |-> "k4", val |-> "v3"],
    [type |-> "commit", txnId |-> 2, time |-> 8, updatedKeys |-> {"k4"}]
>>


GNonadjacent4NodeTest == <<
    [type |-> "begin",  txnId |-> 3, time |-> 1], \* T3 begins
    [type |-> "read",   txnId |-> 3, key |-> "k1", val |-> "Empty"], \* T3 reads k1=0
    [type |-> "write",  txnId |-> 3, key |-> "k5", val |-> "v2"], \* T3 writes k5=v2
    [type |-> "begin",  txnId |-> 1, time |-> 2], \* T1 begins
    [type |-> "write",  txnId |-> 1, key |-> "k6", val |-> "v1"], \* T1 writes k6=v1
    [type |-> "begin",  txnId |-> 2, time |-> 3], \* T2 begins
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v1"], \* T2 writes k2=v1
    [type |-> "write",  txnId |-> 3, key |-> "k3", val |-> "v2"], \* T2 writes k3=v2
    [type |-> "read",   txnId |-> 3, key |-> "k4", val |-> "Empty"], \* T3 reads k4=0
    [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {}], \* T1 commits
    [type |-> "begin",  txnId |-> 0, time |-> 5], \* T0 begins
    [type |-> "read",   txnId |-> 0, key |-> "k6", val |-> "v1"], \* T0 reads k6=v1
    [type |-> "write",  txnId |-> 2, key |-> "k5", val |-> "v1"], \* T2 writes k5=v1
    [type |-> "read",   txnId |-> 2, key |-> "k6", val |-> "Empty"], \* T2 reads k6=Empty
    [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}], \* T2 commits
    [type |-> "read", txnId |-> 0, key |-> "k3", val |-> "Empty"], \* T0 reads k3=Empty
    [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {}], \* T0 commits
    [type |-> "commit", txnId |-> 0, time |-> 8, updatedKeys |-> {}] \* T0 commits
>>


GNonadjacent4NodeWithoutWWTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1], \* T1 begins
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> "$50"], \* T1 writes (X, $50)
    [type |-> "write",  txnId |-> 1, key |-> "Y", val |-> "$50"], \* T1 writes (Y, $50) 
    [type |-> "write",  txnId |-> 1, key |-> "M", val |-> "Open"], \* T1 writes (M, "Open")
    [type |-> "commit", txnId |-> 1, time |-> 2, updatedKeys |-> {"X", "Y", "M"}], \* T1 commits
    [type |-> "begin",  txnId |-> 4, time |-> 3], \* T4 begins
    [type |-> "read",   txnId |-> 4, key |-> "M", val |-> "Open"], \* T4 reads M → gets "Open"
    [type |-> "begin",  txnId |-> 5, time |-> 4], \* T5 begins
    [type |-> "read",   txnId |-> 5, key |-> "M", val |-> "Open"], \* T5 reads M → gets "Open"
    [type |-> "begin",  txnId |-> 2, time |-> 5], \* Ta begins (renaming T2 to Ta for clarity)
    [type |-> "write",  txnId |-> 4, key |-> "X", val |-> "$70"], \* T4 writes (X, $70)
    [type |-> "commit", txnId |-> 4, time |-> 6, updatedKeys |-> {"X"}], \* T4 commits
    [type |-> "read",   txnId |-> 2, key |-> "X", val |-> "$70"], \* Ta reads X → gets $70 (sees T4's committed update)
    [type |-> "begin",  txnId |-> 3, time |-> 7], \* Tb begins (using txnId 3 for Tb)
    [type |-> "write",  txnId |-> 5, key |-> "Y", val |-> "$75"], \* T5 writes (Y, $75)
    [type |-> "read",   txnId |-> 2, key |-> "Y", val |-> "$50"], \* Ta reads Y → gets $50 (misses T5's update - T5 hasn't committed yet)
    [type |-> "commit", txnId |-> 2, time |-> 8, updatedKeys |-> {}], \* Ta commits
    [type |-> "commit", txnId |-> 5, time |-> 9, updatedKeys |-> {"Y"}], \* T5 commits
    [type |-> "read",   txnId |-> 3, key |-> "Y", val |-> "$75"], \* Tb reads Y → gets $75 (sees T5's committed update)
    [type |-> "read",   txnId |-> 3, key |-> "X", val |-> "$50"], \* Tb reads X → gets $50 (misses T4's update due to snapshot choice)
    [type |-> "commit", txnId |-> 3, time |-> 10, updatedKeys |-> {}] \* Tb commits
>>


G6NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2],
    [type |-> "begin",  txnId |-> 2, time |-> 3],
    [type |-> "begin",  txnId |-> 3, time |-> 4],
    [type |-> "begin",  txnId |-> 4, time |-> 5],
    [type |-> "begin",  txnId |-> 5, time |-> 6],

    \* T0 writes k1 (for T0→WR T1)
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    
    \* T1 reads k1 from T0 (creates T0→WR T1)
    [type |-> "read",   txnId |-> 1, key |-> "k1", val |-> "v1"],
    
    \* T2 reads k2 early (for T1→RW T2)
    [type |-> "read",   txnId |-> 2, key |-> "k2", val |-> "Empty"],
    
    \* T1 writes k2 after T2 read (creates T1→RW T2)
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v1"],
    
    \* T2 writes k3 (for T2→WR T3, since WW doesn't create edges)
    [type |-> "write",  txnId |-> 2, key |-> "k3", val |-> "v1"],
    
    \* T3 reads k3 from T2 (creates T2→WR T3)
    [type |-> "read",   txnId |-> 3, key |-> "k3", val |-> "v1"],
    
    \* T3 writes k4 (for T3→WR T4)
    [type |-> "write",  txnId |-> 3, key |-> "k4", val |-> "v1"],
    
    \* T4 reads k4 from T3 (creates T3→WR T4)
    [type |-> "read",   txnId |-> 4, key |-> "k4", val |-> "v1"],
    
    \* T5 reads k5 early (for T4→RW T5)
    [type |-> "read",   txnId |-> 5, key |-> "k5", val |-> "Empty"],
    
    \* T4 writes k5 after T5 read (creates T4→RW T5)
    [type |-> "write",  txnId |-> 4, key |-> "k5", val |-> "v1"],
    
    \* T5 writes k6 (for T5→WR T0, to close the cycle)
    [type |-> "write",  txnId |-> 5, key |-> "k6", val |-> "v1"],
    
    \* T0 reads k6 from T5 (creates T5→WR T0, completing the cycle)
    [type |-> "read",   txnId |-> 0, key |-> "k6", val |-> "v1"],
    
    \* Commits in order
    [type |-> "commit", txnId |-> 0, time |-> 7, updatedKeys |-> {"k1"}],
    [type |-> "commit", txnId |-> 1, time |-> 8, updatedKeys |-> {"k2"}],
    [type |-> "commit", txnId |-> 2, time |-> 9, updatedKeys |-> {"k3"}],
    [type |-> "commit", txnId |-> 3, time |-> 10, updatedKeys |-> {"k4"}],
    [type |-> "commit", txnId |-> 4, time |-> 11, updatedKeys |-> {"k5"}],
    [type |-> "commit", txnId |-> 5, time |-> 12, updatedKeys |-> {"k6"}]
>>

(**************************************************************************************************)
(* G-Single and G-Nonadjacent Anomaly (Experimental).                                             *)
(*                                                                                                *)
(* G-Single anomaly is where there is a dependency cycle of any length that contains exactly      *)
(* one RW edge. This is a specific type of non-serializable schedule that can occur under         *)
(* snapshot isolation.                                                                            *)
(**************************************************************************************************)

\* Returns the serialization graph with edge types and concurrency information.
\* Output format: <<t1, t2, edgeType, concurrent_or_not>>
SerializationGraphWithCC(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2, edgeType, cclabel, rwlabel>> \in (committedTxnIds \X committedTxnIds \X {"WW", "WR", "RW"} \X {"concurrent", "not_concurrent"} \X {"benign", "hazardous"}):
        /\ t1 /= t2
        /\ \/ (edgeType = "WW" /\ WWDependency(history, t1, t2))
           \/ (edgeType = "WR" /\ WRDependency(history, t1, t2))
           \/ (edgeType = "RW" /\ RWDependency(history, t1, t2))
        /\ cclabel = IF AreConcurrent(history, t1, t2) THEN "concurrent" ELSE "not_concurrent"
        /\ rwlabel = IF HazardousRWEdge(<<t1, t2, "RW">>) THEN "hazardous" ELSE "benign"}


\* Write Skew Anomaly
WriteSkewAnomaly == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) = 2
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 2
      /\ \E a,b \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b}) = 2
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<b, a, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

Invariant == WriteSkewAnomaly

\* Find the cardinality of a given edge pair in the edge set
FindCardinality(edges, pair) ==
    Cardinality({e \in edges : <<e[1], e[2]>> = pair})

\* Cardinality check for the actual transaction history (txnHistory)
TxnHistoryCardinality(h) == 
    LET detailedEdges == SerializationGraphWithEdgeTypes(h)
        \* Extract just the node pairs (ignoring edge types) for cardinality checking
        edgePairs == {<<e[1], e[2]>> : e \in detailedEdges}
    IN [pair \in edgePairs |-> FindCardinality(detailedEdges, pair)]


\* For debugging within the model checker in VSCode
Alias == [
    txnHistory |-> txnHistory,
    ccgraph |-> SerializationGraphWithCC(txnHistory),
    incomingEdges |-> incomingEdges,
    outgoingEdges |-> outgoingEdges,
    canCommit |-> [txnId \in txnIds |-> TxnCanCommit(txnId, incomingEdges, outgoingEdges)],
    incomingEdgeTypes |-> [txnId \in txnIds |-> IncomingEdgeTypes(incomingEdges, txnId)],
    txnMustAbort |-> [txnId \in txnIds |-> TxnMustAbort(txnId, incomingEdges, outgoingEdges, txnHistory)],
    ccgraphalt |-> SerializationGraphWithEdgeTypes(txnHistory)
]



-------------------------------------------------

\* Some model checking details.

Symmetry == Permutations(keys) \cup Permutations(values) \cup Permutations(txnIds)


=============================================================================
\* Modification History
\* Last modified Tue Feb 27 12:56:09 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
