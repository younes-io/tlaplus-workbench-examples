---- MODULE OfflineFirstSync ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Cross-device offline-first sync model with edits, deletes, tombstones,  *)
(* deterministic conflict resolution, and tombstone cleanup (GC).           *)
(*                                                                         *)
(* Conflict resolution: total-order Last-Writer-Wins over tags             *)
(* (timestamp, device-rank tie-break).                                     *)
(* GC model: tombstone -> purged while preserving the delete tag so older  *)
(* writes cannot resurrect deleted content.                                *)
(***************************************************************************)

CONSTANTS Devices, Keys, Values, MaxClock, MaxMsg

NoValue == 0
Kinds == {"val", "tomb", "purged"}
Modes == {"chaos", "stable"}

TagSet == [ts : 0..MaxClock, node : Devices]
RecordSet == [tag : TagSet, kind : Kinds, val : Values \cup {NoValue}]
MessageSet == [from : Devices, to : Devices, key : Keys, rec : RecordSet]

VARIABLES clock, store, online, net, writesOpen, mode

vars == <<clock, store, online, net, writesOpen, mode>>

ConstOK ==
  /\ Devices # {}
  /\ Keys # {}
  /\ Values # {}
  /\ Devices \subseteq Nat
  /\ Values \subseteq Nat
  /\ NoValue \notin Values
  /\ Cardinality(Devices) >= 2
  /\ MaxClock \in Nat
  /\ MaxClock > 0
  /\ MaxMsg \in Nat
  /\ MaxMsg > 0

MinNode ==
  CHOOSE d \in Devices:
    \A e \in Devices: d <= e

GenesisTag == [ts |-> 0, node |-> MinNode]
GenesisRec == [tag |-> GenesisTag, kind |-> "purged", val |-> NoValue]

KindRank(k) ==
  CASE k = "val" -> 0
    [] k = "tomb" -> 1
    [] OTHER -> 2

TagLT(t1, t2) ==
  \/ t1.ts < t2.ts
  \/ /\ t1.ts = t2.ts
     /\ t1.node < t2.node

TagLTE(t1, t2) == TagLT(t1, t2) \/ t1 = t2

ResolveEqualTag(r1, r2) ==
  IF KindRank(r1.kind) >= KindRank(r2.kind) THEN r1 ELSE r2

Merge(local, incoming) ==
  IF TagLT(local.tag, incoming.tag)
    THEN incoming
  ELSE IF TagLT(incoming.tag, local.tag)
    THEN local
  ELSE
    ResolveEqualTag(local, incoming)

MaxNum(a, b) == IF a >= b THEN a ELSE b

CanWrite(d) == writesOpen /\ clock[d] < MaxClock
NextTag(d) == [ts |-> clock[d] + 1, node |-> d]

TypeOK ==
  /\ clock \in [Devices -> 0..MaxClock]
  /\ store \in [Devices -> [Keys -> RecordSet]]
  /\ online \subseteq Devices
  /\ net \subseteq MessageSet
  /\ Cardinality(net) <= MaxMsg
  /\ writesOpen \in BOOLEAN
  /\ mode \in Modes

Init ==
  /\ ConstOK
  /\ clock = [d \in Devices |-> 0]
  /\ store = [d \in Devices |-> [k \in Keys |-> GenesisRec]]
  /\ online = Devices
  /\ net = {}
  /\ writesOpen = TRUE
  /\ mode = "chaos"

ToggleOnline(d) ==
  /\ d \in Devices
  /\ mode = "chaos"
  /\ online' = IF d \in online THEN online \ {d} ELSE online \cup {d}
  /\ UNCHANGED <<clock, store, net, writesOpen, mode>>

Stabilize ==
  /\ mode = "chaos"
  /\ mode' = "stable"
  /\ online' = Devices
  /\ UNCHANGED <<clock, store, net, writesOpen>>

StopWrites ==
  /\ writesOpen
  /\ writesOpen' = FALSE
  /\ UNCHANGED <<clock, store, online, net, mode>>

LocalEdit(d, k, v) ==
  /\ d \in Devices
  /\ k \in Keys
  /\ v \in Values
  /\ CanWrite(d)
  /\ LET rec == [tag |-> NextTag(d), kind |-> "val", val |-> v]
     IN
       /\ store' = [store EXCEPT ![d][k] = rec]
       /\ clock' = [clock EXCEPT ![d] = @ + 1]
  /\ UNCHANGED <<online, net, writesOpen, mode>>

LocalDelete(d, k) ==
  /\ d \in Devices
  /\ k \in Keys
  /\ CanWrite(d)
  /\ LET rec == [tag |-> NextTag(d), kind |-> "tomb", val |-> NoValue]
     IN
       /\ store' = [store EXCEPT ![d][k] = rec]
       /\ clock' = [clock EXCEPT ![d] = @ + 1]
  /\ UNCHANGED <<online, net, writesOpen, mode>>

Gossip(from, to, k) ==
  /\ from \in Devices
  /\ to \in Devices
  /\ k \in Keys
  /\ mode = "chaos"
  /\ from # to
  /\ from \in online
  /\ to \in online
  /\ LET msg == [from |-> from, to |-> to, key |-> k, rec |-> store[from][k]]
     IN
       /\ msg \notin net
       /\ Cardinality(net) < MaxMsg
       /\ net' = net \cup {msg}
  /\ UNCHANGED <<clock, store, online, writesOpen, mode>>

Deliver(m) ==
  /\ m \in net
  /\ m.to \in online
  /\ LET merged == Merge(store[m.to][m.key], m.rec)
     IN
       /\ store' = [store EXCEPT ![m.to][m.key] = merged]
       /\ clock' = [clock EXCEPT ![m.to] = MaxNum(@, m.rec.tag.ts)]
       /\ net' = net \ {m}
  /\ UNCHANGED <<online, writesOpen, mode>>

AntiEntropy(from, to, k) ==
  /\ from \in Devices
  /\ to \in Devices
  /\ k \in Keys
  /\ mode = "stable"
  /\ from # to
  /\ LET merged == Merge(store[to][k], store[from][k])
     IN
       /\ store' = [store EXCEPT ![to][k] = merged]
       /\ clock' = [clock EXCEPT ![to] = MaxNum(@, store[from][k].tag.ts)]
  /\ UNCHANGED <<online, net, writesOpen, mode>>

Drop(m) ==
  /\ mode = "chaos"
  /\ m \in net
  /\ net' = net \ {m}
  /\ UNCHANGED <<clock, store, online, writesOpen, mode>>

GC(d, k) ==
  /\ d \in Devices
  /\ k \in Keys
  /\ store[d][k].kind = "tomb"
  /\ store' =
       [store EXCEPT
         ![d][k] = [@ EXCEPT !.kind = "purged", !.val = NoValue]
       ]
  /\ UNCHANGED <<clock, online, net, writesOpen, mode>>

Next ==
  \/ \E d \in Devices: ToggleOnline(d)
  \/ Stabilize
  \/ StopWrites
  \/ \E d \in Devices: \E k \in Keys: \E v \in Values: LocalEdit(d, k, v)
  \/ \E d \in Devices: \E k \in Keys: LocalDelete(d, k)
  \/ \E from \in Devices: \E to \in Devices: \E k \in Keys: Gossip(from, to, k)
  \/ \E m \in net: Deliver(m)
  \/ \E from \in Devices: \E to \in Devices: \E k \in Keys: AntiEntropy(from, to, k)
  \/ \E m \in net: Drop(m)
  \/ \E d \in Devices: \E k \in Keys: GC(d, k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Stabilize)
  /\ WF_vars(StopWrites)
  /\ \A from \in Devices:
       \A to \in Devices \ {from}:
         \A k \in Keys:
           WF_vars(AntiEntropy(from, to, k))
  /\ \A m \in MessageSet: WF_vars(Deliver(m))
  /\ \A d \in Devices: \A k \in Keys: WF_vars(GC(d, k))

ClockCoversAppliedTags ==
  \A d \in Devices:
    \A k \in Keys:
      store[d][k].tag.ts <= clock[d]

StableMeansAllOnline == (mode = "stable") => online = Devices

DeleteKindsHaveNoValue ==
  \A d \in Devices:
    \A k \in Keys:
      (store[d][k].kind # "val") => (store[d][k].val = NoValue)

MergeChoosesMaxTag ==
  \A r1 \in RecordSet:
    \A r2 \in RecordSet:
      /\ TagLTE(r1.tag, Merge(r1, r2).tag)
      /\ TagLTE(r2.tag, Merge(r1, r2).tag)

ConflictResolutionDeterministic ==
  \A d1 \in Devices:
    \A d2 \in Devices:
      \A k \in Keys:
        Merge(store[d1][k], store[d2][k]) =
          Merge(store[d2][k], store[d1][k])

Converged ==
  \A k \in Keys:
    \A d1 \in Devices:
      \A d2 \in Devices:
        store[d1][k] = store[d2][k]

NoTombstones ==
  \A d \in Devices:
    \A k \in Keys:
      store[d][k].kind # "tomb"

Quiescent == /\ mode = "stable"
            /\ ~writesOpen

EventuallyQuiescent == <>Quiescent

ConvergesAfterQuiescence == [](Quiescent => <>Converged)

TombstonesEventuallyPurged == [](Quiescent /\ Converged => <>NoTombstones)

====
