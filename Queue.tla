---- MODULE Queue ----
EXTENDS Naturals, Sequences

CONSTANTS Msgs, MaxDataQ, MaxAckQ

ASSUME Msgs # {}
ASSUME MaxDataQ \in Nat \ {0}
ASSUME MaxAckQ \in Nat \ {0}

VARIABLES
    sent,         \* messages sent at least once
    inFlight,     \* sent but not yet acked
    acked,        \* ack observed by sender
    delivered,    \* delivered to receiver application
    deliverCount, \* saturated delivery count per message (0..2)
    dataQ,        \* network data queue (subject to drop/reorder)
    ackQ          \* network ack queue (subject to drop/reorder)

vars == << sent, inFlight, acked, delivered, deliverCount, dataQ, ackQ >>

Min2(n) == IF n >= 2 THEN 2 ELSE n

DropAt(seq, i) ==
    SubSeq(seq, 1, i - 1) \o SubSeq(seq, i + 1, Len(seq))

Swap(seq, i, j) ==
    [k \in 1..Len(seq) |->
        IF k = i THEN seq[j]
        ELSE IF k = j THEN seq[i]
        ELSE seq[k]
    ]

Init ==
    /\ sent = {}
    /\ inFlight = {}
    /\ acked = {}
    /\ delivered = {}
    /\ deliverCount = [m \in Msgs |-> 0]
    /\ dataQ = << >>
    /\ ackQ = << >>

SendFresh(m) ==
    /\ m \in Msgs \ sent
    /\ Len(dataQ) < MaxDataQ
    /\ sent' = sent \cup {m}
    /\ inFlight' = inFlight \cup {m}
    /\ dataQ' = Append(dataQ, m)
    /\ UNCHANGED << acked, delivered, deliverCount, ackQ >>

Retry(m) ==
    /\ m \in inFlight
    /\ Len(dataQ) < MaxDataQ
    /\ dataQ' = Append(dataQ, m)
    /\ UNCHANGED << sent, inFlight, acked, delivered, deliverCount, ackQ >>

DataDrop(i) ==
    /\ Len(dataQ) > 0
    /\ i \in 1..Len(dataQ)
    /\ dataQ' = DropAt(dataQ, i)
    /\ UNCHANGED << sent, inFlight, acked, delivered, deliverCount, ackQ >>

DataReorder(i, j) ==
    /\ Len(dataQ) >= 2
    /\ i \in 1..Len(dataQ)
    /\ j \in 1..Len(dataQ)
    /\ i # j
    /\ dataQ' = Swap(dataQ, i, j)
    /\ UNCHANGED << sent, inFlight, acked, delivered, deliverCount, ackQ >>

ReceiveData ==
    /\ Len(dataQ) > 0
    /\ LET m == Head(dataQ) IN
        /\ dataQ' = Tail(dataQ)
        /\ IF m \notin delivered
              THEN /\ delivered' = delivered \cup {m}
                   /\ deliverCount' = [deliverCount EXCEPT ![m] = Min2(@ + 1)]
              ELSE /\ delivered' = delivered
                   /\ deliverCount' = deliverCount
        /\ ackQ' = IF Len(ackQ) < MaxAckQ THEN Append(ackQ, m) ELSE ackQ
    /\ UNCHANGED << sent, inFlight, acked >>

AckDrop(i) ==
    /\ Len(ackQ) > 0
    /\ i \in 1..Len(ackQ)
    /\ ackQ' = DropAt(ackQ, i)
    /\ UNCHANGED << sent, inFlight, acked, delivered, deliverCount, dataQ >>

AckReorder(i, j) ==
    /\ Len(ackQ) >= 2
    /\ i \in 1..Len(ackQ)
    /\ j \in 1..Len(ackQ)
    /\ i # j
    /\ ackQ' = Swap(ackQ, i, j)
    /\ UNCHANGED << sent, inFlight, acked, delivered, deliverCount, dataQ >>

ReceiveAck ==
    /\ Len(ackQ) > 0
    /\ LET m == Head(ackQ) IN
        /\ ackQ' = Tail(ackQ)
        /\ acked' = acked \cup {m}
        /\ inFlight' = inFlight \ {m}
    /\ UNCHANGED << sent, delivered, deliverCount, dataQ >>

Done ==
    /\ sent = Msgs
    /\ acked = Msgs
    /\ inFlight = {}
    /\ dataQ = << >>
    /\ ackQ = << >>

IdleWhenDone ==
    /\ Done
    /\ UNCHANGED vars

Next ==
    \/ \E m \in Msgs: SendFresh(m)
    \/ \E m \in Msgs: Retry(m)
    \/ \E i \in 1..Len(dataQ): DataDrop(i)
    \/ \E i \in 1..Len(dataQ), j \in 1..Len(dataQ): DataReorder(i, j)
    \/ ReceiveData
    \/ \E i \in 1..Len(ackQ): AckDrop(i)
    \/ \E i \in 1..Len(ackQ), j \in 1..Len(ackQ): AckReorder(i, j)
    \/ ReceiveAck
    \/ IdleWhenDone

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ sent \subseteq Msgs
    /\ inFlight \subseteq Msgs
    /\ acked \subseteq Msgs
    /\ delivered \subseteq Msgs
    /\ acked \subseteq sent
    /\ inFlight \subseteq sent
    /\ acked \cap inFlight = {}
    /\ deliverCount \in [Msgs -> 0..2]
    /\ dataQ \in Seq(Msgs)
    /\ ackQ \in Seq(Msgs)
    /\ Len(dataQ) <= MaxDataQ
    /\ Len(ackQ) <= MaxAckQ

NoDuplicateDeliver ==
    \A m \in Msgs: deliverCount[m] <= 1

DeliveryCountConsistent ==
    \A m \in Msgs: deliverCount[m] = IF m \in delivered THEN 1 ELSE 0

DeliveredOnlyIfSent ==
    delivered \subseteq sent

====
