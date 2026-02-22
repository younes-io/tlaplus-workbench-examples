---- MODULE WalletLedgerAA ----
EXTENDS Naturals, Integers, TLC

\* Finite bounds chosen for model checking.
Regions == { "us_east", "eu_west" }
Wallets == { "alice", "bob" }
Keys == { "k1", "k2" }

InitBal == [w \in Wallets |-> IF w = "alice" THEN 3 ELSE 1]
KeySrc == [k \in Keys |-> "alice"]
KeyDst == [k \in Keys |-> "bob"]
KeyAmt == [k \in Keys |-> IF k = "k1" THEN 1 ELSE 3]
Home == [k \in Keys |-> IF k = "k1" THEN "us_east" ELSE "eu_west"]

DecisionStatus == { "none", "pending", "committed", "compensated", "rejected" }
ViewStatus ==
  { "none", "submitted", "pending", "committed", "compensated", "rejected" }
TerminalStatus == { "committed", "compensated", "rejected" }
ReplicatedStatus == { "pending", "committed", "compensated", "rejected" }

ReqMsg == [from:Regions, to:Regions, key:Keys ]
RepMsg == [to:Regions, key:Keys, status:ReplicatedStatus ]

VARIABLES homeBal,
          decision,
          regionView,
          replicaBal,
          reqMsgs,
          repMsgs,
          reserveCount

vars ==
  << homeBal,
     decision,
     regionView,
     replicaBal,
     reqMsgs,
     repMsgs,
     reserveCount
  >>

ConstOK == /\ Regions # {}
           /\ Wallets # {}
           /\ Keys # {}
           /\ InitBal \in [Wallets -> Nat]
           /\ KeySrc \in [Keys -> Wallets]
           /\ KeyDst \in [Keys -> Wallets]
           /\ KeyAmt \in [Keys -> Nat]
           /\ \A k \in Keys: KeyAmt[k] > 0
           /\ Home \in [Keys -> Regions]

TypeOK == /\ homeBal \in [Wallets -> Nat]
          /\ decision \in [Keys -> DecisionStatus]
          /\ regionView \in [Regions -> [Keys -> ViewStatus]]
          /\ replicaBal \in [Regions -> [Wallets -> Int]]
          /\ reqMsgs \subseteq ReqMsg
          /\ repMsgs \subseteq RepMsg
          /\ reserveCount \in [Keys -> 0 .. 1]

Broadcast(st, k) == {[ to |-> r, key |-> k, status |-> st ]: r \in Regions}

ViewRank(st) == CASE st = "none" -> 0
                [] st = "submitted" -> 1
                [] st = "pending" -> 2
                [] OTHER-> 3

MergeViewStatus(old, new) == IF ViewRank(new) > ViewRank(old) THEN new ELSE old

ApplyReplicaDelta(bals, r, st, k) ==
  IF st = "pending"
  THEN [bals EXCEPT ![r][KeySrc[k]] = @ - KeyAmt[k]]
  ELSE IF st = "committed"
    THEN [bals EXCEPT ![r][KeyDst[k]] = @ + KeyAmt[k]]
    ELSE IF st = "compensated"
      THEN [bals EXCEPT ![r][KeySrc[k]] = @ + KeyAmt[k]]
      ELSE bals

Init == /\ ConstOK
        /\ homeBal = InitBal
        /\ decision = [k \in Keys |-> "none"]
        /\ regionView = [r \in Regions |-> [k \in Keys |-> "none"]]
        /\ replicaBal = [r \in Regions |-> InitBal]
        /\ reqMsgs = {}
        /\ repMsgs = {}
        /\ reserveCount = [k \in Keys |-> 0]

Submit(r, k) ==
  /\ r \in Regions
  /\ k \in Keys
  /\ regionView[r][k] = "none"
  /\ regionView' = [regionView EXCEPT ![r][k] = "submitted"]
  /\ reqMsgs' = reqMsgs \cup { [ from |-> r, to |-> Home[k], key |-> k ] }
  /\ UNCHANGED << homeBal, decision, replicaBal, repMsgs, reserveCount >>

HandleRequest(m) ==
  /\ m \in reqMsgs
  /\ m.to = Home[m.key]
  /\ reqMsgs' = reqMsgs \ { m }
  /\ IF decision[m.key] = "none"
     THEN IF homeBal[KeySrc[m.key]] >= KeyAmt[m.key]
       THEN /\ decision' = [decision EXCEPT ![m.key] = "pending"]
            /\ homeBal' = [homeBal EXCEPT ![KeySrc[m.key]] = @ - KeyAmt[m.key]]
            /\ repMsgs' = repMsgs \cup Broadcast("pending", m.key)
            /\ reserveCount' = [reserveCount EXCEPT ![m.key] = 1]
       ELSE /\ decision' = [decision EXCEPT ![m.key] = "rejected"]
            /\ homeBal' = homeBal
            /\ repMsgs' = repMsgs \cup Broadcast("rejected", m.key)
            /\ reserveCount' = reserveCount
     ELSE /\ UNCHANGED << homeBal, decision, repMsgs, reserveCount >>
  /\ UNCHANGED << regionView, replicaBal >>

FinalizeCommit(k) ==
  /\ k \in Keys
  /\ decision[k] = "pending"
  /\ decision' = [decision EXCEPT ![k] = "committed"]
  /\ homeBal' = [homeBal EXCEPT ![KeyDst[k]] = @ + KeyAmt[k]]
  /\ repMsgs' = repMsgs \cup Broadcast("committed", k)
  /\ UNCHANGED << regionView, replicaBal, reqMsgs, reserveCount >>

FinalizeCompensate(k) ==
  /\ k \in Keys
  /\ decision[k] = "pending"
  /\ decision' = [decision EXCEPT ![k] = "compensated"]
  /\ homeBal' = [homeBal EXCEPT ![KeySrc[k]] = @ + KeyAmt[k]]
  /\ repMsgs' = repMsgs \cup Broadcast("compensated", k)
  /\ UNCHANGED << regionView, replicaBal, reqMsgs, reserveCount >>

DeliverReplication(m) ==
  /\ m \in repMsgs
  /\ repMsgs' = repMsgs \ { m }
  /\ regionView' =
       [regionView EXCEPT ![m.to][m.key] = MergeViewStatus(@, m.status)]
  /\ replicaBal' = ApplyReplicaDelta(replicaBal, m.to, m.status, m.key)
  /\ UNCHANGED << homeBal, decision, reqMsgs, reserveCount >>

SubmitAny == \E r \in Regions: \E k \in Keys: Submit(r, k)

HandleAny == \E m \in reqMsgs: HandleRequest(m)

FinalizeAny == \E k \in Keys: FinalizeCommit(k) \/ FinalizeCompensate(k)

DeliverAny == \E m \in repMsgs: DeliverReplication(m)

Quiescent == /\ reqMsgs = {}
             /\ repMsgs = {}
             /\ \A k \in Keys: decision[k] \in TerminalStatus
             /\ \A r \in Regions: \A k \in Keys: regionView[r][k] = decision[k]

IdleQuiescent == /\ Quiescent
                 /\ UNCHANGED vars

Next == \/ SubmitAny
        \/ HandleAny
        \/ FinalizeAny
        \/ DeliverAny
        \/ IdleQuiescent

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(HandleAny)
        /\ WF_vars(FinalizeAny)
        /\ WF_vars(DeliverAny)

HomeNonNegative == \A w \in Wallets: homeBal[w] >= 0

ReplicaNonNegative == \A r \in Regions: \A w \in Wallets: replicaBal[r][w] >= 0

ReserveCountAtMostOnce == \A k \in Keys: reserveCount[k] <= 1

DecisionLifecycleConsistent ==
  \A k \in Keys: /\ ( decision[k] = "none" => reserveCount[k] = 0 )
                 /\ ( decision[k] = "pending" => reserveCount[k] = 1 )
                 /\ ( decision[k] = "committed" => reserveCount[k] = 1 )
                 /\ ( decision[k] = "compensated" => reserveCount[k] = 1 )
                 /\ ( decision[k] = "rejected" => reserveCount[k] = 0 )

TerminalAgreement ==
  \A r1 \in Regions:
    \A r2 \in Regions: \A k \in Keys: /\ regionView[r1][k] \in TerminalStatus
                                      /\ regionView[r2][k] \in TerminalStatus
        => regionView[r1][k] = regionView[r2][k]

PendingEventuallyTerminal ==
  \A k \in Keys:
    []( ( decision[k] = "pending" ) => <>( decision[k] \in TerminalStatus ) )

TerminalDecisionEventuallyVisible ==
  \A k \in Keys:
    \A r \in Regions:
      []( ( decision[k] \in TerminalStatus ) =>
          <>( regionView[r][k] = decision[k] )
      )

====
