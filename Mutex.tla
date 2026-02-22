---- MODULE Mutex ----
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS Clients

VARIABLES holders, req

vars == <<holders, req>>

TypeOK ==
  /\ holders \subseteq Clients
  /\ req \in [Clients -> BOOLEAN]

Init ==
  /\ holders = {}
  /\ req = [c \in Clients |-> FALSE]

Request(c) ==
  /\ c \in Clients
  /\ ~req[c]
  /\ req' = [req EXCEPT ![c] = TRUE]
  /\ UNCHANGED holders

Acquire(c) ==
  /\ c \in Clients
  /\ holders = {}
  /\ req[c]
  /\ holders' = {c}
  /\ req' = [req EXCEPT ![c] = FALSE]

Release(c) ==
  /\ c \in Clients
  /\ c \in holders
  /\ holders' = {}
  /\ UNCHANGED req

Next ==
  \E c \in Clients: Request(c) \/ Acquire(c) \/ Release(c)

Fairness ==
  /\ \A c \in Clients: SF_vars(Acquire(c))
  /\ \A c \in Clients: WF_vars(Release(c))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
  Cardinality(holders) <= 1

GrantWhenFree(c) ==
  (holders = {} /\ req[c]) ~> (c \in holders)

Liveness ==
  \A c \in Clients: GrantWhenFree(c)

=============================================================================
