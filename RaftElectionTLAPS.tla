---- MODULE RaftElectionTLAPS ----
EXTENDS Naturals, FiniteSets

\* Business configuration:
\* - Servers: participating nodes in the Raft cluster.
\* - Quorums: vote sets that count as a winning majority.
\* - NoVote: sentinel value meaning "this server has not voted in that term".
CONSTANTS Servers, Quorums, NoVote

\* Safety policy: any two winning vote sets must overlap.
\* Business meaning: two different leaders cannot both gather disjoint majorities.
AXIOM QuorumIntersection ==
  \A Q1 \in Quorums:
    \A Q2 \in Quorums:
      Q1 \cap Q2 # {}

\* Environment assumptions for the deployment model.
ASSUME
  /\ IsFiniteSet(Servers)
  /\ Servers # {}
  /\ Quorums \subseteq SUBSET Servers
  /\ NoVote \notin Servers

\* Trusted arithmetic facts used by TLAPS in monotonicity reasoning.
AXIOM SuccMonotone ==
  \A n \in Nat:
    n + 1 >= n

AXIOM NatLeqReflexive ==
  \A n \in Nat:
    n >= n

\* Runtime state:
\* - term: current election term.
\* - votedFor[t][s]: candidate chosen by server s in term t.
VARIABLES term, votedFor

vars == <<term, votedFor>>

\* Type contract for all states.
TypeOK ==
  /\ term \in Nat
  /\ votedFor \in [Nat -> [Servers -> (Servers \cup {NoVote})]]

\* Initial business state: system starts at term 0, with no recorded votes.
Init ==
  /\ term = 0
  /\ votedFor = [t \in Nat |-> [s \in Servers |-> NoVote]]

\* Election rollover: move to the next term without rewriting prior votes.
StartNewTerm ==
  /\ term' = term + 1
  /\ UNCHANGED votedFor

\* Voting rule: in the current term, a server can cast at most one vote.
CastVote(v, c) ==
  /\ v \in Servers
  /\ c \in Servers
  /\ votedFor[term][v] = NoVote
  /\ votedFor' = [votedFor EXCEPT ![term][v] = c]
  /\ UNCHANGED term

\* Allowed operational step: either open a new term or record one vote.
Next ==
  StartNewTerm
  \/ (\E v \in Servers: \E c \in Servers: CastVote(v, c))

\* System behavior specification.
Spec == Init /\ [][Next]_vars

\* Vote tally helper for candidate c in term t.
VotesFor(t, c) == {v \in Servers: votedFor[t][v] = c}

\* Business definition of "leader for term t": candidate has a quorum.
LeaderForTerm(t, c) == VotesFor(t, c) \in Quorums

\* Safety requirement: there is at most one leader per term.
LeaderUniquenessPerTerm ==
  \A t \in Nat:
    \A c1 \in Servers:
      \A c2 \in Servers:
        (LeaderForTerm(t, c1) /\ LeaderForTerm(t, c2)) => c1 = c2

\* Monotonicity requirement for one transition step.
TermMonotonicStep == term' >= term

\* Proof of leader uniqueness from quorum intersection.
THEOREM LeaderUniquenessPerTermHolds ==
  ASSUME NEW t \in Nat,
         NEW c1 \in Servers,
         NEW c2 \in Servers,
         LeaderForTerm(t, c1),
         LeaderForTerm(t, c2)
  PROVE c1 = c2
PROOF
  <1>1. VotesFor(t, c1) \in Quorums
    BY DEF LeaderForTerm
  <1>2. VotesFor(t, c2) \in Quorums
    BY DEF LeaderForTerm
  <1>3. VotesFor(t, c1) \cap VotesFor(t, c2) # {}
    BY <1>1, <1>2, QuorumIntersection
  <1>4. \E v \in VotesFor(t, c1) \cap VotesFor(t, c2): TRUE
    BY <1>3
  <1>5. PICK v \in VotesFor(t, c1) \cap VotesFor(t, c2): TRUE
    BY <1>4
  <1>6. v \in VotesFor(t, c1)
    BY <1>5
  <1>7. v \in VotesFor(t, c2)
    BY <1>5
  <1>8. votedFor[t][v] = c1
    BY <1>6 DEF VotesFor
  <1>9. votedFor[t][v] = c2
    BY <1>7 DEF VotesFor
  <1>10. QED
    BY <1>8, <1>9

\* Proof that no transition decreases the current term.
THEOREM TermMonotonicStepHolds ==
  ASSUME TypeOK, Next
  PROVE TermMonotonicStep
PROOF
  <1>1. CASE StartNewTerm
    <2>1. term' = term + 1
      BY <1>1 DEF StartNewTerm
    <2>2. term + 1 >= term
      BY SuccMonotone, TypeOK DEF TypeOK
    <2>3. QED
      BY <2>1, <2>2 DEF TermMonotonicStep
  <1>2. CASE \E v \in Servers: \E c \in Servers: CastVote(v, c)
    <2>1. term' = term
      BY <1>2 DEF CastVote
    <2>2. term >= term
      BY NatLeqReflexive, TypeOK DEF TypeOK
    <2>3. QED
      BY <2>1, <2>2 DEF TermMonotonicStep
  <1>3. QED
    BY <1>1, <1>2 DEF Next

=============================================================================
