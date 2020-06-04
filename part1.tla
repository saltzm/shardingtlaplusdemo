---------------------------- MODULE part1 ----------------------------

EXTENDS Integers, FiniteSets, Sequences

\* A set of servers
CONSTANTS Server

\* A set of messages of the format [from : Server, to : Server, msg : Nat]
VARIABLE network

\* An integer counter used as the contents of the next message sent
VARIABLE nextMsgToSend

\* Type checks

\* Type check for network
NetworkTypeOK == network \subseteq [from : Server, to : Server, msg : Nat]

\* Type check for nextMsgToSend
NextMsgToSendTypeOK == nextMsgToSend \in Nat

----
\* Actions

\* Server 'from' sends message 'msg' over the network to server 'to'
SendMsg(from, to, msg) ==
    /\ from /= to
    /\ network' = network \union {[from |-> from, to |-> to, msg |-> msg]}
    /\ nextMsgToSend' = nextMsgToSend + 1

----
\* Spec

\* Define initial values for all variables
Init == 
    /\ network = {}
    /\ nextMsgToSend = 0

\* The "next state" relation, which specifies valid state transitions
Next ==
   \/ \E i, j \in Server : SendMsg(i, j, nextMsgToSend)

\* The full specification. 
Spec == Init /\ [][Next]_<<network, nextMsgToSend>>

----
\* Invariants

\* An assertion to make sure the types of the variables are correct at every state
TypeOK ==
    /\ NetworkTypeOK
    /\ NextMsgToSendTypeOK
    
\* Dummy invariant that we know will fail when the network has more than 2 messages
NetworkStaysSmall == 
    Cardinality(network) < 3

   
=============================================================================
\* Modification History
\* Last modified Fri May 15 11:05:00 EDT 2020 by matthewsaltz
\* Created Wed May 06 18:54:35 EDT 2020 by matthewsaltz
