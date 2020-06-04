---------------------------- MODULE part1 ----------------------------

EXTENDS Integers, FiniteSets, Sequences

\* A set of servers
CONSTANTS Server

\* A set of messages of the format [from : Server, to : Server, msg : Nat]
VARIABLE network

\* An integer counter used as the contents of the next message sent
\*
\* NOTE: It's okay to do this when modeling! Simplify model by having a global variable
\* that is shared across all servers.
VARIABLE nextMsgToSend

\* Type checks

\* Type check for network
\* Notes:
\*     A == B defines a new proposition A which evaluates to B, which is some truth value
\*     [from : Server, to : Server, msg : Nat] is the set of all structures of the form 
\*     [from |-> <server>, to |-> <server>, msg |-> <natural number>]. A structure is like a map.
NetworkTypeOK == network \subseteq [from : Server, to : Server, msg : Nat]
\* Could also write:
\*               \A msg \in network: msg \in [from : Server, to : Server, msg : Nat]

\* Type check for nextMsgToSend
NextMsgToSendTypeOK == nextMsgToSend \in Nat

----
\* Actions

\* Server 'from' sends message 'msg' over the network to server 'to'
SendMsg(from, to, msg) ==
    /\ from /= to \* Precondition
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
\*
\* This says that the specification is satisfied for a given sequence of states (a "behavior") if the 
\* initial conditions hold, and for every state in the behavior (which is a sequence of states), the 
\* "next state" relation holds.
Spec == Init /\ [][Next]_<<network, nextMsgToSend>>

\*
\* A sequence of steps/state transitions is called a "behavior" of the system.
\* 
\* Mandatory disclaimer: A spec is MATH, not CODE. But it's okay to think of it as code until you get 
\* used to it :)
\*
\* Possible behaviors
\* Valid (satisfies the spec):
\*  Step 0: network = {}, nextMsgToSend = 0
\*  Step 1: network = {[from |-> s1, to |-> s2, msg |-> 0]}, nextMsgToSend = 1
\*  Step 2: network = {[from |-> s1, to |-> s2, msg |-> 0], [from |-> s1, to |-> s2, msg |-> 1]}
\*
\* Invalid (does not satisfy the spec because a node sends a message to itself):
\*  Step 0: network = {}, nextMsgToSend = 0
\*  Step 1: network = {[from |-> s1, to |-> s1, msg |-> 0]} \* ILLEGAL because to = from!

\* Invalid (does not satisfy the spec because inital conditions are violated):
\*  Step 0: network = {[I_REALLY_LOVE |-> TACOS]}, nextMsgToSend = 0
\*  Step 1: network = {[from |-> s1, to |-> s2, msg |-> 0]}
\*  Step 2: network = {[from |-> s1, to |-> s2, msg |-> 0]}

----
\* Invariants

\* An assertion to make sure the types of the variables are correct at every state
TypeOK ==
    /\ NetworkTypeOK
    /\ NextMsgToSendTypeOK
    
\* Dummy invariant that we know will fail
NetworkStaysSmall == 
    Cardinality(network) < 3

   
=============================================================================
\* Modification History
\* Last modified Fri May 15 19:55:12 EDT 2020 by matthewsaltz
\* Created Wed May 06 18:54:35 EDT 2020 by matthewsaltz
