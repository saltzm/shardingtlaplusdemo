------------------------------- MODULE part2 -------------------------------

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
    /\ network' = network \union {[from |-> from, to |-> to, msg |-> msg]}
    /\ nextMsgToSend' = nextMsgToSend + 1
    
\****** NEW THING ******
\* Split the "preconditions" and selection from the actual state update
SendMsgAction ==  
    \E i, j \in Server: 
        /\ i /= j
        /\ SendMsg(i, j, nextMsgToSend) 
        
\****** NEW THING ******
\* No-op for receiving a message
ReceiveMsg(server, msg) ==
    \* If you comment this out, you get the error:
    \* Successor state is not completely specified by action ReceiveMsgAction of the next-state relation. 
    \* The following variable is not assigned: nextMsgToSend.
    /\ UNCHANGED <<nextMsgToSend>> \* equivalent to nextMsgToSend' = nextMsgToSend
    
ReceiveMsgAction == 
    \E i \in Server: 
    \E msg \in network: msg.to = i
    /\ ReceiveMsg(i, msg)
    
----
\* Invariants

\* Dummy invariant that will fail
NetworkStaysSmall == 
    Cardinality(network) < 3

\* An assertion to make sure the types of the variables are correct at every state
TypeOK ==
    /\ NetworkTypeOK
    /\ NextMsgToSendTypeOK

----

\* Define initial values for all variables
Init == 
    /\ network = {}
    /\ nextMsgToSend = 0

Next ==
   \/ SendMsgAction
   \/ ReceiveMsgAction

\* The full specification. 
Spec == Init /\ [][Next]_<<network, nextMsgToSend>>

=============================================================================
\* Modification History
\* Last modified Fri May 15 11:04:52 EDT 2020 by matthewsaltz
\* Created Wed May 06 19:34:45 EDT 2020 by matthewsaltz
