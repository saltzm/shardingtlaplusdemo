------------------------------- MODULE part4 -------------------------------
\** WORKING at-most-once processing

EXTENDS Integers, FiniteSets, Sequences

----
\* Global state

\* A set of servers
CONSTANTS Server

\* A set of messages of the format [from : Server, to : Server, msg : Nat]
VARIABLE network

\* An integer counter used as the contents of the next message sent
VARIABLE nextMsgToSend

\* A map from Server -> Ordered list of messages processed by that server
VARIABLE messagesProcessed

----
\* Per-server "protocol" related state

\* A map from Server -> Next message id for that server
VARIABLE nextMsgIdToSend

\* A map from Server -> Set of message ids seen by server
VARIABLE messageIdsProcessed

----
\* Type checks

\* Type check for network
NetworkTypeOK == network \subseteq [from : Server, to : Server, msg : Nat]

\* Type check for nextMsgToSend
NextMsgToSendTypeOK == nextMsgToSend \in Nat

\* Type check for messagesProcessed
MessagesProcessedTypeOK == TRUE \* TODO

\* TODO type checks for per-server state

----
\* Helpers

\* Sometimes adds message to network, sometimes does nothing
SendOnUnreliableNetwork(msg) ==
    \/ network' = network \union {msg}
    \/ UNCHANGED <<network>>

----
\* State update actions

SendMsg(from, to, data) ==
    /\ SendOnUnreliableNetwork([from |-> from, to |-> to, data |-> [id |-> nextMsgIdToSend[from], data |-> data]])
    \* Increment the next message id to send for this server
    /\ nextMsgIdToSend' = [nextMsgIdToSend EXCEPT ![from] = @ + 1]
    /\ nextMsgToSend' = nextMsgToSend + 1
    /\ UNCHANGED <<messagesProcessed, messageIdsProcessed>>

ReceiveMsg(server, msg) ==
    \* Only process the message if this server hasn't seen a message with that id before
    /\ \E id \in messageIdsProcessed[server]: msg.data.id = id
    \* Add the message id to the list of ids processed
    /\ messageIdsProcessed' = [messageIdsProcessed EXCEPT ![server] = @ \union {msg.data.id}]
    /\ messagesProcessed' = [messagesProcessed EXCEPT ![server] = Append(messagesProcessed[server], msg.data)]
    /\ UNCHANGED <<nextMsgToSend, nextMsgIdToSend>>
    
----
\* Action selectors

SendMsgAction ==  
    \E i, j \in Server: 
        /\ i /= j
        /\ SendMsg(i, j, nextMsgToSend) 
    
ReceiveMsgAction == 
    \E i \in Server: 
    \E msg \in network: msg.to = i 
    /\ ReceiveMsg(i, msg)
    
----
\* Invariants
MessagesProcessedAtMostOnce == 
    \A s \in Server:
        ~\E i, j \in DOMAIN messagesProcessed[s]: 
            /\ i /= j 
            /\ messagesProcessed[s][i] = messagesProcessed[s][j]
    
\* An assertion to make sure the types of the variables are correct at every state
TypeOK ==
    /\ NetworkTypeOK
    /\ NextMsgToSendTypeOK
    /\ MessagesProcessedTypeOK
    \* TODO add per-server state

----
\* Spec
   
Init == 
    /\ network = {}
    /\ messagesProcessed = [s \in Server |-> <<>>]     
    /\ nextMsgIdToSend = [s \in Server |-> 0]
    /\ messageIdsProcessed = [s \in Server |-> {}]
    /\ nextMsgToSend = 0

Next ==
   \/ SendMsgAction
   \/ ReceiveMsgAction
   
=============================================================================
\* Modification History
\* Last modified Fri May 15 11:23:30 EDT 2020 by matthewsaltz
\* Created Wed May 06 19:34:45 EDT 2020 by matthewsaltz
