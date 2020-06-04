------------------------------- MODULE part5 -------------------------------

\** WORKING AT-MOST-ONCE PROCESSING

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Server

\* A set of messages of the format [from -> Server, to -> Server, msg -> Integer]
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
\* Define initial values for all variables

Init == 
    /\ network = {}
    /\ messagesProcessed = [s \in Server |-> <<>>]     
    /\ nextMsgIdToSend = [s \in Server |-> 0]
    /\ messageIdsProcessed = [s \in Server |-> {}]
    /\ nextMsgToSend = 0

----
\* Generic helpers
MaxId(s) == IF Cardinality(s) = 0 THEN 0 ELSE CHOOSE x \in s : \A y \in s : x >= y
----

\* Sometimes adds message to network, sometimes does nothing
SendOnUnreliableNetwork(msg) ==
    \/ network' = network \union {msg}
    \/ UNCHANGED <<network>>
    
ProcessMessage(server, msg) ==
    messagesProcessed' = [messagesProcessed EXCEPT ![server] = Append(messagesProcessed[server], msg.data)]

----

SendMsg(from, to, data) ==
    /\ SendOnUnreliableNetwork([from |-> from, 
                                to |-> to, 
                                data |-> [id |-> nextMsgIdToSend[from], 
                                          data |-> data]])
    /\ nextMsgIdToSend' = [nextMsgIdToSend EXCEPT ![from] = @ + 1]
    /\ nextMsgToSend' = nextMsgToSend + 1
    /\ UNCHANGED <<messagesProcessed, messageIdsProcessed>>
    
ReceiveMsg(server, msg) ==
    \* This is new. We don't need this whole set just for this
    /\ msg.data.id > MaxId(messageIdsProcessed[server])
    /\ messageIdsProcessed' = [messageIdsProcessed EXCEPT ![server] = @ \union {msg.data.id}]
    /\ messagesProcessed' = [messagesProcessed EXCEPT ![server] = Append(messagesProcessed[server], msg.data)]
    /\ UNCHANGED <<nextMsgToSend, nextMsgIdToSend, network>>
    
----

\* Invariants
MessagesProcessedAtMostOnce == 
    \A s \in Server:
        ~\E i, j \in DOMAIN messagesProcessed[s]: 
            /\ i /= j 
            /\ messagesProcessed[s][i] = messagesProcessed[s][j]

\* TODO more than one sender on a single server
MessagesProcessedInMonotonicallyIncreasingOrder == 
    \A s \in Server:
        \A i, j \in DOMAIN messagesProcessed[s]:
            i < j => messagesProcessed[s][i].id < messagesProcessed[s][j].id

AllInvariants ==
    /\ MessagesProcessedAtMostOnce
    /\ MessagesProcessedInMonotonicallyIncreasingOrder

----
SendMsgAction ==  
    \E i, j \in Server: 
        /\ i /= j
        /\ SendMsg(i, j, nextMsgToSend) 

ReceiveMsgAction == 
    \E i \in Server: 
    \E msg \in network: msg.from = i 
    /\ ReceiveMsg(i, msg)

Next ==
   \/ SendMsgAction
   \/ ReceiveMsgAction
   
=============================================================================
\* Modification History
\* Last modified Fri May 15 11:19:57 EDT 2020 by matthewsaltz
\* Created Wed May 06 19:34:45 EDT 2020 by matthewsaltz
