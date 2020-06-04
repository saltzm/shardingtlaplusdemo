------------------------------- MODULE part3 -------------------------------

EXTENDS Integers, FiniteSets, Sequences

\* A set of servers
CONSTANTS Server

\* A set of messages of the format [from : Server, to : Server, msg : Nat]
VARIABLE network

\* An integer counter used as the contents of the next message sent
VARIABLE nextMsgToSend

\* A map from Server -> Ordered list of messages processed by that server
VARIABLE messagesProcessed

----
\* Type checks

\* Type check for network
NetworkTypeOK == network \subseteq [from : Server, to : Server, msg : Nat]

\* Type check for nextMsgToSend
NextMsgToSendTypeOK == nextMsgToSend \in Nat

\* Type check for messagesProcessed
MessagesProcessedTypeOK == TRUE \* TODO

----
\* Helpers

\* Sometimes adds message to network, sometimes does nothing
SendOnUnreliableNetwork(msg) ==
    \/ network' = network \union {msg}
    \/ UNCHANGED <<network>>
    
----
\* Actions

SendMsg(from, to, msg) ==
    /\ SendOnUnreliableNetwork([from |-> from, to |-> to, msg |-> msg])
    /\ nextMsgToSend' = nextMsgToSend + 1
    /\ UNCHANGED <<messagesProcessed>>
    
SendMsgAction ==  
    \E i, j \in Server: 
        /\ i /= j
        /\ SendMsg(i, j, nextMsgToSend) 
    
ReceiveMsg(server, msg) ==
    /\ messagesProcessed' = [messagesProcessed EXCEPT ![server] = Append(messagesProcessed[server], msg.msg)]
    /\ UNCHANGED <<nextMsgToSend, network>>
    
ReceiveMsgAction == 
    \E i \in Server: 
    \E msg \in network: msg.to = i 
    /\ ReceiveMsg(i, msg)
    
----
\* Invariants

\****** NEW STUFF ********
\* Expected to fail!!!
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

----
\* Spec

\* Define initial values for all variables
Init == 
    /\ network = {}
    /\ messagesProcessed = [s \in Server |-> <<>>] 
    /\ nextMsgToSend = 0
    
Next ==
   \/ SendMsgAction
   \/ ReceiveMsgAction

=============================================================================
\* Modification History
\* Last modified Fri May 15 11:19:32 EDT 2020 by matthewsaltz
\* Created Wed May 06 19:34:45 EDT 2020 by matthewsaltz
