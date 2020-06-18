---------------------------- MODULE RaHeartbeat ----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Is leader ALIVE or CRASHED
VARIABLE leaderState 

\* Helper variable tracking the number of times the leader node has failed
VARIABLE nodedownIndex

\* A collection of 'nodedown' messages the leader has sent.
\* In Erlang, when a monitored node crashes, the 'nodedown' message is sent to the follower.
\* The value of a message is not a part of the implementation and 
\* represents the number of times the node has failed.
VARIABLE nodedownMessages

nodedownInfo == <<nodedownMessages, nodedownIndex>>

\* Heartbeat messages the leader has sent
\* The value of a message is not a part of the implementation and
\* represents the number of times a heartbeat message was sent.
VARIABLE heartbeatMessages

\* Helper variable tracking the number of sent heartbeat messages
VARIABLE heartbeatIndex

heartbeatInfo == <<heartbeatMessages, heartbeatIndex>>

\* Whether the follower timed out
VARIABLE isTimeout


vars == << leaderState, nodedownInfo, heartbeatInfo, isTimeout >>

\* The leader crashes and doesn't recover
CrashLeader ==
        /\ leaderState = "ALIVE" 
        /\ leaderState' = "CRASHED" 
\*        Erlang sends the NODEDOWN message if the leader was monitored
        /\ nodedownMessages' = Append(nodedownMessages, nodedownIndex)
        /\ nodedownIndex' = nodedownIndex + 1
        /\ UNCHANGED <<heartbeatInfo, isTimeout>>

\* Helper function to remove a message from a sequence of messages
RemoveMessage(i, seq) ==
    [j \in 1 .. Len(seq) - 1 |-> IF j < i THEN seq[j] ELSE seq[j+1]]
    
\* The network drops a heartbeat message
DropHeartbeat == 
        /\ Len(heartbeatMessages) > 0
        /\ \E i \in 1 .. Len(heartbeatMessages): 
            heartbeatMessages' = RemoveMessage(i, heartbeatMessages)
        /\ UNCHANGED <<leaderState, heartbeatIndex, nodedownInfo, isTimeout>>

\* The follower receives a heartbeat message from the leader.
ReceiveHeartbeat == 
        /\ Len(heartbeatMessages) > 0
        /\ \E i \in 1 .. Len(heartbeatMessages): 
            heartbeatMessages' = RemoveMessage(i, heartbeatMessages)
        /\ UNCHANGED <<leaderState, heartbeatIndex, nodedownInfo, isTimeout>>
    
\* The leader sends a heartbeat message to the follower.
SendHeartbeat == 
        /\ leaderState = "ALIVE"
        /\ heartbeatMessages' = Append(heartbeatMessages, heartbeatIndex)
        /\ heartbeatIndex' = heartbeatIndex + 1
        /\ UNCHANGED <<leaderState, nodedownInfo, isTimeout>>
        
\* The network drops a nodedown message.
DropNodedown == 
        /\ Len(nodedownMessages) > 0
        /\ \E i \in 1 .. Len(nodedownMessages): 
            nodedownMessages' = RemoveMessage(i, nodedownMessages)
        /\ UNCHANGED <<leaderState, nodedownIndex, heartbeatInfo, isTimeout>>

\* The follower receives a nodedown message from the leader which causes it time out immediately.
ReceiveNodedown == 
        /\ Len(nodedownMessages) > 0
        /\ \E i \in 1 .. Len(nodedownMessages): 
            nodedownMessages' = RemoveMessage(i, nodedownMessages)
        /\ isTimeout' = TRUE
        /\ UNCHANGED <<leaderState, nodedownIndex, heartbeatInfo>>
        
        
Timeout == 
        /\ isTimeout = FALSE
        /\ isTimeout' = TRUE
        /\ UNCHANGED <<leaderState, heartbeatInfo, nodedownInfo>>

\* Initial state of model
Init == /\ leaderState = "ALIVE"
        /\ nodedownIndex = 0
        /\ nodedownMessages = <<>>
        /\ heartbeatIndex = 0
        /\ heartbeatMessages = <<>>
        /\ isTimeout = FALSE
        
\* Next state function
Next == \/ DropHeartbeat
        \/ SendHeartbeat
        \/ ReceiveHeartbeat
        \/ DropNodedown
        \/ ReceiveNodedown
        \/ CrashLeader
        \/ Timeout

Spec == Init /\[][Next]_vars /\ WF_vars(Next)

\* Invariant that helps make sure we haven't stepped out of bounds
TypeOK == /\ leaderState \in {"ALIVE", "CRASHED"}
          /\ nodedownIndex \in Nat
          /\ nodedownMessages \in Seq(Nat)
          /\ heartbeatMessages \in Seq(Nat)
          /\ heartbeatIndex \in Nat
          /\ isTimeout \in BOOLEAN


\* Properties of the system

LeaderFailureDetected == leaderState = "CRASHED" ~> isTimeout = TRUE

THEOREM Correctness == Spec => []LeaderFailureDetected

=============================================================================