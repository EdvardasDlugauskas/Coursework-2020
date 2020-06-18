--------------------------- MODULE RaftHeartbeat ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Is leader ALIVE or CRASHED
VARIABLE leaderState 

\* A collection of heartbeat (AppendEntries) messages the leader has sent.
\* A single message is abstracted to represent the leader's index 
VARIABLE messages

\* A representation of the commitIndex and term, leader increases index monotonically.
VARIABLE leaderIndex
VARIABLE followerIndex
nodeIndexes == << leaderIndex, followerIndex >>

\* Indicates whether the follower timed out after not hearing from 
\* the leader for the specified amount of time.
VARIABLE isTimeout

vars == << leaderState, messages, nodeIndexes, isTimeout >>
    
\* The leader crashes and doesn't recover
CrashLeader ==
        /\ leaderState = "ALIVE" 
        /\ leaderState' = "CRASHED" 
        /\ UNCHANGED <<messages, nodeIndexes, isTimeout>>
         
\* The leader sends the follower an AppendEntries message
SendMessage == 
        /\ leaderState = "ALIVE"
        /\ messages' = Append(messages, leaderIndex)
        /\ UNCHANGED <<leaderState, nodeIndexes, isTimeout>>

\* Helper function to remove a message from a sequence of messages
RemoveMessage(i, seq) ==
    [j \in 1 .. Len(seq) - 1 |-> IF j < i THEN seq[j] ELSE seq[j+1]]
    
\* The network drops a message
DropMessage == 
        /\ Len(messages) >= 1
        /\ \E i \in 1 .. Len(messages): 
            messages' = RemoveMessage(i, messages)
        /\ UNCHANGED <<leaderState, nodeIndexes, isTimeout>>

\* The leader increments its index
IncrementIndex ==
        /\ leaderState = "ALIVE"
        /\ leaderIndex' = leaderIndex + 1
        /\ UNCHANGED <<leaderState, messages, followerIndex, isTimeout>>

\* The follower receives a message from the leader.
ReceiveMessage == 
        /\ Len(messages) >= 1
        /\ \E i \in 1 .. Len(messages):
            ((LET message == messages[i]
            IN followerIndex' = IF message > followerIndex 
                                THEN message
                                ELSE followerIndex)
            /\ messages' = RemoveMessage(i, messages))
        /\ UNCHANGED <<leaderState, leaderIndex, isTimeout>>

\* The follower times out
Timeout == isTimeout' = TRUE
        /\ UNCHANGED <<leaderState, messages, nodeIndexes>>

\* Initial state of model
Init == /\ leaderState = "ALIVE"
        /\ messages = << >>
        /\ leaderIndex = 0
        /\ followerIndex = 0
        /\ isTimeout = FALSE
        
\* Next state function
Next == \/ SendMessage
        \/ IncrementIndex
        \/ DropMessage
        \/ ReceiveMessage
        \/ CrashLeader
        \/ Timeout

Spec == Init /\[][Next]_vars /\ WF_vars(Next)

\* Invariant that helps make sure we haven't stepped out of bounds
TypeOK == /\ leaderState \in {"ALIVE", "CRASHED"}
          /\ messages \in Seq(Nat)
          /\ leaderIndex \in Nat
          /\ followerIndex \in Nat      
          /\ isTimeout \in BOOLEAN


\* Properties of the system

LeaderFailureDetected == leaderState = "CRASHED" ~> isTimeout = TRUE

THEOREM Correctness == Spec => []LeaderFailureDetected


=============================================================================
