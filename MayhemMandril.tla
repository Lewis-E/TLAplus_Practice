--------------------------- MODULE MayhemMandril ---------------------------
EXTENDS Naturals, Sequences
(**)
(* An attempt to model the MayhemMandril from https://www.roguelynn.com/words/asyncio-we-did-it-wrong/ *)
(**)

CONSTANT 
    NumberOfPublishedMessages, \* How many message ids to generate in the model
    SetOfQueueIds, \* Message Queues to create in the model -- e.g. {"Queue1"}
    SetOfMayhemServerIds, \* Mayhem Servers to create in the model -- e.g. {"Mayhem1"}
    UNSET \* Model Value

VARIABLES
    QueueState, \* Sequence
    SetOfSeenMessages, \* Set
    MayhemServerState, \* Function?
    ProcessLabels, \* Function of processes values -> labels
    OperationsLog \* Sequence

vars == <<ProcessLabels, QueueState, SetOfSeenMessages, MayhemServerState, OperationsLog>>
ProcessSet == (SetOfQueueIds)

\* Parameterized number of messages to 'publish' in the queue.
SetOfMessageIds == 1..NumberOfPublishedMessages 
ServerMessageIdValues == SetOfMessageIds \union {UNSET} \* A server may have a message or may have no message (unset).

\* A queue can contain some set of message ids, including duplicates, or be empty. 
QueueStateInvariant == QueueState = <<>> \/ DOMAIN QueueState \subseteq SetOfMessageIds

\* Once a message has been acted on, the publisher no longer attempts to deliver it.
SeenMessagesInvariant == SetOfSeenMessages \subseteq SetOfMessageIds \/ SetOfSeenMessages = {}

\* The mayhem server is always doing an action (state) to a message or no message (unset).
MayhemStateVal == [
    state: {
        "Waiting", 
        "ReadingFromQueue", 
        "Processing", 
        "CleaingUpMessage", 
        "Off"
    },
    message: SetOfMessageIds \union {UNSET}
]
MayhemServerStateInvariant == MayhemServerState \in [SetOfMayhemServerIds -> MayhemStateVal]

\* The Operations Log records a Queue or Mayhem Server action
OperationsLogVal == [
    type: {"Publish", "Read", "Process", "CleanUp", "ShutDownMayhem", "StartMayhem"},
    message: ServerMessageIdValues
]
OperationsLogInvariant == OperationsLog \in Seq(OperationsLogVal)

\* The full type definition for our variables, to be verified by the model. 
TypeInvariant == 
    /\ MayhemServerStateInvariant 
    /\ QueueStateInvariant 
    /\ OperationsLogInvariant 
    /\ SeenMessagesInvariant

(**)
(* Additional Safety and Liveness Definitions *)
(**)

AllMessagesPublished == 
    \A messageId \in SetOfMessageIds:
        \E i \in 1..Len(OperationsLog):
            LET publishOp == OperationsLog[i] IN
                /\ publishOp.type = "Publish"
                /\ publishOp.message = messageId
AllMessagesConsumed == SetOfMessageIds \ SetOfSeenMessages = {}
            
PublishedMessagesAreConsumedInvariant == AllMessagesPublished => AllMessagesConsumed
Liveness == <>[](AllMessagesPublished /\ AllMessagesConsumed) 

(**)
(* Model Starts Here *)
(**)

Init == \* Set starting values for all vars
    /\ ProcessLabels = [self \in ProcessSet |-> "Publish"]
    /\ OperationsLog = <<>>
    /\ QueueState = <<>>
    /\ SetOfSeenMessages = {}
    /\ MayhemServerState = [mayhemServerId \in SetOfMayhemServerIds |-> [
            state |-> "Waiting",
            message |-> UNSET
        ]]

Publish(self) == 
    /\ ProcessLabels[self] = "Publish"
    /\ ProcessLabels' = [ProcessLabels EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<MayhemServerState>>
    /\ \E messageId \in SetOfMessageIds \ SetOfSeenMessages: 
        /\ OperationsLog' = Append(
            OperationsLog, 
            [
                type |-> "Publish",
                message |-> messageId
            ])
        /\ QueueState' = Append(QueueState, messageId)
        /\ SetOfSeenMessages' = SetOfSeenMessages \union {messageId} \* TODO replace this with the MayhemServer

Terminating == \A self \in ProcessSet: ProcessLabels[self] = "Done" /\ UNCHANGED vars

Next == (\E self \in SetOfQueueIds: Publish(self)) \/ Terminating

Spec == 
    /\ Init /\ [][Next]_vars
    \* Add fairness to processes
    /\ \A self \in SetOfQueueIds : WF_vars(Publish(self))

=============================================================================
\* Modification History
\* Last modified Fri Sep 20 18:06:15 EDT 2024 by lewis
\* Created Thu Sep 19 13:35:35 EDT 2024 by lewis
