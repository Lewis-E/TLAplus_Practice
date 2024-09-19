--------------------------- MODULE MayhemMandril ---------------------------
EXTENDS Naturals, Sequences
(* 
An attempt to model the MayhemMandril from https://www.roguelynn.com/words/asyncio-we-did-it-wrong/
*)

CONSTANT 
    NumberOfPublishedMessages, \* How many message ids to generate in the model
    SetOfQueueIds, \* Queues to create in the model -- e.g. {"Queue1", "Queue2"}
    SetOfMayhemServerIds, \* Mayhem Servers to create in the model -- e.g. {"Mayhem1"}
    UNSET \* Model Value

VARIABLES
    QueueState,
    MayhemServerState,
    OperationsLog

vars == <<QueueState, MayhemServerState, OperationsLog>>

\* Parameterized number of messages to 'publish' in the queue.
SetOfMessageIds == 1..NumberOfPublishedMessages 
ServerMessageIdValues == SetOfMessageIds \union {UNSET} \* A server may have a message or may have no message (unset).

\* A queue can contain some set of message ids or be empty.
QueueStateInvariant == QueueState \subseteq SetOfMessageIds \/ QueueState = {UNSET}

\* The mayhem server is always doing an action (state) to a message or no message (unset).
MayhemStateVal == [
    state: {
        "Waiting", 
        "ReadingFromQueue", 
        "Processing", 
        "CleaingUpMessage", 
        "Off"
    },
    message: ServerMessageIdValues
]
MayhemServerStateInvariant == MayhemServerState \in [SetOfMayhemServerIds -> MayhemStateVal]

\* The Operations Log records a Queue or Mayhem Server action
OperationsLogVal == [
    type: {"Publish", "Read", "Process", "CleanUp", "ShutDownMayhem", "StartMayhem"},
    message: ServerMessageIdValues
]
OperationsLogInvariant == OperationsLog \in Seq(OperationsLogVal)

(*
The full type definition for our variables, to be verified by the model. 
*)
TypeInvariant == MayhemServerStateInvariant /\ QueueStateInvariant /\ OperationsLogInvariant

(**)
(* Model Starts Here *)
(**)

Init == 
    /\ QueueState = [queueId \in SetOfQueueIds |-> UNSET]
    /\ MayhemServerState = [mayhemServerId \in SetOfMayhemServerIds |-> [
            state |-> "Waiting",
            message |-> UNSET
        ]]
    /\ OperationsLog = <<>>
    
=============================================================================
\* Modification History
\* Last modified Thu Sep 19 15:56:30 EDT 2024 by lewis
\* Created Thu Sep 19 13:35:35 EDT 2024 by lewis
