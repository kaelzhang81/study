-------------------------- MODULE progresshandler --------------------------
\*https://andy.hammerhartes.de/finding-bugs-in-systems-through-formalization.html
EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT N, Quorum
ASSUME N \in Nat /\ N > 0
ASSUME Quorum < N
Nodes == 1..N

(***************************************************************************
--algorithm progresshandler 
{
variable 
  \* The progress set of each Cassandra node
  progress = [n \in Nodes |-> {}],
  \* Message queue
  queue = <<"first step", "second step">>,
  \* How many progress handlers have seen the switch from unprocessed to processed
  switchHappened = 0,
  \* The number of unacknowledged messages
  unacked = 0;
    
define
{
  \* Whether the given set of statuses is considered "processing complete"
  ProcessingComplete(p) == p = {"first step", "second step"}
  \* Reads the progress set from the given nodes
  ReadProgress(nodes) == UNION {progress[n] : n \in nodes}
  \* Returs a set with all subsets of nodes with the given cardinality
  NNodes(n) == {x \in SUBSET Nodes : Cardinality(x) = n}
}

\* Receive a message from the queue
macro recv(queue, receiver)
{
    await queue # <<>>;
    receiver := Head(queue);
    queue := Tail(queue);
    print queue;
}

\* Appends status to the progress set at Quorum nodes
procedure appendProgress(writeNodes, status)
variable nodes = writeNodes;
{
p0: while(nodes # {})
    {
p1:     with(n \in nodes)
        {
            progress[n] := progress[n] \union status;
            nodes := nodes \ n;
            print progress[n];
        }
    };
    return;
}

\* Handles a progress message from the queue
fair process(progressHandler \in {"handler1", "handler2"})
variable 
    writeQuorumNodes \in NNodes(Quorum),
    readQuorumNodes \in NNodes(Quorum),
    secondReadQuorumNodes \in NNodes(Quorum),
    completedBefore = FALSE,
    message = "";
{
P0:    
    while(TRUE)
    {
Poll:
        recv(queue, message);
        unacked := unacked + 1;
Read:
        completedBefore := ProcessingComplete(ReadProgress(readQuorumNodes));
Write:
        call appendProgress(writeQuorumNodes, message);
ReadAfterWrite:
        if(~completedBefore /\ ProcessingComplete(ReadProgress(secondReadQuorumNodes)))
        {
            \* The real progress handler would trigger some action here
            switchHappened := switchHappened + 1;
        }
    };
Ack:
    unacked := unacked - 1;
}

}

 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES progress, queue, switchHappened, unacked, pc, stack

(* define statement *)
ProcessingComplete(p) == p = {"first step", "second step"}

ReadProgress(nodes) == UNION {progress[n] : n \in nodes}

NNodes(n) == {x \in SUBSET Nodes : Cardinality(x) = n}

VARIABLES writeNodes, status, nodes, writeQuorumNodes, readQuorumNodes, 
          secondReadQuorumNodes, completedBefore, message

vars == << progress, queue, switchHappened, unacked, pc, stack, writeNodes, 
           status, nodes, writeQuorumNodes, readQuorumNodes, 
           secondReadQuorumNodes, completedBefore, message >>

ProcSet == ({"handler1", "handler2"})

Init == (* Global variables *)
        /\ progress = [n \in Nodes |-> {}]
        /\ queue = <<"first step", "second step">>
        /\ switchHappened = 0
        /\ unacked = 0
        (* Procedure appendProgress *)
        /\ writeNodes = [ self \in ProcSet |-> defaultInitValue]
        /\ status = [ self \in ProcSet |-> defaultInitValue]
        /\ nodes = [ self \in ProcSet |-> writeNodes[self]]
        (* Process progressHandler *)
        /\ writeQuorumNodes \in [{"handler1", "handler2"} -> NNodes(Quorum)]
        /\ readQuorumNodes \in [{"handler1", "handler2"} -> NNodes(Quorum)]
        /\ secondReadQuorumNodes \in [{"handler1", "handler2"} -> NNodes(Quorum)]
        /\ completedBefore = [self \in {"handler1", "handler2"} |-> FALSE]
        /\ message = [self \in {"handler1", "handler2"} |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P0"]

p0(self) == /\ pc[self] = "p0"
            /\ IF nodes[self] # {}
                  THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                       /\ UNCHANGED << stack, writeNodes, status, nodes >>
                  ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ nodes' = [nodes EXCEPT ![self] = Head(stack[self]).nodes]
                       /\ writeNodes' = [writeNodes EXCEPT ![self] = Head(stack[self]).writeNodes]
                       /\ status' = [status EXCEPT ![self] = Head(stack[self]).status]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << progress, queue, switchHappened, unacked, 
                            writeQuorumNodes, readQuorumNodes, 
                            secondReadQuorumNodes, completedBefore, message >>

p1(self) == /\ pc[self] = "p1"
            /\ \E n \in nodes[self]:
                 /\ progress' = [progress EXCEPT ![n] = progress[n] \union status[self]]
                 /\ nodes' = [nodes EXCEPT ![self] = nodes[self] \ n]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << queue, switchHappened, unacked, stack, writeNodes, 
                            status, writeQuorumNodes, readQuorumNodes, 
                            secondReadQuorumNodes, completedBefore, message >>

appendProgress(self) == p0(self) \/ p1(self)

P0(self) == /\ pc[self] = "P0"
            /\ pc' = [pc EXCEPT ![self] = "Poll"]
            /\ UNCHANGED << progress, queue, switchHappened, unacked, stack, 
                            writeNodes, status, nodes, writeQuorumNodes, 
                            readQuorumNodes, secondReadQuorumNodes, 
                            completedBefore, message >>

Poll(self) == /\ pc[self] = "Poll"
              /\ queue # <<>>
              /\ message' = [message EXCEPT ![self] = Head(queue)]
              /\ queue' = Tail(queue)
              /\ PrintT(queue')
              /\ unacked' = unacked + 1
              /\ pc' = [pc EXCEPT ![self] = "Read"]
              /\ UNCHANGED << progress, switchHappened, stack, writeNodes, 
                              status, nodes, writeQuorumNodes, readQuorumNodes, 
                              secondReadQuorumNodes, completedBefore >>

Read(self) == /\ pc[self] = "Read"
              /\ completedBefore' = [completedBefore EXCEPT ![self] = ProcessingComplete(ReadProgress(readQuorumNodes[self]))]
              /\ pc' = [pc EXCEPT ![self] = "Write"]
              /\ UNCHANGED << progress, queue, switchHappened, unacked, stack, 
                              writeNodes, status, nodes, writeQuorumNodes, 
                              readQuorumNodes, secondReadQuorumNodes, message >>

Write(self) == /\ pc[self] = "Write"
               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "appendProgress",
                                                           pc        |->  "ReadAfterWrite",
                                                           nodes     |->  nodes[self],
                                                           writeNodes |->  writeNodes[self],
                                                           status    |->  status[self] ] >>
                                                       \o stack[self]]
                  /\ status' = [status EXCEPT ![self] = message[self]]
                  /\ writeNodes' = [writeNodes EXCEPT ![self] = writeQuorumNodes[self]]
               /\ nodes' = [nodes EXCEPT ![self] = writeNodes'[self]]
               /\ pc' = [pc EXCEPT ![self] = "p0"]
               /\ UNCHANGED << progress, queue, switchHappened, unacked, 
                               writeQuorumNodes, readQuorumNodes, 
                               secondReadQuorumNodes, completedBefore, message >>

ReadAfterWrite(self) == /\ pc[self] = "ReadAfterWrite"
                        /\ IF ~completedBefore[self] /\ ProcessingComplete(ReadProgress(secondReadQuorumNodes[self]))
                              THEN /\ switchHappened' = switchHappened + 1
                              ELSE /\ TRUE
                                   /\ UNCHANGED switchHappened
                        /\ pc' = [pc EXCEPT ![self] = "P0"]
                        /\ UNCHANGED << progress, queue, unacked, stack, 
                                        writeNodes, status, nodes, 
                                        writeQuorumNodes, readQuorumNodes, 
                                        secondReadQuorumNodes, completedBefore, 
                                        message >>

Ack(self) == /\ pc[self] = "Ack"
             /\ unacked' = unacked - 1
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << progress, queue, switchHappened, stack, 
                             writeNodes, status, nodes, writeQuorumNodes, 
                             readQuorumNodes, secondReadQuorumNodes, 
                             completedBefore, message >>

progressHandler(self) == P0(self) \/ Poll(self) \/ Read(self)
                            \/ Write(self) \/ ReadAfterWrite(self)
                            \/ Ack(self)

Next == (\E self \in ProcSet: appendProgress(self))
           \/ (\E self \in {"handler1", "handler2"}: progressHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"handler1", "handler2"} : WF_vars(progressHandler(self)) /\ WF_vars(appendProgress(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Correctness == \/ queue # <<>>
               \/ unacked > 0
               \/ switchHappened > 0
Liveness == <>[](switchHappened > 0)
NoDupAck == unacked >= 0
\* Note that this cannot be guaranteed with the current implementation
NoDupSwitch == switchHappened <= 1

=============================================================================
\* Modification History
\* Last modified Thu Mar 08 14:48:59 CST 2018 by 10077668
\* Created Thu Mar 08 09:30:24 CST 2018 by 10077668
