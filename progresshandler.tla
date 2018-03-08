-------------------------- MODULE progresshandler --------------------------
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
