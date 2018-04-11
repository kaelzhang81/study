---------------------------- MODULE PaxosCommit ----------------------------
EXTENDS Integers

Maximum(S) == IF S ={} THEN -1
                       ELSE CHOOSE n \in S :(\A m \in S : n >= m)

CONSTANTS RM, Acceptor, Majority, Ballot

ASSUME /\ Ballot \subseteq Nat
       /\ {0} \subseteq Ballot
       /\ Majority \subseteq SUBSET Acceptor
       /\ \A MS1, MS2 \in Majority: MS1 \cap MS2 # {}

\* Phase1a：LEADER-Phase1a(bal, rm)-init
\* phase1b：ACCEPTOR-phase1b(acc)-phase1a
\* phase2a：RM-RMPrepare(rm)-init、RM-RMChooseToAbort(rm)-init、LEADER-Phase2a(bal, rm)-phase1b
\* phase2b：ACCEPTOR-phase2b(acc)-phase2a
\* decided：LEADER-Decide-phase2b
Message == [type:{"phase1a"}, ins: RM, bal: Ballot \ {0}]
           \cup
           [type:{"phase1b"}, ins: RM, mbal: Ballot, bal: Ballot \cup {-1}, val: {"prepared", "aborted", "none"}, acc: Acceptor]
           \cup        
           [type:{"phase2a"}, ins: RM, bal: Ballot, val:{"prepared","aborted"}]
           \cup
           [type:{"phase2b"}, acc: Acceptor, ins: RM, bal: Ballot, val:{"prepared", "aborted"}]
           \cup
           [type:{"Commit", "Abort"}]
           
VARIABLES rmState, aState, msgs

PCTypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ aState \in [RM -> [Acceptor -> [mbal: Ballot, bal: Ballot \cup {-1}, val: {"prepared", "aborted", "none"}]]]
            /\ msgs \subseteq Message
            
PCInit == /\ rmState = [rm \in RM |-> "working"]
          /\ aState = [ins \in RM |-> [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
          /\ msgs = {}
          
Send(m) == msgs' = msgs \cup {m}

\**************                           
\* RM
\************** 
\*[type:{"phase2a"}, ins: RM, bal: Ballot, val:{"prepared","aborted"}]
RMPrepare(rm) == /\ rmState[rm] = "working"
                 /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
                 /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "prepared"])
                 /\ UNCHANGED<<aState>> 

\*[type:{"phase2a"}, ins: RM, bal: Ballot, val:{"prepared","aborted"}]               
RMChooseToAbort(rm) == /\ rmState[rm] = "working"
                       /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
                       /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "aborted"])
                       /\ UNCHANGED<<aState>>
                       
RMRcvCommitMsg(rm) == /\ [type |-> "Commit"] \in msgs
                      /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
                      /\ UNCHANGED<<aState, msgs>>
                      
RMRcvAbortMsg(rm) == /\ [type |-> "Abort"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
                     /\ UNCHANGED<<aState, msgs>>      

\**************                           
\* LEADER
\************** 
\*[type:{"phase1a"}, ins: RM, bal: Ballot \ {0}]                  
Phase1a(bal, rm) == /\ Send([type |-> "phase1a", ins |-> rm, bal |-> bal])
                    /\ UNCHANGED<<rmState, aState>>     
           
\*[type:{"phase2a"}, ins: RM, bal: Ballot, val:{"prepared","aborted"}]
Phase2a(bal, rm) == /\ ~ \E m \in msgs: /\ m.type = "phase2a"
                                        /\ m.bal = bal
                                        /\ m.ins = rm
                    /\ \E MS \in Majority:
                            LET mset == {m \in msgs: /\ m.type = "phase1b"
                                                     /\ m.ins = rm
                                                     /\ m.mbal = bal
                                                     /\ m.acc \in MS}
                                \*  Mu 代表所有编号为 u 的阶段 2b 消息集合
                                mu == Maximum({m.bal: m \in mset})
                                v == IF mu = -1 THEN "aborted"
                                                ELSE (CHOOSE m \in mset: m.bal = mu).val
                             IN /\ \A ac \in MS: \E m \in mset:m.acc = ac
                                /\ Send([type |-> "phase2a", ins |->rm, bal |-> bal, val |->v])
                     /\UNCHANGED<<rmState, aState>>
                     
                     
Decide == /\ LET Decided(rm, v) == \E b \in Ballot, MS \in Majority:
                                    \A ac \in MS: [type |-> "phase2b", ins |-> rm, bal |-> b, val |-> v, acc |-> ac] \in msgs
             IN \/ /\ \A rm \in RM: Decided(rm, "prepared")
                   /\ Send([type |-> "Commit"])
                \/ /\ \E rm \in RM: Decided(rm, "aborted")
                   /\ Send([type |-> "Abort"])
          /\ UNCHANGED<<rmState, aState>>
            
            
\**************                           
\* ACCEPTOR
\************** 
\* [type:{"phase1b"}, ins: RM, mbal: Ballot, bal: Ballot \cup {-1}, val: {"prepared", "aborted", "none"}, acc: Acceptor]
phase1b(acc) == \E m \in msgs: /\ m.type = "phase1a"
                               /\ aState[m.ins][acc].mbal < m.bal
                               /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
                               /\ Send([type |-> "phase1b", ins |-> m.ins, mbal |-> m.bal, 
                                        bal |-> aState[m.ins][acc].bal, val |-> aState[m.ins][acc].val,
                                        acc |-> acc])
                               /\ UNCHANGED<<rmState>>

\*[type:{"phase2b"}, acc: Acceptor, ins: RM, bal: Ballot, val:{"prepared", "aborted"}]
phase2b(acc) == /\ \E m \in msgs: /\ m.type = "phase2a"
                                  /\ aState[m.ins][acc].mbal <= m.bal
                                  /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                                            ![m.ins][acc].bal = m.bal,
                                                            ![m.ins][acc].val = m.val]
                                  /\ Send([type |-> "phase2b", acc |-> acc, ins |-> m.ins, 
                                           bal |-> m.bal, val |-> m.val])
                /\ UNCHANGED<<rmState>>


PCNext == \/ \E rm \in RM: \/ RMPrepare(rm)
                           \/ RMChooseToAbort(rm)
                           \/ RMRcvCommitMsg(rm)
                           \/ RMRcvAbortMsg(rm)
          \/ \E bal \in Ballot \ {0}, rm \in RM: \/ Phase1a(bal, rm)
                                                 \/ Phase2a(bal, rm)
          \/ Decide
          \/ \E acc \in Acceptor: \/ phase1b(acc)
                                  \/ phase2b(acc)
                                  
PCSpec == PCInit /\ [][PCNext]_<<rmState, aState, msgs>>

THEOREM PCSpec => []PCTypeOK

TC == INSTANCE TCommit

THEOREM PCSpec => TC!TCSpec
=============================================================================
\* Modification History
\* Last modified Wed Apr 11 15:50:19 CST 2018 by 10077668
\* Created Mon Apr 09 18:47:18 CST 2018 by 10077668
