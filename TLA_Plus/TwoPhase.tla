------------------------------ MODULE TwoPhase ------------------------------
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]

TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages
            
TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ msgs = {}
          /\ tmPrepared = {}
          
TMRcvPrepared(r) == /\ tmState = "init"
                     /\ [type|-> "Prepared", rm|-> r ] \in msgs
                     /\ tmPrepared' = tmPrepared \cup {r}
                     /\ UNCHANGED<<rmState, tmState, msgs>>
                     
TMCommit == /\ tmState = "init"
            /\ tmPrepared = RM
            /\ tmState' = "done"
            /\ msgs' = msgs \cup {[type|-> "Commit"]}
            /\ UNCHANGED<<rmState, tmPrepared>>
            
TMAbort == /\ tmState = "init"
           /\ tmState' = "done"
           /\ msgs' = msgs \cup {[type |-> "Abort"]}
           /\ UNCHANGED<<rmState, tmPrepared>>
           
RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r]= "prepared"] 
                /\ msgs' = msgs \cup {[type|->"Prepared", rm |-> r]}
                /\ UNCHANGED<<tmState, tmPrepared>>
                
RMChooseToAbort(r) == /\ rmState[r] = "working"
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED<<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) == /\ [type|->"Commit"] \in msgs
                     /\ rmState[r] = "prepared"
                     /\ rmState' = [rmState EXCEPT ![r]="committed"]
                     /\ UNCHANGED<<tmState, tmPrepared, msgs>>
                     
RMRcvAbortMsg(r) == /\ [type |-> "Abort"] \in msgs
                    /\ rmState[r] \in {"prepared", "working"}
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                    /\ UNCHANGED<<tmState, tmPrepared, msgs>>
                    
TPNext == \/ TMCommit \/ TMAbort
          \/ \E r \in RM :  
                TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
                    \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
                    
TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>

THEOREM TPSpec => []TPTypeOK

INSTANCE TCommit 

THEOREM TPSpec => TCSpec
              
=============================================================================
\* Modification History
\* Last modified Mon Apr 09 17:08:31 CST 2018 by 10077668
\* Created Mon Apr 09 14:43:33 CST 2018 by 10077668
