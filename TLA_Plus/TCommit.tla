------------------------------ MODULE TCommit ------------------------------
CONSTANT RM

VARIABLE rmState

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM: rmState[r] # "committed"

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
         
DecideC(r) == /\ rmState[r] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
              
DecideA(r) == /\ rmState[r] \in {"working", "prepared"}
              /\ notCommitted
              /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
              
TCNext == \E r \in RM: Prepare(r) \/ DecideA(r) \/ DecideC(r)

          
TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent == \A r1, r2 \in RM: ~ /\ rmState[r1] = "commited"
                                    /\ rmState[r2] = "aborted"
                                    
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)

=============================================================================
\* Modification History
\* Last modified Mon Apr 09 11:41:40 CST 2018 by 10077668
\* Created Mon Apr 09 09:08:19 CST 2018 by 10077668
