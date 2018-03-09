------------------------- MODULE RaceConditionLock -------------------------
\*https://satyasm.github.io/design/tla/model/2017/12/02/design-tla.html
EXTENDS Integers

CONSTANTS N

(***************************************************************************

--algorithm RaceConditionLock
{
    variable 
        total = 0;
        isLocked = FALSE;
    
    
    macro Lock()
    {
        await isLocked = FALSE;
        isLocked := TRUE;
    };
    
    macro UnLock()
    {
        isLocked := FALSE;
    };
    
    process (Proc \in 1..N)
        variable x;
    {
lock:
        Lock();
read:
        x := total;
inc:    
        x := x + 1;
save:
        total := x;
unlock:
        UnLock();
    };
}

 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES total, isLocked, pc, x

vars == << total, isLocked, pc, x >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ total = 0
        /\ isLocked = FALSE
        (* Process Proc *)
        /\ x = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ isLocked = FALSE
              /\ isLocked' = TRUE
              /\ pc' = [pc EXCEPT ![self] = "read"]
              /\ UNCHANGED << total, x >>

read(self) == /\ pc[self] = "read"
              /\ x' = [x EXCEPT ![self] = total]
              /\ pc' = [pc EXCEPT ![self] = "inc"]
              /\ UNCHANGED << total, isLocked >>

inc(self) == /\ pc[self] = "inc"
             /\ x' = [x EXCEPT ![self] = x[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "save"]
             /\ UNCHANGED << total, isLocked >>

save(self) == /\ pc[self] = "save"
              /\ total' = x[self]
              /\ pc' = [pc EXCEPT ![self] = "unlock"]
              /\ UNCHANGED << isLocked, x >>

unlock(self) == /\ pc[self] = "unlock"
                /\ isLocked' = FALSE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << total, x >>

Proc(self) == lock(self) \/ read(self) \/ inc(self) \/ save(self)
                 \/ unlock(self)

Next == (\E self \in 1..N: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AlgoOK == (\A self \in ProcSet : pc[self] = "Done") => total = N

=============================================================================
\* Modification History
\* Last modified Fri Mar 09 12:08:02 CST 2018 by 10077668
\* Created Fri Mar 09 12:01:18 CST 2018 by 10077668
