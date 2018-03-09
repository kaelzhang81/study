--------------------------- MODULE RaceCondition ---------------------------
\*https://satyasm.github.io/design/tla/model/2017/12/02/design-tla.html
EXTENDS Integers

CONSTANTS N

(***************************************************************************

--algorithm RaceCondition
{
    variable total = 0;
    
    process (Proc \in 1..N)
        variable x;
    {
read:
        x := total;
inc:    
        x := x + 1;
save:
        total := x;
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES total, pc, x

vars == << total, pc, x >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ total = 0
        (* Process Proc *)
        /\ x = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "read"]

read(self) == /\ pc[self] = "read"
              /\ x' = [x EXCEPT ![self] = total]
              /\ pc' = [pc EXCEPT ![self] = "inc"]
              /\ total' = total

inc(self) == /\ pc[self] = "inc"
             /\ x' = [x EXCEPT ![self] = x[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "save"]
             /\ total' = total

save(self) == /\ pc[self] = "save"
              /\ total' = x[self]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ x' = x

Proc(self) == read(self) \/ inc(self) \/ save(self)

Next == (\E self \in 1..N: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AlgoOK == (\A self \in ProcSet : pc[self] = "Done") => total = N

=============================================================================
\* Modification History
\* Last modified Fri Mar 09 12:00:10 CST 2018 by 10077668
\* Created Fri Mar 09 11:44:09 CST 2018 by 10077668
