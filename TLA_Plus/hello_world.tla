---------------------------- MODULE hello_world ----------------------------

EXTENDS TLC

(***************************************************************************

--algorithm HelloWorld
{   
    {
        print "hello world"
    }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT("hello world")
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Mar 09 11:19:14 CST 2018 by 10077668
\* Created Fri Mar 09 09:25:19 CST 2018 by 10077668
