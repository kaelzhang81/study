The final issue is the well known problem of state space explosion. Just modeling a small OpenComRTOS application, the TLC model checkers has to examine a few million states, exponentially taking more time for every task added to the model. This also requires increasing amounts of memory and limits the model checking to subsets of the whole architecture. However, this was not a real issue as the architecture is generic and based on a message passing protocol that is independent of the size of the system. The algorithmic logic of the RTOS kernel also makes no difference between local or remote services, making it independent of the topology of the target network and hence there was no need to make the network topology explicit.

A thin boundary between past experience, creativity and model checking

For completeness, we need to mention that some of the elements of the OpenComRTOS architecture were inherited from a previous distributed RTOS (Virtuoso [4]) that was developed in a traditional way, and with some inspiration from CSP. The communication layer of this distributed RTOS used packets but the kernel was a large jump table. We had also experienced issues with portability and scalability. Finally, the third generation of the Virtuoso RTOS was loosing performance through what we can call “feature bloating”. Nevertheless, it was difficult to see how a better architecture could be found that would at the same time provide improvements in terms of code size, safety, security and scalability properties. In addition we defined as objective that it should be able to run from memory restricted multi-core CPUs to widely distributed processing nodes running legacy software.

Formal modeling has helped a lot in formalizing the problem and as a result we can claim success beyond initial expectations.

# Novelties in the architecture

OpenComRTOS has a semantically layered architecture. At the lowest level (L0) the minimum set of entities provides everything that is needed to build a small networked real-time application.

The entities needed are Tasks (having a private function and workspace), an interaction entity we called an L0_Port to synchronize and communicate between the Tasks. Ports act like channels in the tradition of Hoare’s CSP but allow multiple waiters and asynchronous communication. One of the tasks is a kernel task scheduling the tasks in order of priority and managing and providing Port based services. Driver tasks handle inter-node communication. Pre-allocated as well as dynamically allocated packets are used as a carrier for all activities in the RTOS such as: service requests to the kernel, Port synchronization, datacommunication, etc. Each Packet has a fixed size header and data payload with a user defined but global data size. This significantly simplifies the management of the Packets, in particular at the communication layer. A router function also transparently forwards packets in order of priority between the nodes in a network.

OpenComRTOS L0 therefore is a distributed, scalable and network-centric operating systems consisting of a packet-switching communication layer with a scheduler and portbased synchronization. This architecture has proven to be very efficient. E.g. a minimum single processor kernel can have a code size of less than 1 Kbyte, with 2 Kbytes for the multi-processor version.

In the next semantic level (L1) services and entities were added as found in most RTOS: Boolean events, counting semaphores, FIFO queues, resources, memory pools, mailboxes, etc. The formal modeling has allowed defining all such entities as semantic variants of a common and generic entity type. We called this generic entity a “Hub”. In addition, the formal modeling also helped to define “clean” semantics for such services whereas ad-hoc implementations often have side-effects.

As the use of a single generic entity allowed a much greater reuse of code, the resulting code size is about 10 times less than for an RTOS with a more traditional architecture. One could of course remove all such application-oriented services and just use the Hub based services. This has however the drawback that the services loose their specific semantic richness. E.g. resource locking clearly expresses that the task enters a critical section in competition with other tasks. Also erroneous runtime conditions like raising an event twice (with loss of the previous event) are easier to detect at the application level than when using a generic Hub.

An unexpected side-effect of the use of Hub entities, is that the set of services can be expanded independently of the kernel itself. A Hub is a generic synchronization entity and the Hub semantics are determined by the synchronization predicate and by the predicate function following successful synchronization. The result is not only that the RTOS can be made application specific, it also provides better performance and more safety as most of the services and the driver code execute in the application domain, leaving the essential RTOS functions to a small kernel function.

In the course of the formal modeling we also discovered weaknesses in the traditional way priority inheritance is implemented in most RTOS and we found a way to reduce the total blocking time. In single processor RTOS systems, this is less of an issue but in multi-processor systems, all nodes can originate service requests and resource locking is a distributed service. Hence the waiting lists can grow much longer and lower priority tasks can block higher priority ones while waiting for the resource. This was solved by postponing the resource assignment till the rescheduling moment.

Finally, by generalization, also memory allocation has been approached like a resource locking service. In combination with the Packet Pool, this opens new possibilities for a safe and secure management of memory. E.g. the OpenComRTOS architecture is free from buffer overflow by design.

# Results obtained on real execution targets

We shortly summarize the results obtained. Although fully written in ANSI-C (except for the task context switch), the kernel could be reduced to less than 1 Kbytes single processor and 2 Kbytes with multi-processor support (measured on a 16bit Melexis
microcontroller). A sample application with two tasks and one Port required just 1230 bytes of program memory and 226 bytes of data memory (static and dynamic). More information is available in [ 4].

# Formal verification

This project would have been incomplete if we had not attempted a formal verification of the source code. In the end this proved to be quite straightforward because the orthogonal and clean architecture allowed to check each service using a similar pattern. Following issues however must be mentioned:
- We did not find tools and methods that allowed to verify our asynchronous and concurrent design(inevitable for a RTOS) at the source code level. Tools only exist for static and synchronous programs [9][10]
- It was practically impossible but also unnecessary to verify the kernel as a whole. Hence we verified the algorithms for each service class independently. Given the orthogonality of protocol based architecture (by using packets), this is sufficient.
- The hardest part remained to find all properties to check for. A lot of these properties look rather trivial at first sight and our human brain has a tendency to overlook them. 
- The final issue is related to the programming in C itself. It is clear that this language is a major source of errors. Hence, some errors were found at the programming level that no formal verification would ever find.
- However, the fact that the formal modeling helped a lot in achieving such a clean and orthogonal architecture, verification as well as at the abstract level by using a formal model checker as well as at the language level was a lot easier, because the complexity is minimized and the code size is much smaller than comparable hand written code.

# Future developments and research

Above we already identified the need for the model checkers to detect the minimal critical sections. Another area of research is how to maintain consistency between the formal model and the implementation. This will require that the formal model can be used as a reference and requires that the source is generated rather than
written by the software engineer.

Future OpenComRTOS developments will focus on adding more safety and security properties to a SW/HW co-design pair of OpenComRTOS and processor. Formal modeling should contribute in identifying minimum architectures that still are providing safety and security in the resource constrained domain of deeply embedded systems.

Another area of interest is to find a better way to separate orthogonally the priority based scheduling from the logical behavior of the kernel entities. E.g. the use of priority inheritance support results in this code being mixed up in the manipulation of the data structures (e.g. to sort waiting lists). This makes the code more convoluted to read and understand while the impact is only on the timely behavior of the application.

# conclude
The OpenComRTOS project has shown that even for software domains often associated with ‘black art’ programming, formal modeling works very well. The resulting software is not only very robust and maintainable but also very performing in size and timings and inherently safer than standard implementation architectures. Its use however must be integrated with a global systems engineering approach as the process of incremental development and modeling is as important as using the formal model checker itself. The use of formal modeling has resulted in many improvements of the RTOS properties.

Formal modeling and formal verification have proven to be very powerful engineering tools and hence it can not be emphasized enough how many problems in the software world can be avoided by a systematic use from the very beginning.

# REFERENCES
1. OpenComRTOS architectural designdocument on www.OpenLicenseSociety.org
2. TLA+/TLC home page on http://research.microsoft.com/users/lamport/tla/tla.html
3. INCOSE www.incose.org
4. Open License Society www.OpenLicenseSociety.org
5. www.Melexis.com
6. www.verisoft.de
7. www.spin.org
8. www.misra.org
9. Bruno Blanchet, Patrick Cousot, Radhia Cousot, Jérôme Feret, Laurent Mauborgne, Antoine Miné, David Monniaux & Xavier Rival. Design and Implementation of a Special-Purpose Static Program Analyzer for Safety-Critical Real-Time Embedded Software, invited chapter. In The Essence of Computation: Complexity, Analysis, Transformation. Essays Dedicated to Neil D. Jones, T. Mogensen and D.A. Schmidt and I.H. Sudborough (Editors). Lecture Notes in Computer Science 2566, pp. 85—108, Springer. . http://www.astree.ens.fr/
10. Clarke, Edmund and Kroening, Daniel and Lerda, Flavio, A Tool for Checking {ANSI-C} Programs, Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2004), Springer http://www.cprover.org/cbmc/

