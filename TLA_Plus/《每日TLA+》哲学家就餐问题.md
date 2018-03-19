# 《每日TLA+》哲学家就餐问题

## 问题描述
假设有五位哲学家围坐在一张圆形餐桌旁，做以下两件事情之一：吃饭，或者思考。吃东西的时候，他们就停止思考，思考的时候也停止吃东西。餐桌中间有一大碗意大利面，每两个哲学家之间有一只餐叉。因为用一只餐叉很难吃到意大利面，所以假设哲学家必须用两只餐叉吃东西。他们只能使用自己左右手边的那两只餐叉。

哲学家就餐问题的演示
哲学家从来不交谈，这就很危险，可能产生死锁，每个哲学家都拿着左手的餐叉，永远都在等右边的餐叉（或者相反）。

即使没有死锁，也有可能发生资源耗尽。例如，假设规定当哲学家等待另一只餐叉超过五分钟后就放下自己手里的那一只餐叉，并且再等五分钟后进行下一次尝试。这个策略消除了死锁（系统总会进入到下一个状态），但仍然有可能发生“活锁”。如果五位哲学家在完全相同的时刻进入餐厅，并同时拿起左边的餐叉，那么这些哲学家就会等待五分钟，同时放下手中的餐叉，再等五分钟，又同时拿起这些餐叉。

在实际的计算机问题中，缺乏餐叉可以类比为缺乏共享资源。一种常用的计算机技术是资源加锁，用来保证在某个时刻，资源只能被一个程序或一段代码访问。当一个程序想要使用的资源已经被另一个程序锁定，它就等待资源解锁。当多个程序涉及到加锁的资源时，在某些情况下就有可能发生死锁。例如，某个程序需要访问两个文件，当两个这样的程序各锁了一个文件，那它们都在等待对方解锁另一个文件，而这永远不会发生。

## TLA+实现


```
---------------------------- MODULE philosophers ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumPhilosophers, NULL
ASSUME NumPhilosophers > 0
NP == NumPhilosophers

(* --algorithm dining_philosophers {

variables forks = [fork \in 1..NP |-> NULL]

define
{
  LeftFork(p) == p
  RightFork(p) == IF p = NP THEN 1 ELSE p + 1

  HeldForks(p) ==
    { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

  AvailableForks(p) ==
    { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}
};

macro set_fork(fork, val)
{
    forks[fork] := val;
}

macro take_a_fork()
{
    with(fork \in AvailableForks(self))
    {
        set_fork(fork, self);
    };
}

macro drop_a_fork()
{
    await AvailableForks(self) = {};
    with(fork \in HeldForks(self))
    {
        set_fork(fork, NULL);
    };
}

procedure attempt_eat()
{
Eat:
    if(Cardinality(HeldForks(self)) = 2) 
    {
        hungry := FALSE;
        forks[LeftFork(self)] := NULL ||
            forks[RightFork(self)] := NULL;
    }
}

process(philosopher \in 1..NP)
variables hungry = TRUE;
{
P:
    while(hungry)
    {
        either
        {
            take_a_fork();
        }
        or
        {
            drop_a_fork();
        };
        call attempt_eat();
    };
}
} *)


\* BEGIN TRANSLATION
VARIABLES forks, pc, stack

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}

VARIABLE hungry

vars == << forks, pc, stack, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        (* Process philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P"]

Eat(self) == /\ pc[self] = "Eat"
             /\ IF Cardinality(HeldForks(self)) = 2
                   THEN /\ hungry' = [hungry EXCEPT ![self] = FALSE]
                        /\ forks' = [forks EXCEPT ![LeftFork(self)] = NULL,
                                                  ![RightFork(self)] = NULL]
                   ELSE /\ TRUE
                        /\ UNCHANGED << forks, hungry >>
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ stack' = stack

attempt_eat(self) == Eat(self)

P(self) == /\ pc[self] = "P"
           /\ IF hungry[self]
                 THEN /\ \/ /\ \E fork \in AvailableForks(self):
                                 forks' = [forks EXCEPT ![fork] = self]
                         \/ /\ AvailableForks(self) = {}
                            /\ \E fork \in HeldForks(self):
                                 forks' = [forks EXCEPT ![fork] = NULL]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "attempt_eat",
                                                               pc        |->  "P" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "Eat"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << forks, stack >>
           /\ UNCHANGED hungry

philosopher(self) == P(self)

Next == (\E self \in ProcSet: attempt_eat(self))
           \/ (\E self \in 1..NP: philosopher(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Mar 19 21:44:38 CST 2018 by zhangye
\* Created Mon Mar 19 20:47:18 CST 2018 by zhangye

```

