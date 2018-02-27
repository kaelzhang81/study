安全性(safety)是程序在执行期间不会出现异常的结果.对于顺序程序指其最终状态是正确的.对于并发程序指保证共享变量的互斥访问和无死锁出现
活性(liveness)是程序能按预期完成它的工作.对于顺序程序指程序能正常终止.对于并发程序指每个进程能得到它所要求的服务; 或进程总能进入临界段; 或送出的消息总能到达目的进程, 活性深深受到执行机构调度策略的影响
公平性(fairness)指在有限进展的假设下没有一个进程处于死等状态.
    无条件公平性:调度策略如能保证每个无条件的原子功能均能执行
    弱公平性:在具有条件原子动作时, 若条件原子动作能执行并依然保持无条件公平性, 则为弱公平性(Weak fairness says that when an action is (continuously)  enabled, the action will be (eventually) executed. )
    强公平性:条件原子动作一定能执行, 则为强公平性(Strong fairness relaxes the assumption that the action needs to be continuously enabled to be applied. Instead, it requires it to be enabled infinitely often (possible with intervals where it is not enabled).)

strong fairness => weak fairness

weak fairness:
<>[] Enabled (A) ->  []<> A

strong fairness:
[]<> Enabled (A) -> []<> A


F(<>) G([]) says that there is a point in the future from which the action will always be enabled, and G F says that the action will be enabled an infinite number of times (but not necessarily continuously).---F G表示未来有一点可以始终启用动作，G F表示动作将启用无限次（但不一定连续）。