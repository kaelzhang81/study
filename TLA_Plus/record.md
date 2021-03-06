安全性(safety)是程序在执行期间不会出现异常的结果（**正确性**）.对于顺序程序指其最终状态是正确的.对于并发程序指保证共享变量的互斥访问和无死锁出现

活性(liveness)是程序能按预期完成它的工作.对于顺序程序指程序能**正常终止**.对于并发程序指每个进程能得到它所要求的服务; 或进程**总能进入临界段(不会死锁)**; 或送出的**消息总能到达目的进程**, 活性深深受到执行机构调度策略的影响

公平性(fairness)指在有限进展的假设下没有一个进程处于死等状态.
    无条件公平性:调度策略如能保证每个无条件的原子功能均能执行
    弱公平性:在具有条件原子动作时, 若条件原子动作能执行并依然保持无条件公平性, 则为弱公平性(Weak fairness says that when an action is (continuously)  enabled, the action will be (eventually) executed. )
    通俗解释：如果一个步骤一直是enable的但是一直没发生，那么它违反了weakness fairness。一直满足晋级条件，但是一直升不上去，不公平啊。
    例如：x=1,x'=x+1: “1,1......1,1,1,1,1,1,1,1,1”就是没有x为2
    （在所有状态点上）要么不可能，要么执行
    
  强公平性:条件原子动作一定能执行, 则为强公平性(Strong fairness relaxes the assumption that the action needs to be continuously enabled to be applied. Instead, it requires it to be enabled infinitely often (possible with intervals where it is not enabled).)
    通俗解释：无穷多个点是合格的，但是就是不能晋升。
    例如：x=1,x'=x+1: “1,2......1,2,1,1,1,2,1,1,2”
    （在所有状态点上）要么永远不可能，要么执行

strong fairness => weak fairness

weak fairness:
<>[] Enabled (A) ->  []<> A

strong fairness:
[]<> Enabled (A) -> []<> A


F(<>) G([]) says that there is a point in the future from which the action will always be enabled, and G F says that the action will be enabled an infinite number of times (but not necessarily continuously).---F G表示未来有一点可以始终启用动作，G F表示动作将启用无限次（但不一定连续）。


在TLA+中，使用fairness来代替liveness以避免liveness对safty的潜在错误改变。TLA+中一般为weak fairness。strong和weak是用来修饰fairness的，weak条件更苛刻也就更不公平。

坏的事情不发生，不代表好的事情会发生。

# Partial correctness & Total correctness
Example:
y:=1;
while ¬(x=1) do
    (y:=y ⋆ x; x:=x−1)
    
Partial correctness: if initially x has the
value n and **if the program terminates then
the final value of y is n!**

Total correctness: if initially x has the value
n then **the program terminates and the fi-
nal value of y is n!**


## 蕴含
(x=2) => (x+1=3)
(x=2) => (x=2)\/(x>7)

F=>G == ~F\/G


https://news.ycombinator.com/item?id=14221848

https://arxiv.org/pdf/1603.03599.pdf

https://medium.com/espark-engineering-blog/formal-methods-in-practice-8f20d72bce4f

https://www.hillelwayne.com/post/modeling-deployments/

https://news.ycombinator.com/item?id=8902739

https://news.cnblogs.com/n/579998/#comment

http://wenchao.wang/2017/11/20/%E8%81%8A%E8%81%8A-Formal-Specification-%E4%BB%8E-TLA-%E8%AE%B2%E8%B5%B7/
