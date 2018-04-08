# 形式化规范语言TLA+

## 基本定义

维基百科上对TLA+是这样定义的：

```
a formal specification language developed by Leslie Lamport. 
It is used to design, model, document, and verify concurrent systems. 

TLA+ has been described as exhaustively-testable pseudocode and blueprints for software systems;
the TLA stands for "Temporal Logic of Actions."
```

TLA + 是基于动作时序逻辑TLA（Temporal Logic of Actions）加上一阶逻辑和ZF集合论的规范说明语言 。它的描述分为动作层和时序逻辑层，动作层描述系统在动作发生时的演进（可以理解为状态迁移），时序逻辑层指定系统行为必须满足的性质（可以理解为条件约束）。TLA+兼具操作性和描述性特征，能够对系统行为和待验证性质在统一的逻辑框架下描述和验证。

## 作者介绍

leslie lamport是美国计算机科学家及微软首席科学家。

### 主要荣誉

- 1991年入选美国国家工程院院士。
- 2000年凭借《时间、时钟》论文获得ACM分布式计算原理研讨会首届有影响力论文奖。
- 2004年凭借与计算机科学有关的信息处理领域突出贡献荣获IEEE Emanuel R. Piore 奖。
- 2005年荣获Edsger W. Dijkstra分布式计算奖。
- 三次获得ACM SIGOPS荣誉大奖。该奖项旨在表彰发表至少10年、在操作系统领域最有影响力的论文。该奖项成立于2005年，而Lamport曾分别于2007年、2012年和2013年赢得这一殊荣。
- 2008年荣获IEEE计算机科学逻辑研讨会（LICS）最经得起时间考验奖。该奖项每年颁发一次，旨在表彰20年以前发表并经得住时间考验的LICS论文。
- 2008年荣获IEEE约翰·冯·诺依曼奖章。
- 2011年当选美国国家科学院院士。
- 2013年荣获Jean-Claude Laprie可信计算奖&图灵奖。

## 相关重要事件

- 1957年由Arthur Prior提出现代时间逻辑
- 1975年Ed Ashcroft发表《Proving Assertions About Parallel Programs》，首次提出并发系统中的不变性概念
- 1977年Prior提出线性时态逻辑（LTL），LTL迅速成为并发程序分析的重要工具，可轻松表达诸如互斥和无死锁之类的特性
- 1978年Lamport发表《Time, Clocks, and the Ordering of Events in a Distributed System》，该文是计算机科学史上被引用最多的文献，为“并发系统的规范与验证”研究贡献了核心原理。
- 1980年Lamport发表《'Sometime' is Sometimes 'Not Never'》，引用次数最多的时态逻辑论文。
- 1983年Lamport的《Specifying CLamportcurrent Programming Modules》论文中找到了一种实用的规范方法，该方法引入了将状态转换描述为primed和unprimed变量的布尔值函数的思想
- 1990年Lamport陆续发表了一些关于TLA的论文
- 1994年Lamport正式发表《The Temporal Logic of Actions》论文，该文提供了一种优雅的方式来形式化和系统化并发系统中使用的所有推理验证。
- 1999年Lamport发表《Specifying Concurrent Systems with TLA+》论文。同年Yuan Yu编写用于TLA +规范的TLC模型检查器;
- 2002年Lamport发布了一本完整的TLA+教科书《Specifying Systems: The TLA+ Language and Tools for Software Engineers》
- 2009年推出了PlusCal规范语言
- 2012年推出TLA+证明系统（TLAPS）
- 2014年推出TLA+2，增加了一些额外的语言结构，并大大增加了对证明系统的语言支持。

## 一些术语

```
State - an assignment of values to variables
Behaviour - a sequence of states
Step - a pair of successive states in a behavior
Stuttering step - a step during which variables are unchanged
Next-state relation - a relation describing how variables can change in any step
State function - an expression containing variables and constants that is not a next-state relation
State predicate - a Boolean-valued state function
Invariant - a state predicate true in all reachable states
Temporal formula - an expression containing statements in temporal logic
```

## IDE
TLA+的IDE是基于eclipse实现的，其包含一个带有错误和语法突出显示的编辑器，以及几个其他TLA+工具的GUI前端：

- The SANY syntactic analyzer, which parses and checks the spec for syntax errors.
- LaTeX转换器（to generate pretty-printed specs）
- PlusCal转换器
- TLC模型检查器
- TLAPS证明系统

这些工具统一位于TLA Toolbox中。

## 特点

与其它规范说明语言相比， TLA + 具有以下几个 特点：

1. 一个TLA + 模型本质上就是一条时序逻辑公式，完全由数学符号构成；
2. 在TLA + 逻辑框架下，系统行为的规范说明和待验证性质可以统一描述；
3. TLA + 提供了对具体模型“实现”抽象模型的简单数学定义：实现即蕴含；
4. TLA + 是无类型的。模型的类型正确性表达为一个待验证的类型不变式（Invariant）；
5. TLA + 既可以表达安全（Saftety）属性又可以表达活（Liveness）属性。

## 工业案例

1. **Xbox360**：在微软Xbox 360产品内存模块中发现了一个严重的错误。 TLA +还被用来为拜占庭式Paxos和Pastry分布式哈希表组件编写正确的证明。
2. **AWS**： AWS从2011年开始使用TLA+. TLA +模型检查在DynamoDB，S3，EBS和内部分布式锁管理器中均检测出了难以发现的潜在错误; 一些错误需要35个步骤的状态跟踪。
3. **Microsoft Azure**：Azur使用TLA+设计Cosmos DB, 一个具有五种不同一致性模型的全局分布式数据库。
4. Compaq多处理器高速缓存一致性协议中的错误。
5. 一款以网络为中心的RTOS应用案例。
6. 对各种分布式一致性算法（Paxos、Raft等）的正确性验证。
7. 各种领域应用论文，例如：wimax协议验证、滚动升级验证等。

## 价值

1. 帮助架构师对系统行为进行清晰思考（科学视角）
2. 分布式系统原型验证
3. 对已有系统的正确性进行验证
4. 对系统架构演进实现质量守护

## 注意事项

1. 并非银弹
2. 对人的要求（基础数学、抽象能力、清晰思考）
3. 与实际代码尚有一段距离
4. 新的语言、工具的学习

## 参考文献
https://alchetron.com/TLA-
https://www.msra.cn/zh-cn/news/features/leslie-lamport-turing-20140327
