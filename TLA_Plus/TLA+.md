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

leslie lamport，微软首席科学家

### 主要荣誉
1991年入选美国国家工程院院士。
2000年凭借《时间、时钟》论文获得ACM分布式计算原理研讨会首届有影响力论文奖。
2004年凭借与计算机科学有关的信息处理领域突出贡献荣获IEEE Emanuel R. Piore 奖。
2005年荣获Edsger W. Dijkstra分布式计算奖。
三次获得ACM SIGOPS荣誉大奖。该奖项旨在表彰发表至少10年、在操作系统领域最有影响力的论文。该奖项成立于2005年，而Lamport曾分别于2007年、2012年和2013年赢得这一殊荣。
2008年荣获IEEE计算机科学逻辑研讨会（LICS）最经得起时间考验奖。该奖项每年颁发一次，旨在表彰20年以前发表并经得住时间考验的LICS论文。
2008年荣获IEEE约翰·冯·诺依曼奖章。
2011年当选美国国家科学院院士。
2013年荣获Jean-Claude Laprie可信计算奖&图灵奖。

## 特点

与其它规范说明语言相比， TLA + 具有以下几个 特点：
1. 一个TLA + 模型本质上就是一条时序逻辑公式，完全由数学符号构成；
2. 在TLA + 逻辑框架下，系统行为的规范说明和待验证性质可以统一描述；
3. TLA + 提供了对具体模型“实现”抽象模型的简单数学定义：实现即蕴含；
4. TLA + 是无类型的。模型的类型正确性表达为一个待验证的类型不变式（Invariant）；
5. TLA + 既可以表达安全（Saftety）属性又可以表达活（Liveness）属性。
