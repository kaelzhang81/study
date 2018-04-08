# 形式化规范语言TLA+

## 定义

维基百科上对TLA+是这样定义的：

```
a formal specification language developed by Leslie Lamport. 
It is used to design, model, document, and verify concurrent systems. 

TLA+ has been described as exhaustively-testable pseudocode and blueprints for software systems;
the TLA stands for "Temporal Logic of Actions."
```



TLA + 是基于动作时序逻辑TLA（Temporal Logic of Actions）、一阶逻辑和ZF集合论的规范说明语言 。它的描述分为动作层和时序逻辑层，动作层描述系统在动作发生时的演进，时序逻辑层指定系统行为必须满足的性质。TLA+兼具操作性和描述性特征，能够对系统行为和待验证性质在统一的逻辑框架下描述和验证。

## 特点

与其它规范说明语言相比， TLA + 具有以下几个 特点：
1. 一个TLA + 模型本质上就是一条时序逻辑公式，完全由数学符号构成；
2. 在TLA + 逻辑框架下，系统行为的规范说明和待验证性质可以统一描述；
3. TLA + 提供了对具体模型“实现”抽象模型的简单数学定义：实现即蕴含；
4. TLA + 是无类型的。模型的类型正确性表达为一个待验证的类型不变式（Invariant）；
5. TLA + 既可以表达安全（Saftety）属性又可以表达活（Liveness）属性。
