软件可靠性取决于两方面：
* 软件开发的方法与过程
* 软件产品的测试与验证

采用形式化方法对系统进行验证和分析，是构造安全可信软件的一个重要途径。

## 发展历程
什么是形式化方法？
有严格数学基础的软件和系统开发方法，支持计算机系统及软件的规约、设计、验证与演化等活动。

针对60年代“软件危机”提出两种方法：
* 采用工程方法来组织、管理软件的开发过程；
* 深入探讨程序和程序开发过程的规律，建立严密的理论，以期能用来指导软件开发实践。

前者导致“软件工程”的出现和发展，后者则推动了形式化方法的深入研究。

形式化方法能在系统开发的早期发现系统中的不一致、歧义、不完全和错误，已被证明是一种行之有效的减少设计错误、提高软件系统可信性的重要途径。

# 基本内容
基本内容包括：
* 系统建模。通过构造系统S的模型M来描述系统及其行为模式。
* 形式规约。通过定义系统S必须满足的一些属性ψ，如：安全性、活性等来描述系统约束。
* 形式验证。证明描述系统S行为的模型M确实满足系统形式规约ψ（即验证M|=ψ）。

## 系统建模

## 形式规约
确定“做什么”，而清晰、简明、一致且无歧义的方式。非“怎么做”。需求规约就是一种以清晰、简明、一致且无歧义的方式，刻画客户或用户所需系统中所有重要方面的一组陈述。
一方面，规约是客户或用户与软件开发人员之间的接口界面，可看作一种契约合同；
另一方面，规约也是设计和编写程序的出发点和验证程序是否正确的依据。

## 形式验证
形式验证分为两类：
* 以逻辑推理为基础的演绎验证
* 以穷尽搜索为基础的模型检测

### 演绎证明
用逻辑公式描述系统性质，通过一些公理或推理规则来证明系统具有某些性质。

优点：
既可验证有穷状态系统，也可使用归纳法来处理无限状态问题。
缺点：
不能做到完全自动化验证。

### 模型检测
通过搜索待验证系统模型的有穷状态空间来检验该系统的行为是否具备预期属性的一种自动验证技术。

关键问题：如何有效缓解“状态空间爆炸”：
* 基于简化全局状态空间
* 基于检测局部状态空间

主要方法有：
* 符号模型检测
* 有界模型检测
* 对称模型检测
* 偏序模型检测
* On-the-fly模型检测
* 抽象与组合方法