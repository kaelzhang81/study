# 算法与程序的区别

* Algorithms perform operations on arbitrary mathematical objects, such as graphs and vector spaces. Programs perform operations on simple objects such as Booleans and integers; operations on more complex data types must be coded using lower-level operations such as integer addition and method invocation.
* A program describes one method of computing a result; an algorithm may describe a class of possible computations. For example, an algorithm might simply require that a certain operation be performed for all values of i from 1 to N . A program specifies in which order those operations are performed.
* Execution of an algorithm consists of a sequence of steps. An algorithm’s computational complexity is the number of steps it takes to compute the result; defining a concurrent algorithm requires specifying what constitutes a single (atomic) step. There is no well-defined notion of a step of a program.

# PlusCal与程序语言的区别

* The language of PlusCal expressions is TLA+, a high-level specification language based on set theory and first-order logic [3]. TLA+ is infinitely more expressive than the expression language of any programming language. Even the subset of TLA+ that can be executed by the TLC model checker is far more expressive than any programming language.
* PlusCal provides simple constructs for expressing nondeterminism.
* PlusCal uses labels to describe the algorithm’s steps. However, you can omit the labels and let the PlusCal translator add them as necessary. You are likely to do this only for uniprocess (sequential) algorithms,where the partitioning of the computation into steps does not affect the values computed. For multiprocess (concurrent) algorithms, you will probably want to specify the grain of atomicity explicitly.
