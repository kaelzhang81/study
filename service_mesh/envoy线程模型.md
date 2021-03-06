https://blog.envoyproxy.io/envoy-threading-model-a8d44b922310

1.集群管理器是Envoy中的组件，用于管理所有已知的上游集群，CDS API，SDS / EDS API，DNS和主动（带外）健康检查。它负责创建包括发现的主机以及健康状况的每个上游群集的最终一致的视图。
2.运行状况检查程序会执行主动运行状况检查，并将健康状况更改报告回群集管理器。
3.执行CDS / SDS / EDS / DNS以确定群集成员资格。状态更改会报告给集群管理器。
4.每个工作者线程都不断运行一个事件循环。
5.当群集管理器确定群集的状态已更改时，它会创建群集状态的新只读快照并将其发布到每个工作线程。
6.在下一个沉静期间，工作线程将更新分配的TLS插槽中的快照。
7.在需要确定主机负载均衡的IO事件期间，负载均衡器将查询主机信息的TLS插槽。无需获取锁做这个。 （还要注意，TLS还可以在更新时触发事件，以便负载平衡器和其他组件可以重新计算缓存，数据结构等。这超出了本文的范围，但在代码的不同位置使用。

通过使用前面描述的过程，Envoy能够处理每个请求，而不需要任何锁定（除了之前描述的那些锁定之外）。 除了TLS代码本身的复杂性之外，大多数代码不需要了解线程是如何工作的，并且可以写成单线程的。 除了有的性能外，还使得大多数代码更容易编写，。

## 其他使用TLS的子系统

在envoy中广泛使用TLS和RCU。 其他一些例子包括：
运行时（特征标志）重写查找：当前特征标志重载映射在主线程上计算。 然后使用RCU语义为每个工作人员提供只读快照。
路由表交换：对于由RDS提供的路由表，路由表在主线程上实例化。 然后使用RCU语义为每个工作人员提供只读快照。 这使得路由表有效地交换原子。
HTTP日期头缓存：事实证明，每个请求（当每核执行〜25K + RPS时）计算HTTP日期头非常昂贵。 Envoy每半秒统一计算日期标题，并通过TLS和RCU将其提供给每个工作线程。
还有其他一些情况，但是前面的例子已经很好地提供TLS使用的示范。

## 已知的性能陷阱
虽然总体envoy表现相当好，但是在使用非常高的并发性和吞吐量时，有一些已知的地方需要注意：

正如本文所述，当前所有工作线程在写入访问日志的内存缓冲区时都会获得锁。在高并发性和高吞吐量的情况下，当写入最终文件时，将需要按照无序传送的代价来执行每个工作线程的日志访问批处理。 或者访问日志可以成为每个工作者线程。
尽管统计数据的优化程度非常高，但是在非常高的并发性和吞吐量情况下，个别统计数据可能会出现原子争用。 对此的解决方案是每个工作线程的计数器定期冲洗中央计数器。 这将在后续的文章中讨论。
如果Envoy部署在只有极少数连接需要大量资源处理的情况下，现有架构将无法正常运行。 这是因为不能保证工作线程之间的连接会平均分配。 这可以通过实现工作线程连接平衡来解决，其中工作线程能够将连接转发给另一个工作线程进行处理。

## 结论

Envoy的线程模型旨在简化编程和大规模并行处理，但如果没有正确调整，可能会浪费内存和连接。 这个模型使得它在非常高的工作线程数量和吞吐量下表现的非常好。

正如我在Twitter上简单提到的那样，这个设计也适合在像DPDK这样的完整的用户模式网络栈上运行，这可能会导致商品服务器在完整的层7处理时每秒处理数百万个请求。 看看未来几年将会建成什么是非常有趣的。

最后一个快速的评论：我被问了很多次为什么我们选择C ++开发envoy。 原因在于它仍然是唯一广泛部署的生产级语言，在这种语言中可以构建这篇文章中描述的体系结构。 对于很多项目来说，C++肯定是不正确的，但对于某些用例下，它仍然是完成工作的唯一工具。

## 代码链接
