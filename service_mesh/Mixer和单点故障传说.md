# Mixer和单点故障传说---增进高可用和低延迟


增强的SLO：Mixer insulates proxies and services from infrastructure backend failures, enabling higher effective mesh availability. The mesh as a whole tends to experience a lower rate of failure when interacting with the infrastructure backends than if Mixer were not present.
低延迟：Through aggressive use of shared multi-level caches and sharding, Mixer reduces average observed latencies across the mesh.

在一个高层次，Mixer提供：
后端抽象. Mixer隔离了网格中的Istio组件、服务与单个基础设施后端的实现细节。
中介. Mixer允许运维人员对网格和基础设施后端之间的所有交互进行细粒度的控制。

然而除了这些纯功能性的方面，Mixer还具有其他特性为系统提供额外的好处。

## Mixer: SLO加速器
与Mixer单点故障会导致网格中断的说法相反，我们相信它实际上提高了网格的有效可用性。怎么可能这样呢？有三个基本特点在起作用：
1.无状态。Mixer是无状态的，因为它不管理任何持久存储。
2.可靠。Mixer本身被设计成一个高度可靠的组件，设计目标是为任意单个的Mixer实例实现大于99.999％的正常运行时间。
3.缓存和缓冲。Mixer的设计就是为了积攒大量的暂存状态。

位于服务网格中，与每个服务实例相邻的边车代理必须在内存开销方面节制，这限制本地缓存和缓冲可能的数量。然而，Mixer独立存在的化，可以使用非常大的缓存和输出缓冲区。因此，Mixer扮演为一个高弹性和高可用的边车二级缓存。

Mixer的预期可用性远高于大多数基础设施后端（后端通常可用性可能达到99.9％），其本地缓存和缓冲区可以帮助屏蔽基础架构后端故障，即使后端无响应也能继续运行。

## Mixer延迟削减器
正如我们上面所解释的，Istio边车代理通常具有非常高效的一级缓存，它们可以从缓存中提供大部分流量。Mixer提供了更大的二级缓存共享池，这有助于降低每个请求的平均时延。

在缩短等待时间的同时，Mixer还可以固定地减少网格对基础设施后端的调用次数。取决于这些后端的支付方式，这将通过减少后端的有效QPS使你最终会节省一些现金。

## 后续工作
我们有机会在很多方面继续改进这个系统。

### 配置金丝雀

Mixer是高弾缩的故其一般可防止单实例故障。然而，当一份毒药配置部署导致所有Mixer实例基本同时崩溃（是的，这将是糟糕的一天）的话Mixer仍然容易出现级联故障。 为了防止这种情况发生，可以将配置更改加入一部分Mixer实例，然后大范围的配置。

Mixer还没有对配置变更的评估，但我们预计这将作为Istio正在进行的可靠配置分发工作的一部分。

### 缓存调优

我们尚未调整边车代理和Mixer缓存的大小。这项工作将着重于使用最少的资源实现最高的性能。

### 缓存共享

目前，每个混音器实例独立于所有其他实例运行。由一个Mixer实例处理的请求不会利用缓存在不同实例中的数据。我们最终将尝试使用分布式缓存（如memcached或Redis），以便提供更大的网状共享缓存，并进一步减少对基础设施后端的调用次数。

### 分片

在非常大型的网格中, Mixer的负载将会非常大。将会有大量Mixer实例, 每个实例都将为了满足传入流量不断保证缓存写入。 我们期望最终引入智能分片，以便Mixer实例变得更专地处理特定的数据流，以增加缓存命中率。

## 结论

Practical experience at Google showed that the model of a slim sidecar proxy and a large shared caching control plane intermediary hits a sweet spot, delivering excellent perceived availability and latency. We’ve taken the lessons learned there and applied them to create more sophisticated and effective caching, prefetching, and buffering strategies in Istio. We’ve also optimized the communication protocols to reduce overhead when a cache miss does occur.

Mixer is still young. As of Istio 0.3, we haven’t really done significant performance work within Mixer itself. This means when a request misses the sidecar cache, we spend more time in Mixer to respond to requests than we should. We’re doing a lot of work to improve this in coming months to reduce the overhead that Mixer imparts in the synchronous precondition check case.

We hope this post makes you appreciate the inherent benefits that Mixer brings to Istio. Don’t hesitate to post comments or questions to istio-integrations@.
