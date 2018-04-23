# TLA+案例：JAVA缓冲区

前面介绍中提到，由于并发系统的不确定性，导致对系统的测试和调试是非常困难的。下面以共享缓存区案例来介绍如何在并发场景下应用TLA+。

## 背景介绍
假设要设计一个共享缓冲区系统，包含三块内容：生产者、消费者、缓冲区。

![](prodcons.png)

- 生产者：负责往缓冲区中写入数据。
- 消费者：负责从缓冲区中读取数据。
- 缓冲区：充当读写数据的同步器。缓冲区满的时候生产者需要等待，缓冲区空的时候消费者需要等待。

系统主要的同步控制通过缓冲区来完成，生产者和消费者只负责简单的写入和读取。由此可见缓冲区就是系统设计的关键所在，其JAVA实现如下：

···
  
  public class Buffer<E> {
  
    public final int capacity;
    private final E[] store;
    private int head, tail, size;
  
    @SuppressWarnings("unchecked")
    public Buffer (int capacity) {
      this.capacity = capacity;
      this.store = (E[])new Object[capacity];
    }
    private int next (int x) {
      return (x + 1) % store.length;
    }
    public synchronized void put (E e) throws InterruptedException {
      while (isFull())
        wait();
      notify();
      store[tail] = e;
      tail = next(tail);
      size++;
    }
    public synchronized E get () throws InterruptedException {
      while (isEmpty())
        wait();
      notify();
      E e = store[head];
      store[head] = null; // for GC
      head = next(head);
      size--;
      return e;
    }
    public synchronized boolean isFull () {
      return size == capacity;
    }
    public synchronized boolean isEmpty () {
      return size == 0;
    }
  }

···


