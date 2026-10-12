# 正方形 Hardinian 数组的两条渐近公式

这份研究稿证明了 Robert Dougherty-Bliss 与 Manuel Kauers 在 *Hardinian Arrays*（**Electronic Journal of Combinatorics 31(2), 2024, P2.9**，[论文链接](https://doi.org/10.37236/12358)）第 12 页列为猜想的两条渐近公式：

\[
H_2(n,n)\sim\frac{16^n}{324\pi n},\qquad
H_3(n,n)\sim\frac{64^n}{78732\pi n^3}.
\]

`H_r(n,n)` 是原论文定义的正方形数组数量。结论覆盖固定 `r = 2, 3`、边长趋于无穷的情形；不声称解决一般 `r`。

[OEIS A253217](https://oeis.org/A253217) 将 `r = 2` 的渐近猜想署名为 Vaclav Kotesovec，日期为 2023 年 3 月 2 日。

- [完整英文证明 PDF](main.pdf)
- [LaTeX 源码](main.tex)
- [英文说明与复跑命令](README.md)
- [AI 使用与验证状态](AI_USAGE.md)

证明以原论文已建立的互补子式计数恒等式为起点，先推导精确平方和公式，再通过二项式的一致局部展开、完整尾部估计和矩行列式求出渐近常数。全文给出了数学证明过程，没有用有限数据代替无穷范围的证明，也没有依赖猜测的递推式。

随稿 `hardinian.py` 已实际运行到 `n = 201`，并通过原始数组规则的直接枚举、互补子式计算及脚本列明的 OEIS 数据核对。运行：

```text
python hardinian.py --max-n 201
```

整数检查仅需 Python 3.8 或以上版本的标准库。安装 SymPy 和 mpmath 后，还会执行精确符号恒等式检查与小数比值展示。不要使用 `-O`，以免关闭断言。结果保存在 `hardinian_results.json`。

本研究在 AI 辅助下完成。当前版本提供完整书面论证和可复现检查，不声称已获外部同行评审、证明助手形式化验证或穷尽性的文献优先权认证。
