# 正方形 Hardinian 数组：全固定参数渐近

这是同一研究主线的 v0.2.0 扩展版本。对每个预先固定的整数 r>=1，n趋于无穷时，

\[
H_r(n,n)\sim\frac{2^{r(r-3)}}{3^{r^2}\pi^r}
\left(\prod_{j=1}^r\Gamma(j/2)^2\right)4^{rn}n^{-\binom r2}.
\]

[完整英文扩展卷](extensions/paper/proof.pdf)及[TeX](extensions/paper/proof.tex)保留任意固定阶展开、Vandermonde抵消、Mehta归一化、全尾和常数推导；r=1的kappa定义为1，r=0、1另有精确处理。不覆盖r随n增长或矩形两维同时增长。

原论文r<=5表格均吻合，但r=7常数带有额外素因子5²，否定“只由2、3、pi整数幂组成”的另一个模式，不能说全部旧猜测都成立。ACM正式四页poster的固定宽多项式定理已作来源比较，它不直接涵盖k=n。

[旧r=2,3数学稿](main.pdf)、main.tex、hardinian.py和hardinian_results.json保持原字节；旧稿的参数限制是其历史范围。[执行说明](REPRODUCIBILITY.md)区分作者自报、历史候选复跑、另写的有限检查与本扩展卷未新增数学执行的事实。哈希一致不是复跑证明。

本稿在AI辅助下整理，不声称独立人工同行评审、证明助手或世界优先权认证。第三方论文不随包分发。参见[SCOPE](SCOPE.md)、[REFERENCES](REFERENCES.md)及[RIGHTS](RIGHTS.md)。
