# 指定无零宽度的李–刘谱假设 S 反例

假设全局 Dirichlet GRH。李嘉旻、刘建亚把每个充分大的偶数 $N$ 与一个紧自伴算子 $T_N$ 及其谱函数 $\mathcal X_N$ 联系起来。假设 $S_h$ 先选定一个函数 $h(N)\to\infty$，再要求 $\mathcal X_N$ 对所有充分大的偶数 $N$ 都在指定的右半平面内无零点。增大 $h$ 会扩大要求无零的区域。本文构造在每个充分大的区间 $[X,2X]$ 内都出现的反例，并确定构造能达到的二阶宽度。

## 结果

写 $L_N=\log N$、$\ell_N=\log L_N$。对任意固定的 $d_0>1/\sqrt2$ 和 $\varepsilon>0$，每个充分大的 $[X,2X]$ 内至少有

$$
\sqrt X\exp\!\left((d_0-1/\sqrt2-\varepsilon)\sqrt{\log X}\right)
$$

个偶数 $N$ 满足

$$
\log(\sqrt N\,\|T_N\|)\ge
\frac{\sqrt{2L_N}}{\ell_N}
\left(1+\frac{2+\log 2}{\ell_N}-\frac{C}{\ell_N^2}\right).
\tag{1}
$$

这里可选固定的 $C>0$，对 $X$ 的起始要求可依赖 $d_0$ 和 $\varepsilon$。给出下界的矩阵元使用尺度为

$$
\log m=\sqrt{2L_N}+O\!\left(\frac{\sqrt{L_N}}{\ell_N}\right)
\tag{2}
$$

的小变量。由 (1)，以下两类预先指定的 $h$ 都有反例。

- $h(N)=\sqrt N\exp(-d\sqrt{L_N}/\ell_N)$，其中 $0<d\le\sqrt2$ 固定。
- $h(N)=\sqrt N\exp[-(\sqrt{2L_N}/\ell_N)(1+d/\ell_N)]$，其中 $d<2+\log 2$ 固定。

还可以构造一个满足 (1)–(2) 的族，在每个充分大的 $[X,2X]$ 内至少有 $\sqrt X\exp(c\log X/(\log\log X)^4)$ 个成员，其中 $c>0$ 固定。在这一族上，哥德巴赫奇异级数一致趋于 $2C_2$，其中 $C_2=\prod_{p>2}(1-(p-1)^{-2})$。每个成员有至少 $\exp((1/\sqrt2-o(1))\sqrt{L_N})$ 个不同的表示 $N=p+q$，且较小的素数 $p$ 满足 (2)。

## 1. 筛和与欧拉积

固定非负的光滑权 $w,v$，紧支撑于 $(1,2)$，积分均为 $1$。令

$$
U(x)=\int w(y)v(20y-x)\,dy,\qquad F(x)=v(x)-U(x).
$$

$U$ 的支撑在 $(18,39)$，积分为 $1$。因此 $\int F=0$，而 $\widehat F(1/2)\ge 2^{-1/2}-18^{-1/2}>0$，其中 $\widehat F(s)=\int_0^\infty F(x)x^{s-1}\,dx$。对平方自由模数 $Q$，考察

$$
R_Q(H)=H^{-1}\sum_{\substack{t\ge1\\(t,Q)=1}} F(t/H).
$$

莫比乌斯反演把这个和拆成 $d\mid Q$ 上的格点和 $\sum_{j\ge1}F(jd/H)$。由于 $F$ 积分为零，把每个格点值与前一个格区间的平均作比较，格点和的绝对值至多为 $\int|F'|$。按支撑内的格点数估计又得到 $O(H/d)$。由这两个界可得 $|R_Q(H)|\ll 2^{\omega(Q)}/H$，并有更精细的界

$$
\sqrt H\,|R_Q(H)|\ll\sum_{d\mid Q}d^{-1/2}\exp(-|\log H-\log d|/2).
\tag{3}
$$

当 $H<1/40$ 时筛和为零。对 $\Re s>1$，交换求和与积分，并在每一项中令 $x=t/H$，就得到

$$
I_Q(s):=\int_0^\infty R_Q(H)H^{1-s}\,\frac{dH}{H}
=\widehat F(s)\zeta(s)\prod_{p\mid Q}(1-p^{-s}).
\tag{4}
$$

左边由 $R_Q(H)=O_Q(H^{-1})$ 在 $\Re s>0$ 上全纯。右边在 $s=1$ 的极点由 $\widehat F(1)=0$ 消去，故 (4) 在此半平面继续成立。

先取 $Q=P(z):=\prod_{p\le z}p$，再取 $s=1/2+i\pi/\log z$。接近 $z$ 的素数满足 $p^{-i\pi/\log z}\approx-1$，于是欧拉因子 $1-p^{-s}$ 接近其模的上界 $1+p^{-1/2}$。记 $V_Q=\prod_{p\mid Q}(1+p^{-1/2})$。对 $r=p^{-1/2}$，两者模平方之差恰为 $2r(1+\cos(\pi\log p/\log z))$。用 $|1-p^{-s}|\ge 1-2^{-1/2}$ 和 $1-\cos x\le x^2/2$，可得

$$
0\le\log V_Q-\sum_{p\mid Q}\log|1-p^{-s}|
\ll\frac{1}{\log^2 z}\sum_{p\le z}\frac{\log^2(z/p)}{\sqrt p}
\ll\frac{\sqrt z}{\log^3 z}.
\tag{5}
$$

最后一步把 $p\le\sqrt z$ 以全部整数估计，对其余素数按 $ze^{-j-1}<p\le ze^{-j}$ 分段。素数计数上界给出的各段贡献至多为 $O((\sqrt z/\log z)(j+1)^2 e^{-j/2})$。另有 $|\widehat F(s)\zeta(s)|\asymp1$，因为 $s\to1/2$，而 $\zeta(1/2)\ne0$ 可由交错级数判明。

二阶系数来自 $\sum_{p\le z}p^{-1/2}$。用 RH 的 $\pi(x)=\mathrm{Li}(x)+O(\sqrt x\log x)$ 做分部求和，主积分换元 $u=\sqrt x$ 后是 $\mathrm{Li}(\sqrt z)+O(1)$，误差是 $O(\log^2 z)$。展开对数积分，结合 $\log(1+p^{-1/2})=p^{-1/2}+O(p^{-1})$ 和 (5)，得到

$$
\log|I_Q(s)|=\frac{2\sqrt z}{\log z}
\left(1+\frac2{\log z}+O(\log^{-2}z)\right).
\tag{6}
$$

## 2. 从积分定位小变量

在 $Q$ 的约数上赋予概率 $\Pr(D=d)=d^{-1/2}/V_Q$。这等价于各个素数 $p\mid Q$ 以概率 $1/(\sqrt p+1)$ 独立入选，然后相乘。于是 (3) 的右端是 $V_Q\mathbb E e^{-|\log H-\log D|/2}$ 乘一个绝对常数。对 $Q=P(z)$，分部求和及 RH 的 $\vartheta(x)=x+O(\sqrt x\log^2 x)$ 给出

$$
\mu=\mathbb E\log D=2\sqrt z+O(\log^3 z),\qquad
\operatorname{Var}(\log D)\ll\sqrt z\log z.
$$

其中将 $1/(\sqrt p+1)$ 换为 $1/\sqrt p$ 的损失至多为 $\sum_{p\le z}(\log p)/p=O(\log z)$。每个居中的独立项至多为 $\log z$。令 $T=A\sqrt z/\log z$，Bernstein 不等式给出尾概率至多 $2\exp(-c_0 A^2\sqrt z/\log^3 z)$，这里 $A\ge1$ 固定，$c_0>0$ 与 $A$ 无关。将 (3) 在 $|\log H-\mu|>2T$ 上对 $dH/H$ 积分。若 $|\log D-\mu|\le T$，只需积距离 $\log D$ 至少 $T$ 的指数尾。其余事件上的全积分至多为 $4$。故尾积分至多为

$$
O\!\left(V_Q\left[e^{-T/2}+2e^{-c_0 A^2\sqrt z/\log^3 z}\right]\right).
$$

由 (5)，$|I_Q(s)|\gg V_Q\exp(-C_0\sqrt z/\log^3 z)$。取固定 $A$ 使 $c_0A^2>C_0+1$，尾积分就是 $o(|I_Q(s)|)$。余下区间的对数长度为 $4T$。在其中选取一个 $H$，使 $\sqrt H|R_Q(H)|\ge |I_Q(s)|/(8T)$，因此

$$
\begin{aligned}
\log H&=2\sqrt z+O(\sqrt z/\log z),\\
\log(\sqrt H\,|R_Q(H)|)&\ge\frac{2\sqrt z}{\log z}
\left(1+\frac2{\log z}-\frac{C_1}{\log^2 z}\right).
\end{aligned}
\tag{7}
$$

抽取 $H$ 损失的 $\log(8T)$ 只有 $O(\log z)$。

## 3. 转移到素数相关与算子范数

写 $L=\log X$、$\ell=\log L$。取 $z$ 为满足 $\vartheta(z)\le L/2-d_0\sqrt L$ 的最大素数。素数乘积的下一次增长是 $O(\log z)$，所以

$$
\log P(z)=L/2-d_0\sqrt L+O(\ell),\qquad
z=L/2+O_{d_0}(\sqrt L\,\ell^2).
\tag{8}
$$

取 (7) 给出的 $H$，令 $M=10H$。用整数移位 $a$ 定义 $b_a(m)=w(m/M)v((m-a)/H)$ 及

$$
S_a=\sum_{m\text{ 为奇数}}\Lambda(m)b_a(m)
\bigl(\mathbf1_{(a-m,Q)=1}-\mathbf1_{(a+m,Q)=1}\bigr).
$$

求 $\sum_a S_a$ 时，第一项令 $t=m-a$，得到 $\sum_m\Lambda(m)w(m/M)$ 与筛过的 $v$ 和的乘积。第二项令 $t=a+m$。RH 的 $\psi(x)=x+O(\sqrt x\log^2(2x))$ 与分部求和给出

$$
\sum_{m\text{ 为奇数}}\Lambda(m)w(m/M)v((2m-t)/H)
=M U(t/H)+O(\sqrt H\log^2(2H)).
$$

这个误差对 $t$ 一致，因为 $M/H=10$，复合权的总变差有界。第一项的 $m$ 和同样等于 $M+O(\sqrt H\log^2(2H))$。因此

$$
\sum_a S_a=MH\bigl(R_Q(H)+O(H^{-1/2}\log^2(2H))\bigr).
$$

(7) 使误差相对于主项趋零。只有 $O(H)$ 个 $a$ 有贡献，且 $2\mid Q$ 使它们都是偶数。存在一个偶数 $a$ 使 $|S_a|\gg H|R_Q(H)|$。若 $S_a<0$，选剩余类 $a'=-a$，否则选 $a'=a$，两种情形都继续使用原权 $b_a$。这样两个筛指示函数的差在平均中给出 $|S_a|$。

令 $\mathcal A=\{N\in[X,2X]\cap\mathbb Z:N\equiv a'\pmod Q\}$ 及 $K=|\mathcal A|\sim X/Q$。实际的相关差为

$$
B_N(b_a)=\sum_{(m,N)=1}\Lambda(m)b_a(m)(\Lambda(N-m)-\Lambda(N+m)).
$$

对固定的奇素数幂 $m$，全局 GRH 给出模 $Q$ 的素数幂加权计数，单位类的主项为 $X/\varphi(Q)$，每类误差为 $O(\sqrt X\log^2(XQ))$。非单位类的非零项只能来自其固定公因子的素数幂。排除 $(m,N)>1$ 也只删去 $m$ 的底素数的幂权重。这两种损失各至多为 $O(L)$。乘上短变量权并求和，得到

$$
\frac1K\sum_{N\in\mathcal A} B_N(b_a)
=\frac{X}{K\varphi(Q)}|S_a|+O(HQX^{-1/2}\log^2(XQ)).
\tag{9}
$$

主项因子有固定正下界。由 (7)–(8)，$\sqrt H=\exp((1/\sqrt2+o(1))\sqrt L)$，所以误差除以 $\sqrt H$ 后至多为 $\exp(-(d_0-1/\sqrt2+o(1))\sqrt L)$。另一方面，$|B_N(b_a)|\ll HL$。取阈值为平均值下界的一半，则超过阈值的 $N$ 至少有 $\gg K|R_Q(H)|/L$ 个，每个都满足 $B_N(b_a)\gg H|R_Q(H)|$。用 $|R_Q(H)|\ge H^{-1/2}$ 得到结果中的计数。

由 (7)–(8)，$M<N/20$ 对所有充分大的 $N\in[X,2X]$ 成立。在 Hardy 空间中，取小侧测试 $f(u)=b_a(Nu)$，并取大侧测试 $g$ 紧支撑于 $(4/5,6/5)$，且在 $[9/10,11/10]$ 恒为 $1$。两种平移的连续项在 $g(1\pm u)=1$ 上精确相消。算术项由奇特征正交关系留下 $n=N+m$ 与 $n=N-m$，符号相反，矩阵元为 $-B_N(b_a)/N$。小侧向量的范数为 $O(M/\sqrt{NH})$，因为支撑长度至多 $H/N$、$|uf'(u)|\ll M/H$。大侧向量的范数为 $O(1)$。于是 $|B_N(b_a)|\ll M\sqrt{N/H}\,\|T_N\|$，从而 $\sqrt N\|T_N\|\gg\sqrt H|R_Q(H)|$。这一步使用 $\mathrm{GRH}(N)$，式 (9) 使用辅助模数上的 GRH。[Hardy 矩阵元引理，§2](https://hexagonmath.org/pdf/2611.00788v1)

最后，(8) 允许在 (7) 的主项中用 $L/2$ 替换 $z$，误差只有 $O_{d_0}(\ell)=o(\sqrt L/\ell^3)$。展开 $1/\log(L/2)=1/(\ell-\log 2)$ 得到 (1) 的二阶系数 $2+\log 2$。由于 $L_N=L+O(1)$，换成 $L_N$ 同样只产生可吸收的误差。$m\in[10H,20H]$ 则给出 (2)。

## 4. 奇异级数近最小值与真素数表示

沿用 (8) 的 $z$，取 $y=z/(\log z)^4$，把 $P(z)$ 分成 $Q=2\prod_{y<p\le z}p$ 与 $R=\prod_{2<p\le y}p$。这次用 $Q$ 构造筛和，再要求 $N$ 与 $R$ 互素。移除的素数使欧拉积的对数改变至多 $O(\sqrt y/\log y)=O(\sqrt z/\log^3 z)$，使除数对数的中心改变至多 $O(\sqrt y)=O(\sqrt z/\log^2 z)$。方差的原上界仍成立，因此第 2 节照样给出 (7)。

中国剩余定理把 $N\equiv a'\pmod Q$ 且 $(N,R)=1$ 写成模 $QR$ 的 $\varphi(R)$ 个类，总数 $K'\sim X\varphi(R)/(QR)$。对固定 $m$ 和任一符号，模 $R$ 的每个素因子 $p$ 上要排除 $0$ 和 $\mp m$。所以允许类的数目是

$$
\nu(m)=\prod_{\substack{p\mid R\\p\nmid m}}(p-2)\prod_{\substack{p\mid R\\p\mid m}}(p-1).
$$

以 $\nu_0=\prod_{p\mid R}(p-2)$ 替换它时，权重只有在 $m$ 是 $p\mid R$ 的幂时才改变，额外系数为 $1/(p-2)$。每个 $p>2$ 在 $[10H,20H]$ 至多有一个幂，除以 $\nu_0$ 后的总加性损失是 $O(\sum_{2<p\le y}\log p/(p-2))=O(\log y)$。因此 (9) 的对应式为

$$
\frac{1}{K'}\sum_{N\in\mathcal A'}B_N(b_a)
=\frac{X\nu_0}{K'\varphi(Q)\varphi(R)}\bigl(|S_a|+O(\log y)\bigr)
 +O(HQRX^{-1/2}\log^2(XQR)),
$$

其中 $\mathcal A'$ 为加入互素条件后的集合。主项因子渐近于 $(Q/\varphi(Q))\prod_{p\mid R}(1-(p-1)^{-2})\asymp 1$。误差仍可控，因为 $QR=P(z)$，且 $|S_a|\gg H|R_Q(H)|$ 压过 $\log y$。用同样的阈值抽取，得到 $\gg K'|R_Q(H)|/L$ 个 $B_N(b_a)\gg H|R_Q(H)|$ 的偶数。计数中的增益来自 $\log R\sim L/(2\ell^4)$，它大于 $\log\sqrt H=O(\sqrt L)$。又有 $\varphi(R)/R\gg1/\log y$，故可取任意固定 $0<c<1/2$。

这些 $N$ 的奇素因子都大于 $y$。区间 $(y,z]$ 内素数的倒数和是 $o(1)$，因为 $\log y=\log z-4\log\log z$，可用素数倒数和的 Mertens 估计。$N$ 的大于 $z$ 的素因子至多 $L_N/\log z$ 个，倒数和至多 $L_N/(z\log z)=o(1)$。因此由乘积公式，$\mathfrak S(N)=2C_2\prod_{p\mid N,\ p>2}(1+1/(p-2))=2C_2(1+o(1))$。

对于被选中的每个 $N$，$b_a\ge0$ 保证 $N-m$ 的带权表示数至少为 $B_N(b_a)>0$。其中 $m$ 为真素数幂的权重至多为 $O(\sqrt H\log^2(2H)L)$。若 $N-m$ 为真幂，对每个指数 $j\ge2$，量级 $X$ 的 $j$ 次幂间距至少为常数乘 $\sqrt X$，所以长 $O(H)$ 的区间至多含 $O(1+H/\sqrt X)$ 个。全部指数的总权重至多为 $O((1+H/\sqrt X)L^2\log(2H))$。由 (7)，这两项相对于 $B_N(b_a)$ 都趋零。每个真素数对的权重至多为 $O(L\log(2H))$，而较小素数在 $[10H,20H]$ 内。相除得到至少 $\exp((1/\sqrt2-o(1))\sqrt{L_N})$ 个不同表示。

## 5. 换算为无零区反例

置 $\eta_N=h(N)^2 L_N^3/(N\mathfrak S(N))$。当 $0<\eta_N\le1/4$ 时，李–刘定理 6.1 给出精确判据

$$
S_h(N)\quad\Longleftrightarrow\quad
\|T_N\|\le\frac{\mathfrak S(N)}{2h(N)\sqrt{1-\eta_N}}.
$$

这里 $S_h(N)$ 表示 $\Re q>1-\eta_N$ 的无零条件。半平面是开的，范数上界允许等号。[李–刘原文 §2.4.4、定理 6.1](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)

两类 $h$ 均趋于无穷，且 $\eta_N\to0$，因为 $\mathfrak S(N)\ge2C_2>0$，$h(N)^2/N$ 的衰减快于 $L_N^{-3}$。又有 $\mathfrak S(N)\ll\log\log N$。对第一类宽度，在 $d=\sqrt2$ 时，(1) 仍留下量级 $\sqrt{L_N}/\ell_N^2$ 的正余量。对第二类宽度，余量的首项是 $(2+\log2-d)\sqrt{2L_N}/\ell_N^2$。两者都压过 $\log\mathfrak S(N)=O(\log\ell_N)$ 及判据中的有界项。因此每个上述偶数上，范数都严格超过该宽度允许的上界。

若改问是否存在某个容许的 $h\to\infty$ 使 $S_h$ 成立，目标是判断 $\|T_N\|/\mathfrak S(N)$ 是否沿全部大偶数趋零。本文对这个比值给出的下界量级为 $N^{-1/2+o(1)}$。

## 核验记录

初审核对了相位与集中估计的常数、辅助模数上的误差、CRT 筛选、两类真素数幂的损失和谱判据的严格边界。Lean 工程的对应定理、构建命令和仍需连接的解析输入见核验记录。[Lean 核验记录](../lean/verification/01-prescribed-s-width.md)
