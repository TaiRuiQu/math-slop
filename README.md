# math-slop

解析数论等方向的数学中间成果，附可读证明和 Lean 形式化核验。每份文稿列明数学假设，Lean 核验记录说明已检查的定理及仍需显式输入的引理。

## 成果索引

<!-- results:start -->

### [指定无零宽度的李–刘谱假设 S 反例](readable/01-prescribed-s-width.md)

- **李–刘算子范数的二阶下界** · 在全局 Dirichlet GRH 下，对任意固定 $c>0$，证明每个充分大的 $[X,2X]$ 至少有 $\sqrt X\exp(c\sqrt{\log X})$ 个偶数满足李–刘算子范数的二阶下界，二阶系数为 $2+\log 2$。
- **首阶指定宽度反例** · 在全局 Dirichlet GRH 下，证明谱假设 $S_h$ 对预先指定的 $h(N)=\sqrt N\exp(-d\sqrt{\log N}/\log\log N)$ 失败，覆盖所有固定 $0<d\le\sqrt2$。
- **二阶指定宽度反例** · 在全局 Dirichlet GRH 下，证明谱假设 $S_h$ 对 $h(N)=\sqrt N\exp[-(\sqrt{2\log N}/\log\log N)(1+d/\log\log N)]$ 失败，覆盖所有固定 $d<2+\log 2$。
- **奇异级数趋近最小值的反例子族** · 在全局 Dirichlet GRH 下，构造每个充分大的 $[X,2X]$ 内至少有 $\sqrt X\exp(c\log X/(\log\log X)^4)$ 个成员的反例子族（某个 $c>0$），其奇异级数趋于 $2C_2$，每个成员有至少 $\exp((1/\sqrt2-o(1))\sqrt{\log N})$ 个较小素数满足 $\log p\sim\sqrt{2\log N}$ 的哥德巴赫表示。

[Lean 部分核验](lean/verification/01-prescribed-s-width.md) · [Lean 入口](lean/PrescribedSWidth.lean)

<!-- results:end -->

## 仓库入口

- [可读证明](readable/)保存每项成果的命题、证明和参考文献。
- [Lean 工程](lean/README.md)保存形式化代码、构建命令和逐项核验记录。
- [JSON 成果目录](catalog.json)提供稳定编号、逐条命题概述、数学假设和 Lean 状态。
- [纯文本索引](llms.txt)供 AI agent 发现并直接读取文稿和核验记录。
- [发布指南](PUBLISHING.md)说明怎样新增成果、刷新索引和生成可抓取的 HTML。
