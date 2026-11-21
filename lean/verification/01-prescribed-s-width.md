# 指定无零宽度反例的 Lean 核验

工程使用 Lean 4.35.0，并复用固定版本的李–刘算子、奇异级数、谱函数和定理 6.1。[上游 Lean 工程](https://github.com/subfish-zhou/conditional-goldbach-lean/tree/c55db645f3b4aed00374fe4aa1fcee2428c88c4b/formalization) · [可读证明](../../readable/01-prescribed-s-width.md)

## 复现

在 [Lean 工程目录](../README.md)运行以下命令。首次构建会下载 Mathlib 的编译缓存，并编译导入的李–刘证明。

```powershell
lake exe cache get
lake --wfail build
```

严格构建已通过。对下表各步骤的主要定理运行了 `#print axioms`，结果仅列出 `propext`、`Classical.choice` 和 `Quot.sound`。下文列出的解析输入通过定理的参数传入。

## 已形式化的推导

| 可读证明中的步骤 | Lean 文件 |
| --- | --- |
| 零均值权的格点误差、莫比乌斯展开、约数归一化、欧拉积二次相位损失 | [Quadrature](../PrescribedSWidth/Quadrature.lean)、[Sieve](../PrescribedSWidth/Sieve.lean) |
| 筛和的 Mellin 恒等式及其在右上象限的解析延拓 | [Mellin](../PrescribedSWidth/Mellin.lean) |
| 独立选取素因子的指数矩和双侧尾界、对数窗外的积分界、由积分抽取见证 | [Concentration](../PrescribedSWidth/Concentration.lean)、[Localization](../PrescribedSWidth/Localization.lean) |
| 正负移位的符号、加权平均误差和计数、CRT 类数、扣除真素数幂后的表示数 | [Transfer](../PrescribedSWidth/Transfer.lean)、[Residues](../PrescribedSWidth/Residues.lean)、[Counterexamples](../PrescribedSWidth/Counterexamples.lean) |
| 更换素数截断时保留 $2+\log 2$、两类宽度的渐近余量、奇异级数的乘积界 | [Scales](../PrescribedSWidth/Scales.lean)、[SingularSeries](../PrescribedSWidth/SingularSeries.lean) |
| 容许性、精确谱判据、由算子下界推出指定宽度失败 | [Spectral](../PrescribedSWidth/Spectral.lean)、[Counterexamples](../PrescribedSWidth/Counterexamples.lean) |

`first_width_fails` 和 `second_width_fails` 使用上游的 `HypothesisS` 和真实的 `residualOperator`。它们从全局 GRH 和无界多个满足可读证明式 (1) 的模数导出矛盾。`card_normBound_of_progression_average` 给出这些模数的有限计数步骤，输入为逐项平移计数、主项与误差的比较以及短窗 Hardy 矩阵元估计。

## 仍待形式化的连接

- 从全局 GRH 建立随 $X$ 变化的统一算术级数估计，并导出短变量平滑素数和及其所需的显式素数和渐近式。
- 将具体卷积权、素数乘积预算和积分尾界连起来，统一选出每个区间的 $H,Q,a$。Mellin 延拓的定理签名包含筛和在端点的增长条件。
- 将 R 稿第 2 节的混合 Hardy 矩阵元引理接入 Lean 中的算子定义，并核验两个总体计数所用的所有渐近估计，包括近最小奇异级数族的真幂定量界。
