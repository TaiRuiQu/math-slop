# Lean 形式化核验

Lean 版本由 [lean-toolchain](lean-toolchain) 固定，依赖版本记录在 [lake-manifest.json](lake-manifest.json)。每份核验记录对应一个成果编号，注明已验证的定理、所用假设及仍需形式化的推导。[成果索引](../README.md) · [核验记录](verification/)

## 构建

在 `lean/` 目录运行以下命令。首次构建会下载 Mathlib 缓存。

```powershell
lake exe cache get
lake --wfail build
```

## 工程入口

<!-- results:start -->

| 成果 | Lean 入口 | 核验记录 |
| --- | --- | --- |
| 指定无零宽度的李–刘谱假设 S 反例 | [PrescribedSWidth.lean](PrescribedSWidth.lean) | [Lean 部分核验](verification/01-prescribed-s-width.md) |

<!-- results:end -->
