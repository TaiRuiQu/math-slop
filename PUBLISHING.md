# 发布指南

## 新增成果

1. 在 `readable/` 添加一份 Markdown 文稿，写清命题、假设、证明和参考来源。
2. 在 [成果目录](catalog.json) 的 `results` 数组添加一项。`id` 用稳定的 ASCII 编号和短名，网页地址沿用 `results/<id>/`。`claims` 中每个主要命题或推论单独占一项，`summary` 用一句话写明假设和证明的结论。
3. 若有 Lean 代码，在 `lean/` 中维护源码，并在 `lean/verification/` 添加同编号的核验记录。`lean.status` 用 `partial` 表示部分核验，用 `complete` 表示文稿列出的命题已在其声明的数学假设下完整核验。尚无 Lean 代码时将 `lean` 设为 `null`。
4. 运行 `python tools/publish.py sync`，从目录更新根 README 的成果索引、Lean 入口和 `llms.txt`。

## 检查与预览

```powershell
python tools/publish.py check
python -m pip install -r tools/requirements.txt
python tools/publish.py build
python -m http.server --directory _site 8000
```

HTML 首页、每项成果的页面和 Lean 核验记录都会写入 `_site/`。正文直接出现在 HTML 中，数学公式保留 TeX。站点同时提供原始 Markdown、登记的 Lean 源码、`catalog.json`、`llms.txt` 和 `sitemap.xml`。生成目录由脚本在每次构建时重建。

## 发布到 GitHub Pages

将审阅过的内容推送到 GitHub。在仓库的 **Settings → Pages** 中选择 **GitHub Actions**，然后在 **Actions** 中手动运行 **Publish math-slop**。工作流会检查索引一致性，并使用 Pages 的实际地址生成网页、结构化数据与 sitemap。[GitHub Pages 发布源](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site)

发布后可从首页发现所有成果，从 `catalog.json` 读取机器可读记录，从 `llms.txt` 找到原文，并在搜索站长工具中提交站点的 `sitemap.xml`。[Google sitemap 指南](https://developers.google.com/search/docs/crawling-indexing/sitemaps/build-sitemap)
