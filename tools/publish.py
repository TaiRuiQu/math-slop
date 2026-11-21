"""Synchronize the repository indexes and render the registered research notes."""

import argparse
from html import escape
import json
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
from urllib.parse import quote, unquote, urlsplit, urlunsplit
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parents[1]
START = "<!-- results:start -->"
END = "<!-- results:end -->"
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
LEAN_STATUS = {"partial": "Lean 部分核验", "complete": "Lean 完整核验"}


def https_url(value):
    url = urlsplit(value)
    if url.scheme != "https" or not url.hostname or url.username or url.query or url.fragment:
        raise ValueError(f"Expected a public HTTPS URL without a query or fragment: {value}")
    return value.rstrip("/") + "/"


def source_path(value, folder, suffix=None):
    path = PurePosixPath(value)
    candidate = ROOT / value
    if (
        path.as_posix() != value
        or folder not in path.parents
        or ".." in path.parts
        or "\\" in value
        or not candidate.resolve().is_relative_to(ROOT / folder)
        or (suffix and (path.suffix != suffix or not candidate.is_file()))
        or (suffix is None and not candidate.is_dir())
    ):
        raise ValueError(f"Missing or invalid source path: {value}")
    return candidate


def validate_ids(items):
    ids = [item["id"] for item in items]
    if len(set(ids)) != len(ids) or any(not SLUG.fullmatch(value) for value in ids):
        raise ValueError(f"IDs must be distinct lowercase slugs: {ids}")


def load_catalog():
    catalog = json.loads((ROOT / "catalog.json").read_text(encoding="utf-8"))
    if catalog["schema_version"] != 1:
        raise ValueError("Unsupported catalog schema_version")
    https_url(catalog["repository_url"])
    https_url(catalog["site_url"])
    validate_ids(catalog["results"])
    used_manuscripts = set()
    for result in catalog["results"]:
        manuscript = result["manuscript"]
        source_path(manuscript, PurePosixPath("readable"), ".md")
        if manuscript in used_manuscripts:
            raise ValueError(f"Manuscript registered twice: {manuscript}")
        used_manuscripts.add(manuscript)
        claims = result["claims"]
        if not claims:
            raise ValueError(f"{result['id']} needs a statement summary")
        validate_ids(claims)
        for claim in claims:
            summary = claim["summary"]
            if not summary.strip() or len(summary.splitlines()) != 1:
                raise ValueError(f"{result['id']}/{claim['id']} needs a one-line summary")
        if lean := result["lean"]:
            if lean["status"] not in LEAN_STATUS:
                raise ValueError(f"Unknown Lean status: {lean['status']}")
            source_path(lean["verification"], PurePosixPath("lean/verification"), ".md")
            source_path(lean["entrypoint"], PurePosixPath("lean"), ".lean")
            source_path(lean["source_directory"], PurePosixPath("lean"))
    return catalog


def readme_index(results):
    lines = []
    for result in results:
        lines.extend([f"### [{result['title']}]({result['manuscript']})", ""])
        lines.extend(f"- **{claim['title']}** · {claim['summary']}" for claim in result["claims"])
        lines.append("")
        if lean := result["lean"]:
            lines.extend([
                f"[{LEAN_STATUS[lean['status']]}]({lean['verification']}) · [Lean 入口]({lean['entrypoint']})",
                "",
            ])
    return "\n".join(lines).rstrip()


def lean_index(results):
    lines = ["| 成果 | Lean 入口 | 核验记录 |", "| --- | --- | --- |"]
    for result in results:
        if lean := result["lean"]:
            entrypoint = href_between("lean/README.md", lean["entrypoint"])
            report = href_between("lean/README.md", lean["verification"])
            status = LEAN_STATUS[lean["status"]]
            lines.append(f"| {result['title']} | [{PurePosixPath(entrypoint).name}]({entrypoint}) | [{status}]({report}) |")
    return "\n".join(lines)


def text_index(catalog, download_root):
    lines = [
        f"# {catalog['name']}",
        "",
        f"> {catalog['description']}",
        "",
        f"[JSON 成果目录]({download_root}catalog.json)列出编号、逐条命题、数学假设和核验状态。",
        "",
        "## 可读证明",
        "",
    ]
    for result in catalog["results"]:
        manuscript = quote(result["manuscript"])
        lines.append(f"- [{result['title']}]({download_root}{manuscript}): {result['description']}")
    lines.extend(["", "## Lean 核验记录", ""])
    for result in catalog["results"]:
        if lean := result["lean"]:
            report = quote(lean["verification"])
            lines.append(f"- [{result['title']}]({download_root}{report}): {LEAN_STATUS[lean['status']]}。")
    return "\n".join(lines).rstrip() + "\n"


def replace_index(path, content):
    readme = (ROOT / path).read_text(encoding="utf-8")
    before, start, block = readme.partition(START)
    _, end, after = block.partition(END)
    if not start or not end or readme.count(START) != 1 or readme.count(END) != 1:
        raise ValueError(f"{path} needs exactly one results:start / results:end block")
    return f"{before}{START}\n\n{content}\n\n{END}{after}"


def sync_indexes(catalog, check):
    owner_repo = urlsplit(catalog["repository_url"]).path.strip("/")
    download_root = f"https://raw.githubusercontent.com/{owner_repo}/{quote(catalog['default_branch'])}/"
    expected = {
        "README.md": replace_index("README.md", readme_index(catalog["results"])),
        "lean/README.md": replace_index("lean/README.md", lean_index(catalog["results"])),
        "llms.txt": text_index(catalog, download_root),
    }
    for path, content in expected.items():
        target = ROOT / path
        actual = target.read_text(encoding="utf-8") if target.is_file() else ""
        if actual == content:
            continue
        if check:
            raise ValueError(f"{path} is out of date. Run python tools/publish.py sync.")
        target.write_text(content, encoding="utf-8", newline="\n")


def href_between(source, target):
    return quote(posixpath.relpath(target, posixpath.dirname(source) or "."))


def render_markdown(source, output, routes, repository_root):
    from markdown_it import MarkdownIt
    from mdit_py_plugins.anchors import anchors_plugin
    from mdit_py_plugins.dollarmath import dollarmath_plugin

    def render_tex(content, options):
        content = escape(content)
        return rf"\[{content}\]" if options["display_mode"] else rf"\({content}\)"

    md = (
        MarkdownIt("commonmark", {"html": False})
        .enable("table")
        .use(anchors_plugin, min_level=1, max_level=5)
        .use(dollarmath_plugin, renderer=render_tex)
    )
    text = (ROOT / source).read_text(encoding="utf-8").replace(START, "").replace(END, "")
    tokens = md.parse(text)
    for token in tokens:
        for child in token.children or []:
            if child.type != "link_open":
                continue
            parts = urlsplit(child.attrGet("href") or "")
            if parts.scheme or parts.netloc or not parts.path:
                continue
            target = (ROOT / source).parent.joinpath(unquote(parts.path)).resolve()
            if not target.is_relative_to(ROOT):
                raise ValueError(f"Link leaves the repository in {source}: {parts.path}")
            relative = target.relative_to(ROOT).as_posix()
            if relative in routes:
                href = href_between(output, routes[relative])
            elif target.exists():
                kind = "tree" if target.is_dir() else "blob"
                repo, branch = repository_root
                href = f"{repo}/{kind}/{quote(branch)}/{quote(relative)}"
            else:
                raise ValueError(f"Missing link target in {source}: {parts.path}")
            href_parts = urlsplit(href)
            child.attrSet("href", urlunsplit(href_parts._replace(query=parts.query, fragment=parts.fragment)))
    return md.renderer.render(tokens, md.options, {})


def html_document(title, description, language, canonical, output, body, catalog, article=None):
    repository = escape(catalog["repository_url"], quote=True)
    stylesheet = href_between(output, "style.css")
    home = href_between(output, "index.html")
    data = json.dumps(article, ensure_ascii=False).replace("<", r"\u003c")
    structured = f'<script type="application/ld+json">{data}</script>' if article else ""
    return f"""<!doctype html>
<html lang="{escape(language, quote=True)}">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{escape(title)}</title>
  <meta name="description" content="{escape(description, quote=True)}">
  <link rel="canonical" href="{escape(canonical, quote=True)}">
  <link rel="alternate" type="application/json" href="{href_between(output, 'catalog.json')}" title="成果目录">
  <link rel="stylesheet" href="{stylesheet}">
  {structured}
  <script>window.MathJax = {{tex: {{tags: 'ams'}}}};</script>
  <script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml.js"></script>
</head>
<body>
  <nav aria-label="仓库导航"><a href="{home}">math-slop</a><a href="{repository}">GitHub</a></nav>
  <main>
{body}
  </main>
</body>
</html>
"""


def site_files(catalog, site_url):
    documents = {
        "README.md": ("index.html", catalog["name"], catalog["description"], "zh-CN"),
        "lean/README.md": ("lean/index.html", "Lean 形式化核验", "Lean 构建与核验记录。", "zh-CN"),
        "PUBLISHING.md": ("publishing.html", "发布指南", "数学成果和核验记录的发布流程。", "zh-CN"),
    }
    raw = {"LICENSE", "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json"}
    article_data = {}
    exported = json.loads(json.dumps(catalog))
    exported["site_url"] = site_url
    for result in exported["results"]:
        source = result["manuscript"]
        output = f"results/{result['id']}/index.html"
        documents[source] = (output, result["title"], result["description"], result["language"])
        result["url"] = site_url + output.removesuffix("index.html")
        result["markdown_url"] = site_url + quote(source)
        article_data[source] = {
            "@context": "https://schema.org",
            "@type": "ScholarlyArticle",
            "headline": result["title"],
            "alternativeHeadline": result["english_title"],
            "description": result["description"],
            "inLanguage": result["language"],
            "keywords": result["keywords"],
            "url": result["url"],
            "encoding": {
                "@type": "MediaObject",
                "contentUrl": result["markdown_url"],
                "encodingFormat": "text/markdown",
            },
        }
        if lean := result["lean"]:
            report = lean["verification"]
            report_html = report.removesuffix(".md") + ".html"
            documents[report] = (report_html, result["title"] + " · Lean 核验", LEAN_STATUS[lean["status"]], result["language"])
            lean["verification_url"] = site_url + quote(report_html)
            lean["entrypoint_url"] = site_url + quote(lean["entrypoint"])
            raw.add(lean["entrypoint"])
            for path in (ROOT / lean["source_directory"]).rglob("*.lean"):
                value = path.relative_to(ROOT).as_posix()
                source_path(value, PurePosixPath(lean["source_directory"]), ".lean")
                raw.add(value)
    raw.update(documents)
    files = {path: (ROOT / path).read_bytes() for path in raw}
    routes = {path: path for path in raw | {"catalog.json", "llms.txt"}}
    routes.update({source: output for source, (output, _, _, _) in documents.items()})
    routes.update({"readable": "index.html", "lean/verification": "lean/index.html"})
    sitemap = ET.Element("urlset", xmlns="http://www.sitemaps.org/schemas/sitemap/0.9")
    repo = (catalog["repository_url"].rstrip("/"), catalog["default_branch"])
    for source, (output, title, description, language) in documents.items():
        canonical = site_url + quote(output.removesuffix("index.html"))
        ET.SubElement(ET.SubElement(sitemap, "url"), "loc").text = canonical
        body = render_markdown(source, output, routes, repo)
        if article := article_data.get(source):
            markdown_link = href_between(output, source)
            body += f'\n<p><a href="{markdown_link}">下载原始 Markdown</a></p>'
        files[output] = html_document(title, description, language, canonical, output, body, catalog, article).encode("utf-8")
    files["catalog.json"] = (json.dumps(exported, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    files["llms.txt"] = text_index(catalog, site_url).encode("utf-8")
    files["sitemap.xml"] = ET.tostring(sitemap, encoding="utf-8", xml_declaration=True)
    files["style.css"] = (ROOT / "tools/style.css").read_bytes()
    files[".nojekyll"] = b""
    return files


def build(catalog, site_url):
    files = site_files(catalog, https_url(site_url or catalog["site_url"]))
    output = ROOT / "_site"
    marker = output / ".math-slop-build"
    if output.resolve() != output:
        raise ValueError("The _site output directory must be inside this repository")
    if output.exists():
        if not marker.is_file():
            raise ValueError("The existing _site directory was not created by this script")
        shutil.rmtree(output)
    output.mkdir()
    marker.touch()
    for name, content in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(f"Built {len(files)} files in {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["sync", "check", "build"])
    parser.add_argument("--site-url", help="Use the configured Pages URL in the exported site")
    args = parser.parse_args()
    try:
        catalog = load_catalog()
        sync_indexes(catalog, check=args.command != "sync")
        if args.command == "build":
            build(catalog, args.site_url)
    except (KeyError, OSError, ValueError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
