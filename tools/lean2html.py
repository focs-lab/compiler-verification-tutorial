#!/usr/bin/env python3
"""
lean2html -- render Lean 4 sources as pretty-printed, cross-referenced HTML.

The Lean counterpart of the `coq2html` tool used by the original Coq course:
doc comments (`/-! ... -/` and `/-- ... -/`) become prose, code becomes
syntax-highlighted blocks, and top-level declarations get anchors.

Usage:  python3 tools/lean2html.py OUTDIR FILE.lean [FILE.lean ...]
"""

import html
import os
import re
import sys

KEYWORDS = {
    "abbrev", "attribute", "at", "by", "calc", "cases", "class", "def",
    "deriving", "do", "else", "end", "example", "exact", "exists", "extends",
    "for", "from", "fun", "generalizing", "have", "if", "import", "in",
    "inductive", "instance", "intro", "let", "match", "mutual", "namespace",
    "noncomputable", "obtain", "open", "partial", "private", "protected",
    "rcases", "refine", "rfl", "rintro", "section", "set_option", "show",
    "simp", "sorry", "structure", "termination_by", "decreasing_by", "then",
    "theorem", "this", "universe", "unless", "using", "variable", "where",
    "while", "with", "return", "omega", "grind", "induction", "subst",
    "apply", "constructor", "refold", "trivial", "assumption", "nomatch",
}

DECL_KEYWORDS = ("theorem", "def", "abbrev", "inductive", "structure",
                 "instance", "class", "example", "opaque", "axiom")

IDENT = re.compile(r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'!?₀-₉¹²³.α-ω]*")


# --------------------------------------------------------------------------
# Splitting a file into doc blocks and code blocks
# --------------------------------------------------------------------------

def split_source(src):
    """Yield ('moddoc'|'decldoc'|'code'|'header', text) segments."""
    out = []
    i, n = 0, len(src)
    code_start = 0

    def flush_code(upto):
        if upto > code_start:
            chunk = src[code_start:upto]
            if chunk.strip():
                out.append(("code", chunk))

    # A leading /- ... -/ block (not /-! or /--) is the licence header.
    m = re.match(r"\s*/-(?![!-])(.*?)-/", src, re.S)
    if m:
        out.append(("header", m.group(1).strip("\n")))
        i = code_start = m.end()

    while i < n:
        if src.startswith("/-!", i):
            flush_code(i)
            j = find_close(src, i)
            out.append(("moddoc", src[i + 3:j].strip()))
            i = code_start = j + 2
        elif src.startswith("/--", i):
            flush_code(i)
            j = find_close(src, i)
            out.append(("decldoc", src[i + 3:j].strip()))
            i = code_start = j + 2
        elif src.startswith("/-", i):
            j = find_close(src, i)
            i = j + 2
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
        else:
            i += 1
    flush_code(n)
    return out


def find_close(src, i):
    """Index of the '-/' closing the block comment opening at i (nested-aware)."""
    depth, j, n = 0, i, len(src)
    while j < n:
        if src.startswith("/-", j):
            depth += 1
            j += 2
        elif src.startswith("-/", j):
            depth -= 1
            if depth == 0:
                return j
            j += 2
        else:
            j += 1
    return n


# --------------------------------------------------------------------------
# Markdown-ish rendering of doc comments
# --------------------------------------------------------------------------

def inline(text):
    text = html.escape(text)
    spans = []

    def stash(m):
        spans.append(m.group(1))
        return "\x00%d\x00" % (len(spans) - 1)

    text = re.sub(r"`([^`]+)`", stash, text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<!\w)\*([^*\n]+)\*(?!\w)", r"<em>\1</em>", text)
    text = re.sub(r"&lt;(https?://[^&\s]+)&gt;", r'<a href="\1">\1</a>', text)
    text = re.sub(r"\x00(\d+)\x00",
                  lambda m: "<code>%s</code>" % spans[int(m.group(1))], text)
    return text


def render_doc(text):
    """Render a doc comment (a small subset of Markdown) to HTML."""
    lines = text.split("\n")
    out, i, n = [], 0, len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()
        if not s:
            i += 1
            continue
        m = re.match(r"^(#{1,4})\s+(.*)$", s)
        if m:
            lvl = min(len(m.group(1)) + 1, 5)
            anchor = re.sub(r"[^a-z0-9]+", "-", m.group(2).lower()).strip("-")
            out.append('<h%d id="sec-%s">%s</h%d>'
                       % (lvl, anchor, inline(m.group(2)), lvl))
            i += 1
            continue
        if re.match(r"^[*-]\s+", s):
            items = []
            while i < n and (re.match(r"^\s*[*-]\s+", lines[i])
                             or (lines[i].startswith("  ") and lines[i].strip()
                                 and items)):
                if re.match(r"^\s*[*-]\s+", lines[i]):
                    items.append(re.sub(r"^\s*[*-]\s+", "", lines[i]))
                else:
                    items[-1] += " " + lines[i].strip()
                i += 1
            out.append("<ul>%s</ul>"
                       % "".join("<li>%s</li>" % inline(x) for x in items))
            continue
        if line.startswith("    ") or line.startswith("```"):
            block = []
            if line.startswith("```"):
                i += 1
                while i < n and not lines[i].startswith("```"):
                    block.append(lines[i])
                    i += 1
                i += 1
            else:
                while i < n and (lines[i].startswith("    ") or not lines[i].strip()):
                    block.append(lines[i][4:])
                    i += 1
                while block and not block[-1].strip():
                    block.pop()
            out.append('<pre class="doccode">%s</pre>'
                       % highlight("\n".join(block))[0])
            continue
        para = []
        while i < n and lines[i].strip() and not re.match(r"^(#{1,4}\s|\s*[*-]\s|```)", lines[i]) \
                and not lines[i].startswith("    "):
            para.append(lines[i].strip())
            i += 1
        out.append("<p>%s</p>" % inline(" ".join(para)))
    return "\n".join(out)


# --------------------------------------------------------------------------
# Syntax highlighting
# --------------------------------------------------------------------------

def highlight(code, anchors=None):
    """Return (html, [(name, kind)]) for a chunk of Lean code."""
    out, decls = [], []
    i, n = 0, len(code)
    at_decl = None
    while i < n:
        ch = code[i]
        if code.startswith("--", i):
            j = code.find("\n", i)
            j = n if j < 0 else j
            out.append('<span class="c">%s</span>' % html.escape(code[i:j]))
            i = j
        elif code.startswith("/-", i):
            j = find_close(code, i) + 2
            out.append('<span class="c">%s</span>' % html.escape(code[i:j]))
            i = j
        elif ch == '"':
            j = i + 1
            while j < n and code[j] != '"':
                j += 2 if code[j] == "\\" else 1
            j += 1
            out.append('<span class="s">%s</span>' % html.escape(code[i:j]))
            i = j
        else:
            m = IDENT.match(code, i)
            if m:
                word = m.group(0)
                if word in KEYWORDS:
                    out.append('<span class="k">%s</span>' % html.escape(word))
                    at_decl = word if word in DECL_KEYWORDS else None
                elif at_decl:
                    name = word
                    decls.append((name, at_decl))
                    if anchors is not None:
                        out.append('<span class="d" id="%s">'
                                   '<a class="anchor" href="#%s">%s</a></span>'
                                   % (html.escape(name), html.escape(name),
                                      html.escape(name)))
                    else:
                        out.append('<span class="d">%s</span>' % html.escape(name))
                    at_decl = None
                else:
                    out.append(html.escape(word))
                i = m.end()
            else:
                if ch not in " \t\n" and ch != "@":
                    at_decl = at_decl if ch in "{}[]()" else at_decl
                out.append(html.escape(ch))
                i += 1
    return "".join(out), decls


# --------------------------------------------------------------------------
# Page assembly
# --------------------------------------------------------------------------

PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{module}</title>
<link rel="stylesheet" href="lean2html.css">
</head>
<body>
<div class="nav">
<a href="../index.html">Course page</a>
{prevnext}
</div>
<h1 class="modname">{module}</h1>
{toc}
<div class="content">
{body}
</div>
<div class="footer">
Generated by <code>tools/lean2html.py</code> from <code>{src}</code>.
</div>
</body>
</html>
"""


def module_name(path):
    rel = os.path.relpath(path).replace(os.sep, ".")
    return rel[:-5] if rel.endswith(".lean") else rel


def render_file(path, prev, nxt):
    src = open(path, encoding="utf-8").read()
    mod = module_name(path)
    segments = split_source(src)

    body, toc, pending = [], [], None
    codebuf = []

    def flush_code():
        if codebuf:
            body.append('<pre class="code">%s</pre>' % "\n".join(codebuf))
            del codebuf[:]

    for kind, text in segments:
        if kind == "header":
            flush_code()
            body.append('<div class="license">%s</div>'
                        % html.escape(text).replace("\n", "<br>"))
        elif kind == "moddoc":
            flush_code()
            for m in re.finditer(r"^(#{1,4})\s+(.*)$", text, re.M):
                anchor = re.sub(r"[^a-z0-9]+", "-", m.group(2).lower()).strip("-")
                toc.append((len(m.group(1)), m.group(2), anchor))
            body.append('<div class="doc">%s</div>' % render_doc(text))
        elif kind == "decldoc":
            pending = text
        elif kind == "code":
            stripped = "\n".join(l.rstrip() for l in text.split("\n")).strip("\n")
            if not stripped.strip():
                continue
            indented = bool(re.match(r"^\s+\S", stripped))
            if pending is not None:
                if indented and codebuf:
                    # A doc comment on a constructor or field: keep it inside
                    # the surrounding code block rather than breaking it apart.
                    indent = re.match(r"^(\s*)", stripped).group(1)
                    oneline = " ".join(pending.split())
                    codebuf.append('<span class="c">%s-- %s</span>'
                                   % (indent, html.escape(oneline)))
                else:
                    flush_code()
                    body.append('<div class="doc decl">%s</div>' % render_doc(pending))
                pending = None
            code_html, _ = highlight(stripped, anchors=True)
            codebuf.append(code_html)
    flush_code()

    toc_html = ""
    if toc:
        items = "".join('<li class="l%d"><a href="#sec-%s">%s</a></li>'
                        % (lvl, a, html.escape(t)) for lvl, t, a in toc)
        toc_html = '<div class="toc"><b>Contents</b><ul>%s</ul></div>' % items

    links = []
    if prev:
        links.append('<a href="%s.html">&larr; %s</a>' % (prev, prev))
    if nxt:
        links.append('<a href="%s.html">%s &rarr;</a>' % (nxt, nxt))
    prevnext = ('<span class="prevnext">%s</span>' % " &nbsp; ".join(links)) if links else ""

    return PAGE.format(module=mod, body="\n".join(body), toc=toc_html,
                       src=os.path.relpath(path), prevnext=prevnext)


CSS = """
:root { --fg:#1b1b1b; --muted:#666; --rule:#dcdcdc; --bg:#fff;
        --codebg:#f7f7f4; --kw:#0059a0; --cmt:#6e6e6e; --str:#a03c14;
        --decl:#7a2f8f; --link:#0b5fa5; }
* { box-sizing: border-box; }
body { margin:0 auto; max-width:52em; padding:1.5em 1.5em 4em;
       background:var(--bg); color:var(--fg);
       font:16px/1.55 Georgia, "Times New Roman", serif; }
a { color:var(--link); }
.nav { font:13px/1.4 -apple-system, "Helvetica Neue", Arial, sans-serif;
       padding-bottom:.6em; border-bottom:1px solid var(--rule);
       margin-bottom:1.4em; display:flex; justify-content:space-between; }
.prevnext a { margin-left:1em; }
h1.modname { font:600 26px/1.2 -apple-system,"Helvetica Neue",Arial,sans-serif;
             margin:.2em 0 1em; }
.doc h2 { font:600 21px/1.3 -apple-system,"Helvetica Neue",Arial,sans-serif;
          margin:1.8em 0 .5em; padding-top:.3em; border-top:1px solid var(--rule); }
.doc h3 { font:600 17px/1.3 -apple-system,"Helvetica Neue",Arial,sans-serif;
          margin:1.4em 0 .4em; }
.doc h4 { font:600 15px/1.3 -apple-system,"Helvetica Neue",Arial,sans-serif;
          margin:1.2em 0 .3em; }
.doc p { margin:.65em 0; }
.doc.decl { margin-top:1.6em; color:#2a2a2a; }
.doc.decl p:first-child { margin-top:0; }
.toc { background:#fafaf8; border:1px solid var(--rule); border-radius:4px;
       padding:.8em 1.2em; margin-bottom:2em;
       font:14px/1.5 -apple-system,"Helvetica Neue",Arial,sans-serif; }
.toc ul { list-style:none; padding-left:0; margin:.4em 0 0; }
.toc li.l2 { margin-left:0; } .toc li.l3 { margin-left:1.2em; }
.toc li.l4 { margin-left:2.4em; font-size:.95em; }
pre { overflow-x:auto; }
pre.code { background:var(--codebg); border:1px solid var(--rule);
           border-radius:4px; padding:.7em .9em; margin:.7em 0 1.1em;
           font:13.5px/1.5 "DejaVu Sans Mono", Menlo, Consolas, monospace; }
pre.doccode { background:#f2f2ef; border-left:3px solid #ccc; padding:.5em .8em;
              margin:.7em 0; font:13px/1.45 "DejaVu Sans Mono",Menlo,monospace; }
code { background:var(--codebg); border-radius:3px; padding:.08em .3em;
       font:.88em/1.4 "DejaVu Sans Mono", Menlo, Consolas, monospace; }
pre code { background:none; padding:0; }
.k { color:var(--kw); font-weight:600; }
.c { color:var(--cmt); font-style:italic; }
.s { color:var(--str); }
.d { color:var(--decl); font-weight:600; }
.d a.anchor { color:inherit; text-decoration:none; }
.d a.anchor:hover { text-decoration:underline; }
.license { color:var(--muted); font-size:12.5px; line-height:1.45;
           border-left:3px solid var(--rule); padding:.5em .9em; margin-bottom:2em;
           font-family:-apple-system,"Helvetica Neue",Arial,sans-serif; }
.footer { margin-top:3em; padding-top:.8em; border-top:1px solid var(--rule);
          color:var(--muted); font-size:12.5px;
          font-family:-apple-system,"Helvetica Neue",Arial,sans-serif; }
ul { padding-left:1.4em; }
@media (prefers-color-scheme: dark) {
  :root { --fg:#e6e6e6; --muted:#9a9a9a; --rule:#3a3a3a; --bg:#191919;
          --codebg:#212121; --kw:#6fb3ee; --cmt:#9a9a9a; --str:#e0916a;
          --decl:#cf9ae0; --link:#78b7f0; }
  .toc { background:#1f1f1f; }
  pre.doccode { background:#202020; border-left-color:#444; }
}
"""


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    outdir, files = sys.argv[1], sys.argv[2:]
    os.makedirs(outdir, exist_ok=True)
    mods = [module_name(f) for f in files]
    for idx, path in enumerate(files):
        prev = mods[idx - 1] if idx > 0 else None
        nxt = mods[idx + 1] if idx + 1 < len(mods) else None
        page = render_file(path, prev, nxt)
        dest = os.path.join(outdir, mods[idx] + ".html")
        open(dest, "w", encoding="utf-8").write(page)
        print("wrote", dest)
    open(os.path.join(outdir, "lean2html.css"), "w", encoding="utf-8").write(CSS)
    print("wrote", os.path.join(outdir, "lean2html.css"))


if __name__ == "__main__":
    main()
