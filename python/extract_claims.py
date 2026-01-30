#!/usr/bin/env python3
import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import sys
from typing import Dict, List, Optional, Tuple

BUILTIN_ENVS = {
    "definition",
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "remark",
}

SECTION_RE = re.compile(r"\\section\*?\{([^}]*)\}")
SUBSECTION_RE = re.compile(r"\\subsection\*?\{([^}]*)\}")
SUBSUBSECTION_RE = re.compile(r"\\subsubsection\*?\{([^}]*)\}")
NEWTHEOREM_RE = re.compile(r"\\newtheorem\{([^}]+)\}")
BEGIN_RE = re.compile(r"\\begin\{([^}]+)\}")
END_RE = re.compile(r"\\end\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def _sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _detect_source() -> str:
    if os.path.isfile("paper.tex"):
        return "paper.tex"
    if os.path.isfile("six-birds-paper.tex"):
        return "six-birds-paper.tex"
    raise SystemExit("No source file found. Expected paper.tex or six-birds-paper.tex")


def _build_context(section: Optional[str], subsection: Optional[str]) -> str:
    parts: List[str] = []
    if section:
        parts.append(section)
    if subsection:
        parts.append(subsection)
    return " > ".join(parts)


def _normalize_snippet(text: str, limit: int = 120) -> str:
    norm = re.sub(r"\s+", " ", text).strip()
    if len(norm) > limit:
        return norm[:limit]
    return norm


def _collect_envs(lines: List[str]) -> List[str]:
    envs = set(BUILTIN_ENVS)
    for line in lines:
        if line.lstrip().startswith("%"):
            continue
        for m in NEWTHEOREM_RE.finditer(line):
            env = m.group(1).strip()
            if env:
                envs.add(env)
    return sorted(envs)


def _parse_tex(lines: List[str], envs: List[str]) -> Tuple[List[Dict], Dict]:
    items: List[Dict] = []
    env_set = set(envs)

    section_title: Optional[str] = None
    subsection_title: Optional[str] = None

    current_env: Optional[Dict] = None
    current_env_body: List[str] = []

    for idx, line in enumerate(lines, start=1):
        if line.lstrip().startswith("%"):
            continue

        sec_m = SECTION_RE.search(line)
        if sec_m:
            section_title = sec_m.group(1).strip()
            subsection_title = None
            items.append({"kind": "section", "title": section_title, "line": idx})

        sub_m = SUBSECTION_RE.search(line)
        if sub_m:
            subsection_title = sub_m.group(1).strip()
            items.append({"kind": "subsection", "title": subsection_title, "line": idx})

        subsub_m = SUBSUBSECTION_RE.search(line)
        if subsub_m:
            subsection_title = subsub_m.group(1).strip()
            items.append({"kind": "subsection", "title": subsection_title, "line": idx})

        if current_env is None:
            begin_m = BEGIN_RE.search(line)
            if begin_m:
                env = begin_m.group(1).strip()
                if env in env_set:
                    current_env = {
                        "kind": "env",
                        "env": env,
                        "start_line": idx,
                        "end_line": None,
                        "label": None,
                        "snippet": "",
                        "context": _build_context(section_title, subsection_title),
                    }
                    after = line[begin_m.end():]
                    end_m = END_RE.search(after)
                    if end_m and end_m.group(1).strip() == env:
                        body = after[: end_m.start()]
                        if body.strip():
                            current_env_body.append(body)
                        current_env["end_line"] = idx
                        current_env["snippet"] = _normalize_snippet(" ".join(current_env_body))
                        items.append(current_env)
                        current_env = None
                        current_env_body = []
                    else:
                        if after.strip():
                            current_env_body.append(after)
        else:
            end_m = END_RE.search(line)
            if end_m and end_m.group(1).strip() == current_env["env"]:
                before = line[: end_m.start()]
                if before.strip():
                    current_env_body.append(before)
                current_env["end_line"] = idx
                current_env["snippet"] = _normalize_snippet(" ".join(current_env_body))
                items.append(current_env)
                current_env = None
                current_env_body = []
            else:
                current_env_body.append(line)

        if current_env is not None and current_env.get("label") is None:
            label_m = LABEL_RE.search(line)
            if label_m:
                current_env["label"] = label_m.group(1).strip()

    return items, _build_markdown_groups(items)


def _build_markdown_groups(items: List[Dict]) -> Dict:
    groups: Dict[str, Dict] = {}
    order: List[str] = []
    current_section = "(No section)"
    current_subsection: Optional[str] = None

    def ensure_section(title: str) -> None:
        nonlocal groups, order
        if title not in groups:
            groups[title] = {"envs": [], "subsections": {}, "suborder": []}
            order.append(title)

    ensure_section(current_section)

    for item in items:
        if item["kind"] == "section":
            current_section = item["title"]
            current_subsection = None
            ensure_section(current_section)
        elif item["kind"] == "subsection":
            current_subsection = item["title"]
            ensure_section(current_section)
            subs = groups[current_section]
            if current_subsection not in subs["subsections"]:
                subs["subsections"][current_subsection] = []
                subs["suborder"].append(current_subsection)
        elif item["kind"] == "env":
            ensure_section(current_section)
            if current_subsection:
                subs = groups[current_section]
                if current_subsection not in subs["subsections"]:
                    subs["subsections"][current_subsection] = []
                    subs["suborder"].append(current_subsection)
                subs["subsections"][current_subsection].append(item)
            else:
                groups[current_section]["envs"].append(item)

    return {"order": order, "groups": groups}


def _write_markdown(path: str, md_groups: Dict) -> None:
    lines: List[str] = []
    lines.append("# Claim Index")

    for sec in md_groups["order"]:
        lines.append("")
        lines.append(f"## {sec}")
        group = md_groups["groups"][sec]
        for env_item in group["envs"]:
            label = env_item.get("label") or "(no label)"
            snippet = env_item.get("snippet") or ""
            lines.append(
                f"- {env_item['env']} {label} (lines {env_item['start_line']}-{env_item['end_line']}): {snippet}"
            )
        for sub in group["suborder"]:
            lines.append("")
            lines.append(f"### {sub}")
            for env_item in group["subsections"][sub]:
                label = env_item.get("label") or "(no label)"
                snippet = env_item.get("snippet") or ""
                lines.append(
                    f"- {env_item['env']} {label} (lines {env_item['start_line']}-{env_item['end_line']}): {snippet}"
                )

    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines).rstrip() + "\n")


def _counts(items: List[Dict]) -> Dict:
    counts = {"section": 0, "subsection": 0, "env": 0, "env_types": {}}
    for item in items:
        kind = item.get("kind")
        if kind in counts:
            counts[kind] += 1
        if kind == "env":
            env = item.get("env")
            if env:
                counts["env_types"][env] = counts["env_types"].get(env, 0) + 1
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract sections and theorem-like environments from LaTeX.")
    parser.add_argument("--tex", default=None, help="Path to LaTeX source (default: auto-detect)")
    parser.add_argument("--out-json", default="artifacts/claims_index.json", help="JSON output path")
    parser.add_argument("--out-md", default="notes/claims_index.md", help="Markdown output path")
    args = parser.parse_args()

    source = args.tex or _detect_source()
    with open(source, "r", encoding="utf-8") as f:
        lines = f.readlines()

    envs = _collect_envs(lines)
    items, md_groups = _parse_tex(lines, envs)

    meta = {
        "source_file": source,
        "sha256": _sha256(source),
        "generated_at": _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "counts": _counts(items),
    }

    out = {"meta": meta, "items": items}

    os.makedirs(os.path.dirname(args.out_json), exist_ok=True)
    with open(args.out_json, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, sort_keys=True)

    _write_markdown(args.out_md, md_groups)


if __name__ == "__main__":
    main()
