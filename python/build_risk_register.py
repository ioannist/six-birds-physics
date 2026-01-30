#!/usr/bin/env python3
import datetime as _dt
import hashlib
import json
import os
import re
import sys
from typing import Dict, List, Tuple

REF_RE = re.compile(r"\\(?:ref|eqref|autoref|cref|Cref)\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{[^}]+\}")

PROOF_HYBRID_PATTERNS = [
    re.compile(r"\bkl\b"),
    re.compile(r"relative entropy"),
    re.compile(r"data processing"),
    re.compile(r"\btv\b"),
    re.compile(r"total variation"),
]
PROOF_MANUAL_PATTERNS = [
    re.compile(r"forcing"),
    re.compile(r"definable"),
    re.compile(r"generic extension"),
]
PROOF_PY_PATTERNS = [
    re.compile(r"approximate"),
    re.compile(r"error bound"),
    re.compile(r"defect"),
    re.compile(r"retention"),
]

RISK_KEYWORDS: List[Tuple[str, re.Pattern]] = [
    ("assume", re.compile(r"\bassum")),
    ("bound", re.compile(r"\bbound\b")),
    ("rate", re.compile(r"\brate\b")),
    ("finite", re.compile(r"\bfinite\b")),
    ("constant", re.compile(r"\bconstant\b")),
    ("approx", re.compile(r"\bapprox")),
    ("error", re.compile(r"\berror\b")),
    ("inequality", re.compile(r"\binequality\b")),
    ("stability", re.compile(r"\bstability\b")),
    ("decay", re.compile(r"\bdecay\b")),
    ("coupling", re.compile(r"\bcoupling\b")),
    ("entropy", re.compile(r"\bentropy\b")),
    ("probability", re.compile(r"\bprobability\b")),
    ("limit", re.compile(r"\blimit\b")),
    ("tail", re.compile(r"\btail\b")),
    ("open", re.compile(r"\bopen\b")),
    ("numerical", re.compile(r"\bnumerical\b")),
    ("simulation", re.compile(r"\bsimulat")),
    ("heuristic", re.compile(r"\bheuristic\b")),
    ("defect", re.compile(r"\bdefect\b")),
    ("retention", re.compile(r"\bretention\b")),
]


def _sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_json(path: str) -> Dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def _normalize_snippet(snippet: str, limit: int = 60) -> str:
    if not snippet:
        return ""
    cleaned = LABEL_RE.sub("", snippet)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    if len(cleaned) > limit:
        return cleaned[:limit].rstrip() + "..."
    return cleaned


def _escape_cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ").strip()


def _extract_refs(text: str, cap: int = 8) -> str:
    seen = set()
    ordered: List[str] = []
    for m in REF_RE.finditer(text):
        label = m.group(1).strip()
        if label and label not in seen:
            seen.add(label)
            ordered.append(label)
    if not ordered:
        return ""
    if len(ordered) > cap:
        return ", ".join(ordered[:cap]) + ", ..."
    return ", ".join(ordered)


def _proof_mode(text: str) -> str:
    lower = text.lower()
    if any(p.search(lower) for p in PROOF_HYBRID_PATTERNS):
        return "Hybrid"
    if any(p.search(lower) for p in PROOF_MANUAL_PATTERNS):
        return "Manual"
    if any(p.search(lower) for p in PROOF_PY_PATTERNS):
        return "Python"
    return "Manual"


def _risk_level(text: str) -> Tuple[str, List[str]]:
    lower = text.lower()
    flags: List[str] = []
    for name, pat in RISK_KEYWORDS:
        if pat.search(lower):
            flags.append(name)
    if len(flags) > 8:
        flags = flags[:8] + ["..."]
    score = len(flags)
    if score >= 3:
        level = "High"
    elif score > 0:
        level = "Med"
    else:
        level = "Low"
    return level, flags


def _get_env_text(lines: List[str], start: int, end: int) -> str:
    if start < 1 or end < start or end > len(lines):
        return ""
    return "".join(lines[start - 1 : end])


def main() -> None:
    source_file = "paper.tex" if os.path.isfile("paper.tex") else "six-birds-paper.tex"
    if not os.path.isfile(source_file):
        print("Missing source file (paper.tex or six-birds-paper.tex)", file=sys.stderr)
        sys.exit(1)

    integrity = _load_json("artifacts/source_integrity.json")
    expected_sha = integrity.get("sha256")
    actual_sha = _sha256(source_file)
    if expected_sha != actual_sha:
        print("Source integrity check failed: SHA256 mismatch", file=sys.stderr)
        sys.exit(1)

    claims = _load_json("artifacts/claims_index.json")
    items = [i for i in claims.get("items", []) if i.get("kind") == "env"]

    with open(source_file, "r", encoding="utf-8") as f:
        lines = f.readlines()

    section_order: List[str] = []
    grouped: Dict[str, List[Dict]] = {}

    rows: List[Dict] = []
    for item in items:
        env = item.get("env", "")
        start_line = int(item.get("start_line", 0))
        end_line = int(item.get("end_line", 0))
        label = item.get("label") or ""
        claim_id = label if label else f"{env}@L{start_line}"

        env_text = _get_env_text(lines, start_line, end_line)
        refs = _extract_refs(env_text)
        informal = _normalize_snippet(item.get("snippet", ""))
        if not informal:
            informal = env

        proof = _proof_mode(env_text)
        risk, flags = _risk_level(env_text)

        context = item.get("context") or ""
        section = context.split(" > ")[0].strip() if context else "(No section)"
        if not section:
            section = "(No section)"

        row = {
            "section": section,
            "claim_id": claim_id,
            "informal": informal,
            "depends": refs,
            "proof": proof,
            "risk": risk,
            "context": context if context else "(No section)",
            "flags": flags,
            "env": env,
        }
        rows.append(row)

        if section not in grouped:
            grouped[section] = []
            section_order.append(section)
        grouped[section].append(row)

    out_lines: List[str] = []
    out_lines.append("# Risk Register")
    out_lines.append("")
    out_lines.append(f"Generated at: {_dt.datetime.utcnow().replace(microsecond=0).isoformat()}Z")

    header = (
        "| Claim ID / label | Informal name | Depends on (IDs) | "
        "Proof mode: Lean / Python / manual / hybrid | "
        "Risk level: Low/Med/High/Unknown | Notes / suspected weak points |"
    )
    sep = "| --- | --- | --- | --- | --- | --- |"

    for section in section_order:
        out_lines.append("")
        out_lines.append(f"## {section}")
        out_lines.append(header)
        out_lines.append(sep)
        for row in grouped[section]:
            flags = ", ".join(row["flags"]) if row["flags"] else "none"
            notes = f"context: {row['context']}; flags: {flags}; env: {row['env']}"
            out_lines.append(
                "| "
                + " | ".join(
                    [
                        _escape_cell(row["claim_id"]),
                        _escape_cell(row["informal"]),
                        _escape_cell(row["depends"]),
                        _escape_cell(row["proof"]),
                        _escape_cell(row["risk"]),
                        _escape_cell(notes),
                    ]
                )
                + " |"
            )

    os.makedirs("notes", exist_ok=True)
    with open("notes/risk_register.md", "w", encoding="utf-8") as f:
        f.write("\n".join(out_lines).rstrip() + "\n")


if __name__ == "__main__":
    main()
