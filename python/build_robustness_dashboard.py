#!/usr/bin/env python3
import hashlib
import json
import os
import re
import sys
from collections import Counter
from typing import Dict, List, Tuple


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def split_row(line: str) -> List[str]:
    parts = [p.strip() for p in re.split(r"(?<!\\)\|", line)]
    if parts and parts[0] == "":
        parts = parts[1:]
    if parts and parts[-1] == "":
        parts = parts[:-1]
    return parts


def is_separator_row(cols: List[str]) -> bool:
    if not cols:
        return False
    return all(re.fullmatch(r"-+", c) is not None for c in cols)


def extract_field(notes: str, key: str) -> str:
    m = re.search(rf"{re.escape(key)}\s*:\s*([^;]*)", notes)
    if not m:
        return ""
    return m.group(1).strip()


def parse_flags(notes: str) -> List[str]:
    val = extract_field(notes, "flags")
    if not val or val.lower() == "none":
        return []
    return [v.strip() for v in val.split(",") if v.strip()]


def update_status(notes: str, statuses: List[str]) -> str:
    status_val = ", ".join(statuses)
    if re.search(r"status\s*:", notes):
        return re.sub(r"status\s*:\s*[^;]*", f"status: {status_val}", notes)
    if notes.strip() == "":
        return f"status: {status_val}"
    return f"{notes}; status: {status_val}"


def main() -> int:
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    risk_path = os.path.join(root, "notes", "risk_register.md")
    dashboard_path = os.path.join(root, "notes", "robustness_dashboard.md")
    integrity_path = os.path.join(root, "artifacts", "source_integrity.json")
    source_path = os.path.join(root, "paper.tex")

    with open(integrity_path, "r", encoding="utf-8") as f:
        integrity = json.load(f)
    expected = integrity.get("sha256")
    actual = sha256_file(source_path)
    if expected != actual:
        print("Source integrity check failed: SHA256 mismatch", file=sys.stderr)
        return 1

    with open(risk_path, "r", encoding="utf-8") as f:
        lines = f.read().splitlines()

    updated_lines: List[str] = []
    claim_status: Dict[str, Dict[str, object]] = {}
    status_counts: Counter = Counter()
    high_risk_watch: List[Tuple[str, List[str], str]] = []
    high_risk_gaps: List[Tuple[str, List[str], str, str]] = []

    for line in lines:
        if not line.startswith("|"):
            updated_lines.append(line)
            continue
        cols = split_row(line)
        if len(cols) < 6:
            updated_lines.append(line)
            continue
        if "Claim ID / label" in line:
            updated_lines.append(line)
            continue
        if is_separator_row(cols):
            updated_lines.append(line)
            continue

        claim_id = cols[0].strip()
        informal = cols[1].strip()
        risk_level = cols[4].strip()
        notes = cols[5].strip()

        informal_l = informal.lower()
        claim_l = claim_id.lower()
        context = extract_field(notes, "context")
        context_l = context.lower()

        statuses = set()

        if any(k in context_l for k in ["arrow-of-time", "relative entropy", "data processing"]):
            statuses.add("Sim:DPI")
        if any(k in context_l for k in ["idempotent endomaps", "closure", "toolkit theory---defects"]):
            statuses.add("Sim:Idempotence")
        if any(k in context_l for k in ["forcing", "generic extension"]):
            statuses.add("Sim:Definability")

        if (
            any(k in claim_l for k in ["route", "mismatch", "commut", "non-section"])
            or any(k in informal_l for k in ["route", "mismatch", "commut", "non-section"])
            or "order-closure" in context_l
        ):
            statuses.add("CE:FailureModes")

        if any(k in context_l for k in ["coarse-graining lenses", "idempotent endomaps"]):
            statuses.add("Lean:Core")
        if any(k in context_l for k in ["arrow-of-time", "idempotent endomaps"]):
            statuses.add("Lean:Stub")

        if not statuses:
            statuses = {"Unknown"}

        statuses_sorted = sorted(statuses)
        notes = update_status(notes, statuses_sorted)
        cols[5] = notes

        updated_lines.append("| " + " | ".join(cols) + " |")

        for s in statuses_sorted:
            status_counts[s] += 1

        claim_status[claim_id] = {
            "risk_level": risk_level,
            "statuses": statuses_sorted,
            "context": context,
        }

        if risk_level == "High":
            high_risk_watch.append((claim_id, statuses_sorted, context))
            has_sim = any(s.startswith("Sim:") for s in statuses_sorted)
            has_lean = any(s.startswith("Lean:") for s in statuses_sorted)
            has_ce = "CE:FailureModes" in statuses_sorted
            is_unknown = statuses_sorted == ["Unknown"]
            if is_unknown:
                priority = 0
                missing_note = "missing: unknown"
            elif not has_sim:
                priority = 1
                missing_note = "missing: no sim tag"
            elif not has_lean:
                priority = 2
                missing_note = "missing: no lean tag"
            elif has_ce:
                priority = 3
                missing_note = "missing: counterexample-known"
            else:
                priority = 4
                missing_note = "missing: (none)"
            reason = f"context: {context}" if context else "context: (none)"
            reason = f"{reason}; {missing_note}"
            high_risk_gaps.append((claim_id, statuses_sorted, reason, str(priority)))

    with open(risk_path, "w", encoding="utf-8") as f:
        f.write("\n".join(updated_lines).rstrip() + "\n")

    # Dashboard
    evidence_lines = [
        "# Math robustness dashboard",
        "",
        "## Evidence assets",
        "- Lean modules:",
        "  - lean/EmergenceCalc/Emergence/Lens.lean — Q_f, Q_f_pure, Q_id, Q_comp",
        "  - lean/EmergenceCalc/Emergence/Completion.lean — SectionAxiom, E, E_idempotent",
        "  - lean/EmergenceCalc/Emergence/RouteMismatch.lean — routeMismatch, Commutes, commutes_of_intertwine",
        "  - lean/EmergenceCalc/Emergence/Info.lean — KL wrapper; DPI_KL_Qf (Prop + TODO)",
        "- Simulation assets:",
        "  - artifacts/dpi_kl_summary.csv; artifacts/dpi_kl_hist.png",
        "  - artifacts/idempotence_defect_summary.csv; artifacts/idempotence_defect.png",
        "  - artifacts/failure_modes.csv; artifacts/failure_modes.png; notes/failure_modes.md",
        "  - artifacts/definability_ratio.csv; artifacts/definability_ratio.png",
        "",
        "## Status counts",
    ]

    for key in [
        "Sim:DPI",
        "Sim:Idempotence",
        "Sim:Definability",
        "CE:FailureModes",
        "Lean:Core",
        "Lean:Stub",
        "Unknown",
    ]:
        evidence_lines.append(f"- {key}: {status_counts.get(key, 0)}")

    evidence_lines.append("")
    evidence_lines.append("## High-risk claim watchlist")
    if high_risk_watch:
        for claim_id, statuses_sorted, context in high_risk_watch:
            evidence_lines.append(f"- {claim_id} — {', '.join(statuses_sorted)} — {context}")
    else:
        evidence_lines.append("- (none)")

    evidence_lines.append("")
    evidence_lines.append("## Top 5 remaining high-risk gaps")
    if high_risk_gaps:
        high_risk_gaps.sort(key=lambda t: (int(t[3]), t[0]))
        for claim_id, statuses_sorted, reason, _ in high_risk_gaps[:5]:
            evidence_lines.append(f"- {claim_id} — {reason}")
    else:
        evidence_lines.append("- (none)")

    with open(dashboard_path, "w", encoding="utf-8") as f:
        f.write("\n".join(evidence_lines).rstrip() + "\n")

    claim_status_path = os.path.join(root, "artifacts", "claim_status.json")
    with open(claim_status_path, "w", encoding="utf-8") as f:
        json.dump(claim_status, f, indent=2, sort_keys=True)

    print("OK: robustness dashboard built")
    return 0


if __name__ == "__main__":
    sys.exit(main())
