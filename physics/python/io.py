#!/usr/bin/env python3
import csv
import json
import os
from typing import List, Dict

import matplotlib.pyplot as plt


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def write_csv(path: str, rows: List[Dict], *, sort_keys: bool = True) -> None:
    if not rows:
        raise ValueError("rows must be non-empty")
    if sort_keys:
        keys = sorted({k for row in rows for k in row.keys()})
    else:
        keys = list(rows[0].keys())
    ensure_dir(os.path.dirname(path))
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=keys)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def save_plot(path: str) -> None:
    ensure_dir(os.path.dirname(path))
    plt.savefig(path, dpi=150, bbox_inches="tight")
    plt.close()


def load_manifest(manifest_path: str) -> Dict:
    if not os.path.exists(manifest_path):
        return {"artifacts": []}
    with open(manifest_path, "r", encoding="utf-8") as f:
        return json.load(f)


def update_manifest(manifest_path: str, entries: List[Dict]) -> None:
    data = load_manifest(manifest_path)
    artifacts = data.get("artifacts", [])
    by_path = {a.get("path"): a for a in artifacts if "path" in a}
    for entry in entries:
        path = entry.get("path")
        if not path:
            continue
        by_path[path] = entry
    data["artifacts"] = [by_path[k] for k in sorted(by_path.keys())]
    ensure_dir(os.path.dirname(manifest_path))
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
