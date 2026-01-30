#!/usr/bin/env python3
import json
import os
import sys


def main() -> int:
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    manifest_path = os.path.join(root, "physics", "artifacts", "manifest.json")
    required_path = os.path.join(
        root, "physics", "artifacts", "required_artifacts.txt"
    )

    if not os.path.exists(manifest_path):
        print("Missing manifest: physics/artifacts/manifest.json", file=sys.stderr)
        return 1
    if not os.path.exists(required_path):
        print(
            "Missing required list: physics/artifacts/required_artifacts.txt",
            file=sys.stderr,
        )
        return 1

    try:
        with open(manifest_path, "r", encoding="utf-8") as f:
            manifest = json.load(f)
    except Exception as e:
        print(f"Invalid manifest JSON: {e}", file=sys.stderr)
        return 1

    required = []
    with open(required_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            required.append(line)

    for rel in required:
        path = os.path.join(root, rel)
        if not os.path.exists(path) or os.path.getsize(path) == 0:
            print(f"Missing or empty artifact: {rel}", file=sys.stderr)
            return 1

    manifest_paths = {
        entry.get("path")
        for entry in manifest.get("artifacts", [])
        if entry.get("path")
    }
    for rel in required:
        if rel == "physics/artifacts/manifest.json":
            continue
        if rel not in manifest_paths:
            print(f"Required artifact not in manifest: {rel}", file=sys.stderr)
            return 1

    for entry in manifest.get("artifacts", []):
        rel = entry.get("path")
        if not rel:
            continue
        path = os.path.join(root, rel)
        if not os.path.exists(path) or os.path.getsize(path) == 0:
            print(f"Missing or empty artifact: {rel}", file=sys.stderr)
            return 1

    print("OK: physics artifacts verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
