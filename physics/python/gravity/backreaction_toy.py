#!/usr/bin/env python3
"""Nonlinear averaging vs dynamics (backreaction) toy demo."""
import csv
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def evolve_exact(y0: np.ndarray, t: float) -> np.ndarray:
    return y0 / (1.0 - t * y0)


def main(seed: int = 0, M: int = 20000) -> List[Dict]:
    rng = np.random.default_rng(seed)
    mu0 = 0.3
    s_list = np.linspace(0.0, 0.8, 9)
    t_list = np.linspace(0.0, 1.0, 101)

    rows: List[Dict] = []
    max_abs_by_s: Dict[float, float] = {}

    for s in s_list:
        z = rng.normal(size=M)
        z = np.clip(z, -3.0, 3.0)
        y0 = mu0 + s * z
        y0 = np.clip(y0, -0.8, 0.8)
        mean_y0 = float(np.mean(y0))

        max_abs = 0.0
        for t in t_list:
            y_micro = evolve_exact(y0, float(t))
            mean_micro = float(np.mean(y_micro))
            y_mean = float(mean_y0 / (1.0 - t * mean_y0))
            mismatch = mean_micro - y_mean
            abs_mismatch = abs(mismatch)
            max_abs = max(max_abs, abs_mismatch)
            rows.append(
                {
                    "seed": seed,
                    "M": M,
                    "mu0": mu0,
                    "s": float(s),
                    "t": float(t),
                    "mean_micro": mean_micro,
                    "y_mean": y_mean,
                    "mismatch": mismatch,
                    "abs_mismatch": abs_mismatch,
                }
            )
        max_abs_by_s[float(s)] = max_abs

    if max_abs_by_s.get(0.0, 1.0) > 1e-12:
        raise ValueError(f"s=0 mismatch too large: {max_abs_by_s[0.0]}")
    if max_abs_by_s[float(s_list[-1])] < 1e-4:
        raise ValueError("largest s mismatch too small")

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "gravity_backreaction.csv")
    png_path = os.path.join(artifacts_dir, "gravity_backreaction.png")

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "seed",
                "M",
                "mu0",
                "s",
                "t",
                "mean_micro",
                "y_mean",
                "mismatch",
                "abs_mismatch",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7, 4))
    for s in s_list:
        ts = [r["t"] for r in rows if r["s"] == float(s)]
        abs_ms = [r["abs_mismatch"] for r in rows if r["s"] == float(s)]
        plt.plot(ts, abs_ms, label=f"s={s:.1f}")
    plt.xlabel("t")
    plt.ylabel("abs mismatch")
    plt.title(f"Backreaction toy (mu0={mu0}, M={M})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(png_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/gravity_backreaction.csv",
            "kind": "csv",
            "desc": "Backreaction toy mismatch over time",
            "created_by": "physics/python/gravity/backreaction_toy.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/gravity_backreaction.png",
            "kind": "png",
            "desc": "Backreaction toy abs mismatch vs time",
            "created_by": "physics/python/gravity/backreaction_toy.py",
            "seed": seed,
        },
    ]
    return entries


if __name__ == "__main__":
    main()
