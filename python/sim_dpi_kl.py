#!/usr/bin/env python3
import csv
import math
import os
import sys
from dataclasses import dataclass
from typing import Dict, List, Tuple

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


@dataclass
class SummaryRow:
    n: int
    m: int
    sparsity: float
    trials: int
    eps: float
    tol: float
    min_diff: float
    violations: int


def random_prob(n: int, rng: np.random.Generator) -> np.ndarray:
    return rng.dirichlet(np.ones(n))


def random_stochastic(n: int, m: int, rng: np.random.Generator, sparsity: float) -> np.ndarray:
    mat = rng.random((n, m))
    if sparsity > 0:
        mask = rng.random((n, m)) < sparsity
        mat = mat * (~mask)
        for i in range(n):
            if np.all(mat[i] == 0):
                j = rng.integers(0, m)
                mat[i, j] = 1.0
    row_sums = mat.sum(axis=1, keepdims=True)
    mat = mat / row_sums
    return mat


def smooth(p: np.ndarray, eps: float) -> np.ndarray:
    return (p + eps) / (p.sum() + eps * p.size)


def kl(p: np.ndarray, q: np.ndarray) -> float:
    return float(np.sum(p * np.log(p / q)))


def main() -> int:
    rng = np.random.default_rng(20250126)
    eps = 1e-12
    tol = 1e-10

    sizes: List[Tuple[int, int]] = [
        (2, 2),
        (3, 3),
        (5, 5),
        (10, 10),
        (20, 20),
        (20, 10),
        (50, 20),
    ]
    sparsities = [0.0, 0.5, 0.8]
    trials_per = 300

    artifacts_dir = os.path.join(os.path.dirname(__file__), "..", "artifacts")
    artifacts_dir = os.path.abspath(artifacts_dir)
    os.makedirs(artifacts_dir, exist_ok=True)

    trials_path = os.path.join(artifacts_dir, "dpi_kl_trials.csv")
    summary_path = os.path.join(artifacts_dir, "dpi_kl_summary.csv")
    hist_path = os.path.join(artifacts_dir, "dpi_kl_hist.png")

    diffs: List[float] = []
    summaries: Dict[Tuple[int, int, float], SummaryRow] = {}
    violations_global = 0
    diff_min = math.inf

    with open(trials_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["seed", "trial_id", "n", "m", "sparsity", "eps", "kl_in", "kl_out", "diff"])
        trial_id = 0
        for n, m in sizes:
            for sparsity in sparsities:
                key = (n, m, sparsity)
                summaries[key] = SummaryRow(
                    n=n,
                    m=m,
                    sparsity=sparsity,
                    trials=0,
                    eps=eps,
                    tol=tol,
                    min_diff=math.inf,
                    violations=0,
                )
                for _ in range(trials_per):
                    trial_id += 1
                    p = random_prob(n, rng)
                    q = random_prob(n, rng)
                    K = random_stochastic(n, m, rng, sparsity)

                    pin = smooth(p, eps)
                    qin = smooth(q, eps)
                    pout = smooth(pin @ K, eps)
                    qout = smooth(qin @ K, eps)

                    kl_in = kl(pin, qin)
                    kl_out = kl(pout, qout)
                    diff = kl_in - kl_out

                    diffs.append(diff)
                    diff_min = min(diff_min, diff)

                    row = summaries[key]
                    row.trials += 1
                    row.min_diff = min(row.min_diff, diff)
                    if diff < -tol:
                        row.violations += 1
                        violations_global += 1

                    writer.writerow([20250126, trial_id, n, m, sparsity, eps, kl_in, kl_out, diff])

    with open(summary_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "m", "sparsity", "trials", "eps", "tol", "min_diff", "violations"])
        for key in sorted(summaries.keys()):
            row = summaries[key]
            writer.writerow([row.n, row.m, row.sparsity, row.trials, row.eps, row.tol, row.min_diff, row.violations])

    plt.figure(figsize=(8, 4.5))
    plt.hist(diffs, bins=60, color="#1f77b4", edgecolor="black", linewidth=0.4)
    plt.xlabel("diff = KL(p||q) - KL(pK||qK)")
    plt.ylabel("count")
    plt.title(f"DPI KL diffs (min={diff_min:.3e}, tol={tol:.1e})")
    plt.tight_layout()
    plt.savefig(hist_path, dpi=150)
    plt.close()

    total_trials = len(diffs)
    if violations_global > 0:
        print(
            f"DPI violations: {violations_global} / {total_trials} (min diff {diff_min:.3e}, tol {tol:.1e})"
        )
        return 1

    print(f"OK: {total_trials} trials, min diff {diff_min:.3e}, tol {tol:.1e}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
