#!/usr/bin/env python3
import csv
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python.quantum.core import (
    random_density_matrix,
    random_cptp_kraus,
    kraus_dephasing,
    kraus_depolarizing,
    kraus_projective_measurement_standard,
    apply_kraus,
    quantum_relative_entropy,
)


def main(seed: int = 0, trials_per_dim: int = 300, tol: float = 1e-8, eps: float = 1e-12) -> List[Dict]:
    rng = np.random.default_rng(seed)
    d_list = [2, 3, 4, 6]
    channel_types = ["dephasing", "depolarizing", "projective", "random_kraus"]

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    summary_path = os.path.join(artifacts_dir, "quantum_dpi_summary.csv")
    hist_path = os.path.join(artifacts_dir, "quantum_dpi_hist.png")

    diffs_all: List[float] = []
    per_d_min = {d: float("inf") for d in d_list}

    stats = {}
    for d in d_list:
        for ct in channel_types:
            stats[(d, ct)] = []

    violations = 0
    min_diff = float("inf")

    for d in d_list:
        for _ in range(trials_per_dim):
            rho = random_density_matrix(d, rng)
            sigma = random_density_matrix(d, rng)

            ct = rng.choice(channel_types)
            if ct == "dephasing":
                p = float(rng.uniform(0.1, 0.9))
                kraus = kraus_dephasing(d, p)
            elif ct == "depolarizing":
                p = float(rng.uniform(0.05, 0.5))
                kraus = kraus_depolarizing(d, p)
            elif ct == "projective":
                kraus = kraus_projective_measurement_standard(d)
            elif ct == "random_kraus":
                kraus, _ = random_cptp_kraus(d, r=4, rng=rng, eps=eps)
            else:
                raise ValueError("unknown channel_type")

            Sin, _ = quantum_relative_entropy(rho, sigma, eps=eps)
            rho_out = apply_kraus(rho, kraus)
            sigma_out = apply_kraus(sigma, kraus)
            Sout, _ = quantum_relative_entropy(rho_out, sigma_out, eps=eps)

            if not np.isfinite(Sin) or not np.isfinite(Sout):
                raise ValueError("NaN/inf in relative entropy")

            diff = Sin - Sout
            diffs_all.append(diff)
            stats[(d, ct)].append(diff)
            min_diff = min(min_diff, diff)
            per_d_min[d] = min(per_d_min[d], diff)
            if diff < -tol:
                violations += 1

    if violations > 0:
        print(f"DPI violations: {violations}, min diff {min_diff:.3e}")
        raise SystemExit(1)

    # Summary CSV
    with open(summary_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "d",
                "channel_type",
                "trials",
                "seed",
                "tol",
                "eps",
                "min_diff",
                "mean_diff",
                "p05_diff",
                "p50_diff",
                "p95_diff",
                "violations",
            ]
        )
        for d in d_list:
            for ct in channel_types:
                vals = np.array(stats[(d, ct)], dtype=float)
                if vals.size == 0:
                    continue
                writer.writerow(
                    [
                        d,
                        ct,
                        int(vals.size),
                        seed,
                        tol,
                        eps,
                        float(np.min(vals)),
                        float(np.mean(vals)),
                        float(np.quantile(vals, 0.05)),
                        float(np.quantile(vals, 0.5)),
                        float(np.quantile(vals, 0.95)),
                        0,
                    ]
                )

    # Histogram
    plt.figure(figsize=(8, 4.5))
    plt.hist(diffs_all, bins=60)
    plt.xlabel("diff = S(rho||sigma) - S(Φ(rho)||Φ(sigma))")
    plt.ylabel("count")
    plt.title(f"Quantum DPI diffs (min={min_diff:.3e}, tol={tol:.1e})")
    plt.tight_layout()
    plt.savefig(hist_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/quantum_dpi_summary.csv",
            "kind": "csv",
            "desc": "Quantum DPI summary",
            "created_by": "physics/python/quantum/dpi.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/quantum_dpi_hist.png",
            "kind": "png",
            "desc": "Quantum DPI histogram",
            "created_by": "physics/python/quantum/dpi.py",
            "seed": seed,
        },
    ]

    print("OK: quantum DPI")
    return entries


if __name__ == "__main__":
    main()
