#!/usr/bin/env python3
"""Subgrid stress term visualization for 1D viscous Burgers."""
import csv
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python.les.burgers_1d import wavenumbers, filter_gaussian, evolve_series


def main(seed: int = 0, N: int = 128, nu: float = 0.1, dt: float = 0.002, tmax: float = 1.0) -> List[Dict]:
    _ = seed  # deterministic initial condition; seed kept for manifest
    L = 2.0 * np.pi
    x = np.linspace(0.0, L, N, endpoint=False)
    u0 = np.sin(x) + 0.5 * np.sin(2.0 * x)

    k = wavenumbers(N, L)
    dx = L / N
    sigma_list = [0.0, 1.0 * dx, 2.0 * dx, 4.0 * dx, 8.0 * dx]

    sample_times = np.linspace(0.0, tmax, 51)
    sample_indices = [int(round(t / dt)) for t in sample_times]
    n_steps = max(sample_indices)

    u_series = evolve_series(u0, k, nu, dt, n_steps, sample_indices)

    rows: List[Dict] = []
    max_tau_l2: Dict[float, float] = {}

    for sigma in sigma_list:
        max_l2 = 0.0
        for i, t in enumerate(sample_times):
            u = u_series[i]
            ubar = filter_gaussian(u, k, sigma)
            u2bar = filter_gaussian(u ** 2, k, sigma)
            tau_sgs = u2bar - (ubar ** 2)
            tau_l2 = float(np.sqrt(np.mean(tau_sgs ** 2)))
            tau_linf = float(np.max(np.abs(tau_sgs)))
            tau_l1 = float(np.mean(np.abs(tau_sgs)))
            max_l2 = max(max_l2, tau_l2)
            rows.append(
                {
                    "seed": seed,
                    "N": N,
                    "nu": nu,
                    "dt": dt,
                    "tmax": tmax,
                    "sigma": sigma,
                    "t": float(t),
                    "tau_l2": tau_l2,
                    "tau_linf": tau_linf,
                    "tau_l1": tau_l1,
                }
            )
        max_tau_l2[sigma] = max_l2

    # Sanity checks
    if max_tau_l2.get(0.0, 1.0) > 1e-12:
        raise ValueError(f"sigma=0 tau_l2 too large: {max_tau_l2[0.0]}")
    if max_tau_l2[sigma_list[-1]] < 1e-4:
        raise ValueError("largest sigma tau_l2 too small")
    if max_tau_l2[sigma_list[-1]] + 1e-12 < max_tau_l2[sigma_list[1]]:
        raise ValueError("tau_l2 does not increase with sigma")

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "les_subgrid_term.csv")
    png_path = os.path.join(artifacts_dir, "les_subgrid_term.png")

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["seed", "N", "nu", "dt", "tmax", "sigma", "t", "tau_l2", "tau_linf", "tau_l1"],
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7, 4))
    for sigma in sigma_list:
        ts = [r["t"] for r in rows if r["sigma"] == sigma]
        l2s = [r["tau_l2"] for r in rows if r["sigma"] == sigma]
        plt.plot(ts, l2s, label=f"sigma={sigma:.4f}")
    plt.xlabel("t")
    plt.ylabel(r"$\tau_{sgs}$ L2")
    plt.title(f"LES subgrid term (N={N}, nu={nu}, dt={dt})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(png_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/les_subgrid_term.csv",
            "kind": "csv",
            "desc": "LES subgrid term stats over time",
            "created_by": "physics/python/les/subgrid_term.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/les_subgrid_term.png",
            "kind": "png",
            "desc": "LES subgrid term L2 vs time",
            "created_by": "physics/python/les/subgrid_term.py",
            "seed": seed,
        },
    ]
    return entries


if __name__ == "__main__":
    main()
