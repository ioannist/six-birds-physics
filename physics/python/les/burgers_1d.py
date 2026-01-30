#!/usr/bin/env python3
"""LES-style route mismatch demo for 1D viscous Burgers."""
import csv
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def wavenumbers(n: int, L: float) -> np.ndarray:
    dx = L / n
    return 2.0 * np.pi * np.fft.fftfreq(n, d=dx)


def filter_gaussian(u: np.ndarray, k: np.ndarray, sigma: float) -> np.ndarray:
    if sigma <= 0.0:
        return u.copy()
    uhat = np.fft.fft(u)
    g = np.exp(-0.5 * (k * sigma) ** 2)
    return np.fft.ifft(uhat * g).real


def burgers_rhs(u: np.ndarray, k: np.ndarray, nu: float) -> np.ndarray:
    uhat = np.fft.fft(u)
    ux = np.fft.ifft(1j * k * uhat).real
    uxx = np.fft.ifft(-(k ** 2) * uhat).real
    return -u * ux + nu * uxx


def rk4_step(u: np.ndarray, k: np.ndarray, nu: float, dt: float) -> np.ndarray:
    k1 = burgers_rhs(u, k, nu)
    k2 = burgers_rhs(u + 0.5 * dt * k1, k, nu)
    k3 = burgers_rhs(u + 0.5 * dt * k2, k, nu)
    k4 = burgers_rhs(u + dt * k3, k, nu)
    return u + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)


def evolve_series(
    u0: np.ndarray,
    k: np.ndarray,
    nu: float,
    dt: float,
    n_steps: int,
    sample_indices: List[int],
) -> np.ndarray:
    u = u0.copy()
    series: List[np.ndarray] = [None] * len(sample_indices)
    index_map: Dict[int, List[int]] = {}
    for i, step in enumerate(sample_indices):
        index_map.setdefault(step, []).append(i)

    for step in range(n_steps + 1):
        if step in index_map:
            for idx in index_map[step]:
                series[idx] = u.copy()
        if step == n_steps:
            break
        u = rk4_step(u, k, nu, dt)
        if not np.all(np.isfinite(u)):
            raise ValueError(f"NaN/inf encountered at step {step + 1}")

    return np.array(series)


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
    max_mismatch: Dict[float, float] = {}

    for sigma in sigma_list:
        if sigma == 0.0:
            v_series = u_series
        else:
            v0 = filter_gaussian(u0, k, sigma)
            v_series = evolve_series(v0, k, nu, dt, n_steps, sample_indices)

        mm_max = 0.0
        for i, t in enumerate(sample_times):
            a = filter_gaussian(u_series[i], k, sigma)
            b = v_series[i]
            mismatch = float(np.sqrt(np.mean((a - b) ** 2)))
            mm_max = max(mm_max, mismatch)
            rows.append(
                {
                    "seed": seed,
                    "N": N,
                    "nu": nu,
                    "dt": dt,
                    "tmax": tmax,
                    "sigma": sigma,
                    "t": float(t),
                    "mismatch_l2": mismatch,
                }
            )
        max_mismatch[sigma] = mm_max

    # Sanity checks
    if max_mismatch.get(0.0, 1.0) > 1e-12:
        raise ValueError(f"sigma=0 mismatch too large: {max_mismatch[0.0]}")
    if max_mismatch[sigma_list[-1]] < 1e-6:
        raise ValueError("largest sigma mismatch too small")
    if max_mismatch[sigma_list[-1]] + 1e-12 < max_mismatch[sigma_list[1]]:
        raise ValueError("mismatch does not increase with sigma")

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "les_route_mismatch.csv")
    png_path = os.path.join(artifacts_dir, "les_route_mismatch.png")

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["seed", "N", "nu", "dt", "tmax", "sigma", "t", "mismatch_l2"],
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7, 4))
    for sigma in sigma_list:
        ts = [r["t"] for r in rows if r["sigma"] == sigma]
        ms = [r["mismatch_l2"] for r in rows if r["sigma"] == sigma]
        plt.plot(ts, ms, label=f"sigma={sigma:.4f}")
    plt.xlabel("t")
    plt.ylabel("L2 mismatch")
    plt.title(f"Burgers route mismatch (N={N}, nu={nu}, dt={dt})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(png_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/les_route_mismatch.csv",
            "kind": "csv",
            "desc": "LES Burgers filter/evolve mismatch",
            "created_by": "physics/python/les/burgers_1d.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/les_route_mismatch.png",
            "kind": "png",
            "desc": "LES Burgers mismatch vs time",
            "created_by": "physics/python/les/burgers_1d.py",
            "seed": seed,
        },
    ]
    return entries


if __name__ == "__main__":
    main()
