#!/usr/bin/env python3
"""Gravity toy in lens/completion terms (Q, U, E_tau)."""
import csv
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def phi_t(y0: np.ndarray, t: float) -> np.ndarray:
    return y0 / (1.0 - t * y0)


def pushforward(mu: np.ndarray, y_grid: np.ndarray, t: float) -> np.ndarray:
    y1 = phi_t(y_grid, t)
    y1 = np.clip(y1, y_grid[0], y_grid[-1])
    idx = np.searchsorted(y_grid, y1, side="right") - 1
    idx = np.clip(idx, 0, len(y_grid) - 2)
    y_left = y_grid[idx]
    y_right = y_grid[idx + 1]
    denom = y_right - y_left
    denom = np.where(denom == 0, 1.0, denom)
    frac = (y1 - y_left) / denom

    mu_new = np.zeros_like(mu)
    np.add.at(mu_new, idx, mu * (1.0 - frac))
    np.add.at(mu_new, idx + 1, mu * frac)
    total = mu_new.sum()
    if total > 0:
        mu_new = mu_new / total
    return mu_new


def Q_mean_var(mu: np.ndarray, y_grid: np.ndarray, var_floor: float = 1e-4) -> np.ndarray:
    mean = float(np.sum(mu * y_grid))
    var = float(np.sum(mu * (y_grid - mean) ** 2))
    if var < var_floor:
        var = 0.0
    return np.array([mean, var])


def U_gaussian(macro: np.ndarray, y_grid: np.ndarray, var_floor: float = 1e-4) -> np.ndarray:
    mean, var = float(macro[0]), float(macro[1])
    if var < var_floor:
        idx = np.searchsorted(y_grid, mean, side="right") - 1
        idx = int(np.clip(idx, 0, len(y_grid) - 2))
        y_left = y_grid[idx]
        y_right = y_grid[idx + 1]
        denom = y_right - y_left if y_right != y_left else 1.0
        frac = (mean - y_left) / denom
        mu = np.zeros_like(y_grid)
        mu[idx] += 1.0 - frac
        mu[idx + 1] += frac
        return mu
    # Match mean/variance via a quadratic exponential family on the grid.
    a = 0.0
    b = -0.5 / var
    for _ in range(30):
        expo = a * y_grid + b * (y_grid ** 2)
        expo = expo - np.max(expo)
        w = np.exp(expo)
        w_sum = float(np.sum(w))
        if w_sum == 0:
            break
        p = w / w_sum
        m1 = float(np.sum(p * y_grid))
        m2 = float(np.sum(p * (y_grid ** 2)))
        v = m2 - m1 * m1
        f1 = m1 - mean
        f2 = v - var
        if abs(f1) + abs(f2) < 1e-10:
            return p
        m3 = float(np.sum(p * (y_grid ** 3)))
        m4 = float(np.sum(p * (y_grid ** 4)))
        dm_da = v
        dm_db = m3 - m1 * m2
        dm2_da = m3 - m2 * m1
        dm2_db = m4 - m2 * m2
        dv_da = dm2_da - 2.0 * m1 * dm_da
        dv_db = dm2_db - 2.0 * m1 * dm_db
        J = np.array([[dm_da, dm_db], [dv_da, dv_db]], dtype=float)
        F = np.array([f1, f2], dtype=float)
        if abs(np.linalg.det(J)) < 1e-14:
            break
        delta = np.linalg.solve(J, F)
        a -= float(delta[0])
        b -= float(delta[1])
    # Fallback: simple Gaussian weights.
    w = np.exp(-0.5 * (y_grid - mean) ** 2 / var)
    w_sum = float(np.sum(w))
    if w_sum == 0:
        return np.ones_like(y_grid) / len(y_grid)
    return w / w_sum


def E(mu: np.ndarray, y_grid: np.ndarray) -> np.ndarray:
    return U_gaussian(Q_mean_var(mu, y_grid), y_grid)


def E_tau(mu: np.ndarray, y_grid: np.ndarray, t: float) -> np.ndarray:
    return E(pushforward(mu, y_grid, t), y_grid)


def tv(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def mu_init(y_grid: np.ndarray, mu0: float, s: float, sig2: float = 0.01) -> np.ndarray:
    if s == 0.0:
        idx = int(np.argmin(np.abs(y_grid - mu0)))
        mu = np.zeros_like(y_grid)
        mu[idx] = 1.0
        return mu
    w1 = np.exp(-0.5 * (y_grid - (mu0 - s)) ** 2 / sig2)
    w2 = np.exp(-0.5 * (y_grid - (mu0 + s)) ** 2 / sig2)
    w = 0.5 * w1 + 0.5 * w2
    w_sum = float(np.sum(w))
    if w_sum == 0:
        return np.ones_like(y_grid) / len(y_grid)
    return w / w_sum


def main(seed: int = 0, Nbin: int = 401) -> List[Dict]:
    _ = seed  # deterministic initial condition; seed kept for manifest
    y_grid = np.linspace(-0.5, 0.9, Nbin)
    t_list = np.linspace(0.0, 1.0, 51)
    s_list = [0.0, 0.2, 0.5, 0.8]
    mu0_val = 0.3

    rows: List[Dict] = []
    max_route_by_s: Dict[float, float] = {}

    for s in s_list:
        mu0 = mu_init(y_grid, mu0_val, s)
        mean0, var0 = Q_mean_var(mu0, y_grid)
        max_route = 0.0
        for t in t_list:
            mu_t = pushforward(mu0, y_grid, float(t))
            E_mu_t = E(mu_t, y_grid)
            T_E_mu = pushforward(E(mu0, y_grid), y_grid, float(t))
            delta_route = tv(E_mu_t, T_E_mu)

            e_mu_t = E(mu_t, y_grid)
            delta_closure_idem = tv(E(e_mu_t, y_grid), e_mu_t)

            g = E_tau(mu0, y_grid, float(t))
            h = E_tau(g, y_grid, float(t))
            delta_iter = tv(h, g)

            max_route = max(max_route, delta_route)
            rows.append(
                {
                    "seed": seed,
                    "Nbin": Nbin,
                    "s": float(s),
                    "t": float(t),
                    "delta_route": delta_route,
                    "delta_closure_idem": delta_closure_idem,
                    "delta_iter": delta_iter,
                    "mean0": float(mean0),
                    "var0": float(var0),
                }
            )
        max_route_by_s[float(s)] = max_route

    max_closure_idem = max(r["delta_closure_idem"] for r in rows)
    max_closure_idem_s0 = max(r["delta_closure_idem"] for r in rows if r["s"] == 0.0)
    if max_route_by_s.get(0.0, 1.0) > 1e-6:
        raise ValueError(f"s=0 route mismatch too large: {max_route_by_s[0.0]}")
    if max_route_by_s.get(0.8, 0.0) < 1e-2:
        raise ValueError("s=0.8 route mismatch too small")
    if max_closure_idem > 1e-2:
        raise ValueError(f"closure idempotence too large: {max_closure_idem}")
    if max_closure_idem_s0 > 1e-6:
        raise ValueError(f"s=0 closure idempotence too large: {max_closure_idem_s0}")

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "gravity_packaging_mismatch.csv")
    png_path = os.path.join(artifacts_dir, "gravity_packaging_mismatch.png")

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "seed",
                "Nbin",
                "s",
                "t",
                "delta_route",
                "delta_closure_idem",
                "delta_iter",
                "mean0",
                "var0",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7, 4))
    for s in s_list:
        ts = [r["t"] for r in rows if r["s"] == float(s)]
        dr = [r["delta_route"] for r in rows if r["s"] == float(s)]
        plt.plot(ts, dr, label=f"s={s:.1f}")
    plt.xlabel("t")
    plt.ylabel("route mismatch (TV)")
    plt.title("packaging route mismatch (mean/var Gaussian completion)")
    plt.legend()
    plt.tight_layout()
    plt.savefig(png_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/gravity_packaging_mismatch.csv",
            "kind": "csv",
            "desc": "Gravity packaging route mismatch and idempotence",
            "created_by": "physics/python/gravity/packaging_view.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/gravity_packaging_mismatch.png",
            "kind": "png",
            "desc": "Gravity packaging route mismatch vs time",
            "created_by": "physics/python/gravity/packaging_view.py",
            "seed": seed,
        },
    ]
    return entries


if __name__ == "__main__":
    main()
