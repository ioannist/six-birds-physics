#!/usr/bin/env python3
import csv
import math
import os
import sys
from typing import List, Dict, Tuple

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

V = np.array([-1.0, 0.0, 1.0])


def transport(f: np.ndarray) -> np.ndarray:
    out = np.empty_like(f)
    out[:, 0] = np.roll(f[:, 0], -1)
    out[:, 1] = f[:, 1]
    out[:, 2] = np.roll(f[:, 2], 1)
    return out


def moments(f: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    rho = np.sum(f, axis=1)
    mom = f @ V
    u = np.zeros_like(rho)
    mask = rho >= 1e-15
    u[mask] = mom[mask] / rho[mask]
    u = np.clip(u, -1.0, 1.0)
    return rho, mom, u


def _u_from_beta(beta: np.ndarray) -> np.ndarray:
    eb = np.exp(beta)
    em = np.exp(-beta)
    Z = 1.0 + eb + em
    return (eb - em) / Z


def _beta_from_u(u: np.ndarray, iters: int = 40) -> np.ndarray:
    u = np.clip(u, -1.0, 1.0)
    lo = np.full_like(u, -20.0)
    hi = np.full_like(u, 20.0)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        umid = _u_from_beta(mid)
        lo = np.where(umid < u, mid, lo)
        hi = np.where(umid >= u, mid, hi)
    return 0.5 * (lo + hi)


def feq_from_rho_u(rho: np.ndarray, u: np.ndarray) -> np.ndarray:
    beta = _beta_from_u(u)
    eb = np.exp(beta)
    em = np.exp(-beta)
    Z = 1.0 + eb + em
    p_neg = em / Z
    p_zero = 1.0 / Z
    p_pos = eb / Z
    f_eq = np.zeros((rho.size, 3))
    f_eq[:, 0] = rho * p_neg
    f_eq[:, 1] = rho * p_zero
    f_eq[:, 2] = rho * p_pos

    # diagnostic checks for non-tiny rho
    mask = rho >= 1e-12
    if np.any(mask):
        mass_err = np.max(np.abs(np.sum(f_eq[mask], axis=1) - rho[mask]))
        mom_err = np.max(np.abs((f_eq[mask] @ V) - rho[mask] * u[mask]))
        if mass_err > 1e-12 or mom_err > 1e-10:
            raise ValueError("Equilibrium moment mismatch")

    return f_eq


def bgk_collision(f: np.ndarray, omega: float) -> np.ndarray:
    if omega < 0 or omega > 1:
        raise ValueError("omega must be in [0,1]")
    rho, _, u = moments(f)
    f_eq = feq_from_rho_u(rho, u)
    f_new = (1.0 - omega) * f + omega * f_eq
    total = float(np.sum(f_new))
    if total <= 0:
        raise ValueError("Non-positive total mass")
    return f_new / total


def bgk_step(f: np.ndarray, omega: float) -> np.ndarray:
    return bgk_collision(transport(f), omega)


def evolve(f: np.ndarray, omega: float, steps: int) -> np.ndarray:
    out = f
    for _ in range(steps):
        out = bgk_step(out, omega)
    return out


def E(f: np.ndarray) -> np.ndarray:
    rho, _, u = moments(f)
    return feq_from_rho_u(rho, u)


def E_tau(f: np.ndarray, omega: float, tau: int) -> np.ndarray:
    return E(evolve(f, omega, tau))


def tv_flat(a: np.ndarray, b: np.ndarray) -> float:
    p = a.reshape(-1)
    q = b.reshape(-1)
    return 0.5 * float(np.sum(np.abs(p - q)))


def random_f0(Nx: int, Nv: int, rng: np.random.Generator) -> np.ndarray:
    if Nv != 3:
        raise ValueError("Nv must be 3")
    rho = rng.dirichlet(np.ones(Nx))
    f = np.zeros((Nx, Nv))
    for x in range(Nx):
        p = rng.dirichlet(np.ones(Nv))
        f[x, :] = rho[x] * p
    total = float(np.sum(f))
    return f / total


def main(seed: int = 0, Nx: int = 16, Nv: int = 3, trials_per_combo: int = 200) -> List[Dict]:
    rng = np.random.default_rng(seed)
    omega_values = [i / 10.0 for i in range(11)]
    tau_values = [1, 2, 5, 10]

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "bgk_idempotence_defect.csv")
    summary_path = os.path.join(artifacts_dir, "bgk_summary.csv")
    plot_path = os.path.join(artifacts_dir, "bgk_idempotence_defect.png")

    rows = []
    summary = {}

    for omega in omega_values:
        for tau in tau_values:
            deltas = []
            for trial in range(trials_per_combo):
                f0 = random_f0(Nx, Nv, rng)
                g = E_tau(f0, omega, tau)
                h = E_tau(g, omega, tau)
                delta = tv_flat(h, g)
                deltas.append(delta)
                rows.append(
                    {
                        "seed": seed,
                        "trial": trial,
                        "Nx": Nx,
                        "Nv": Nv,
                        "omega": omega,
                        "tau": tau,
                        "delta": delta,
                    }
                )
            deltas_arr = np.array(deltas)
            summary[(omega, tau)] = {
                "mean": float(np.mean(deltas_arr)),
                "median": float(np.median(deltas_arr)),
                "std": float(np.std(deltas_arr, ddof=0)),
                "trials": trials_per_combo,
            }

    # Trend check
    for tau in [2, 5, 10]:
        mean0 = summary[(0.0, tau)]["mean"]
        mean1 = summary[(1.0, tau)]["mean"]
        if mean1 > mean0 + 1e-12:
            print(f"Trend check failed tau={tau}: {mean1} > {mean0}")
            raise SystemExit(1)

    # Write CSVs
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["seed", "trial", "Nx", "Nv", "omega", "tau", "delta"])
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    with open(summary_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f, fieldnames=["omega", "tau", "mean_delta", "median_delta", "std_delta", "trials"]
        )
        writer.writeheader()
        for omega in omega_values:
            for tau in tau_values:
                s = summary[(omega, tau)]
                writer.writerow(
                    {
                        "omega": omega,
                        "tau": tau,
                        "mean_delta": s["mean"],
                        "median_delta": s["median"],
                        "std_delta": s["std"],
                        "trials": s["trials"],
                    }
                )

    # Plot
    plt.figure(figsize=(8, 4.5))
    for tau in tau_values:
        means = [summary[(omega, tau)]["mean"] for omega in omega_values]
        plt.plot(omega_values, means, label=f"tau={tau}")
    plt.xlabel("omega")
    plt.ylabel("mean delta")
    plt.title(f"BGK idempotence defect (Nx={Nx}, Nv={Nv}, trials={trials_per_combo})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(plot_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/bgk_idempotence_defect.csv",
            "kind": "csv",
            "desc": "BGK idempotence defect (per trial)",
            "created_by": "physics/python/fluids/bgk_discrete.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/bgk_summary.csv",
            "kind": "csv",
            "desc": "BGK idempotence defect summary",
            "created_by": "physics/python/fluids/bgk_discrete.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/bgk_idempotence_defect.png",
            "kind": "png",
            "desc": "BGK idempotence defect plot",
            "created_by": "physics/python/fluids/bgk_discrete.py",
            "seed": seed,
        },
    ]

    print("OK: bgk discrete")
    return entries


if __name__ == "__main__":
    main()
