#!/usr/bin/env python3
import csv
import os
import sys
from dataclasses import dataclass
from typing import Dict, List, Tuple

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


@dataclass
class Params:
    K: int
    m: int
    N: int
    lam: float
    gamma: float


def tv(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def build_D(params: Params) -> np.ndarray:
    K, m, N = params.K, params.m, params.N
    gamma = params.gamma
    D = np.zeros((N, N))
    for z in range(N):
        x = z // m
        gate = x * m
        D[z, gate] += gamma
        D[z, z] += (1.0 - gamma)
    return D


def build_W(alpha: float, params: Params) -> np.ndarray:
    K, m, N = params.K, params.m, params.N
    Wfull = np.zeros((N, N))
    for x in range(K):
        rows = slice(x * m, (x + 1) * m)
        cols = slice(x * m, (x + 1) * m)
        Wfull[rows, cols] = 1.0 / m
    I = np.eye(N)
    return (1.0 - alpha) * I + alpha * Wfull


def build_L(params: Params) -> np.ndarray:
    K, m, N = params.K, params.m, params.N
    lam = params.lam
    L = np.eye(N)
    for x in range(K):
        gate = x * m
        next_gate = ((x + 1) % K) * m
        L[gate, gate] = 1.0 - lam
        L[gate, next_gate] = lam
    return L


def build_P_funnel(params: Params) -> np.ndarray:
    K, m, N = params.K, params.m, params.N
    P = np.zeros((N, N))
    for z in range(N):
        x = z // m
        gate = x * m
        P[z, gate] = 1.0
    return P


def lens_std(z: int, params: Params) -> int:
    return z // params.m


def lens_mod(z: int, params: Params) -> int:
    return z % params.K


def lens_diag(z: int, params: Params) -> int:
    return ((z // params.m) + (z % params.m)) % params.K


def fiber_map(params: Params, lens_fn) -> Tuple[np.ndarray, np.ndarray]:
    fiber_of_z = np.zeros(params.N, dtype=int)
    for z in range(params.N):
        fiber_of_z[z] = lens_fn(z, params)
    sizes = np.bincount(fiber_of_z, minlength=params.K)
    if np.any(sizes == 0):
        raise ValueError("Lens has empty fiber")
    return fiber_of_z, sizes


def Q_f(mu: np.ndarray, fiber_of_z: np.ndarray, K: int) -> np.ndarray:
    return np.bincount(fiber_of_z, weights=mu, minlength=K)


def U_uniform(nu: np.ndarray, fiber_of_z: np.ndarray, sizes: np.ndarray) -> np.ndarray:
    out = np.zeros_like(fiber_of_z, dtype=float)
    for z, x in enumerate(fiber_of_z):
        out[z] = nu[x] / sizes[x]
    return out


def E_from_lens(mu: np.ndarray, fiber_of_z: np.ndarray, sizes: np.ndarray, K: int) -> np.ndarray:
    return U_uniform(Q_f(mu, fiber_of_z, K), fiber_of_z, sizes)


def macro_transition(Ptau: np.ndarray, params: Params, fiber_of_z: np.ndarray, sizes: np.ndarray) -> np.ndarray:
    K = params.K
    M = np.zeros((K, K))
    for x in range(K):
        ex = np.zeros(K)
        ex[x] = 1.0
        mu = U_uniform(ex, fiber_of_z, sizes)
        nu = Q_f(mu @ Ptau, fiber_of_z, K)
        M[x, :] = nu
    return M


def main() -> int:
    params = Params(K=6, m=10, N=60, lam=0.2, gamma=0.7)
    seeds = [0, 1, 2, 3, 4]

    artifacts_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "artifacts"))
    os.makedirs(artifacts_dir, exist_ok=True)

    csv_path = os.path.join(artifacts_dir, "failure_modes.csv")
    plot_path = os.path.join(artifacts_dir, "failure_modes.png")

    fieldnames = [
        "mode_id",
        "lens_name",
        "alpha",
        "tau",
        "seed",
        "trial",
        "mismatch_tv",
        "idem_tv",
        "macro_drift_tv",
        "delta_tv",
        "K",
        "m",
        "N",
        "lam",
        "gamma",
    ]

    rows: List[Dict[str, object]] = []

    # FM1: macro preserved, micro funnel => commutation fails
    fiber_std, sizes_std = fiber_map(params, lens_std)
    P_funnel = build_P_funnel(params)
    trials_per_seed_fm1 = 50
    for seed in seeds:
        rng = np.random.default_rng(seed)
        for t in range(trials_per_seed_fm1):
            mu = rng.dirichlet(np.ones(params.N))
            C_mu = E_from_lens(mu, fiber_std, sizes_std, params.K)
            left = E_from_lens(mu @ P_funnel, fiber_std, sizes_std, params.K)
            right = C_mu @ P_funnel
            mismatch = tv(left, right)
            rows.append(
                {
                    "mode_id": "FM1_macro_preserved_micro_funnel",
                    "lens_name": "std",
                    "alpha": "",
                    "tau": 1,
                    "seed": seed,
                    "trial": t,
                    "mismatch_tv": mismatch,
                    "idem_tv": "",
                    "macro_drift_tv": "",
                    "delta_tv": "",
                    "K": params.K,
                    "m": params.m,
                    "N": params.N,
                    "lam": params.lam,
                    "gamma": params.gamma,
                }
            )

    # FM2: bad completion => idempotence fails
    trials_per_seed_fm2 = 50
    for seed in seeds:
        rng = np.random.default_rng(seed + 100)
        for t in range(trials_per_seed_fm2):
            mu = rng.dirichlet(np.ones(params.N))
            nu = Q_f(mu, fiber_std, params.K)
            # shift macro index
            nu_shift = np.roll(nu, -1)
            E_bad = U_uniform(nu_shift, fiber_std, sizes_std)
            nu2 = Q_f(E_bad, fiber_std, params.K)
            nu2_shift = np.roll(nu2, -1)
            E_bad2 = U_uniform(nu2_shift, fiber_std, sizes_std)
            idem_bad = tv(E_bad2, E_bad)
            macro_drift = tv(Q_f(E_bad, fiber_std, params.K), nu)
            rows.append(
                {
                    "mode_id": "FM2_bad_completion_nonsection",
                    "lens_name": "std",
                    "alpha": "",
                    "tau": 0,
                    "seed": seed,
                    "trial": t,
                    "mismatch_tv": "",
                    "idem_tv": idem_bad,
                    "macro_drift_tv": macro_drift,
                    "delta_tv": "",
                    "K": params.K,
                    "m": params.m,
                    "N": params.N,
                    "lam": params.lam,
                    "gamma": params.gamma,
                }
            )

    # FM3: misaligned lens => mixing knob doesn't help much
    alpha_values = [i / 10.0 for i in range(11)]
    tau_values = [2, 5, 10]
    trials_per_seed_fm3 = 40  # 5 seeds * 40 = 200 trials per (alpha,tau)

    D = build_D(params)
    L = build_L(params)

    lens_defs = {
        "std": (lens_std, *fiber_map(params, lens_std)),
        "mod": (lens_mod, *fiber_map(params, lens_mod)),
        "diag": (lens_diag, *fiber_map(params, lens_diag)),
    }

    deltas: Dict[Tuple[str, float, int], List[float]] = {}

    for lens_name in ["std", "mod", "diag"]:
        _, fiber_of_z, sizes = lens_defs[lens_name]
        for alpha in alpha_values:
            W = build_W(alpha, params)
            P = D @ W @ L
            for tau in tau_values:
                Ptau = np.linalg.matrix_power(P, tau)
                M = macro_transition(Ptau, params, fiber_of_z, sizes)
                key = (lens_name, alpha, tau)
                deltas[key] = []
                for seed in seeds:
                    rng = np.random.default_rng(seed + 1000)
                    for t in range(trials_per_seed_fm3):
                        mu = rng.dirichlet(np.ones(params.N))
                        nu1 = Q_f(mu @ Ptau, fiber_of_z, params.K)
                        nu2 = nu1 @ M
                        delta = tv(nu2, nu1)
                        deltas[key].append(delta)

    # Select misaligned lens with largest endpoint ratio at tau=2
    best_lens = None
    best_ratio = -1.0
    for lens_name in ["mod", "diag"]:
        mean0 = float(np.mean(deltas[(lens_name, 0.0, 2)]))
        mean1 = float(np.mean(deltas[(lens_name, 1.0, 2)]))
        ratio = mean1 / mean0 if mean0 > 0 else float("inf")
        if ratio > best_ratio:
            best_ratio = ratio
            best_lens = lens_name

    # Write FM3 rows: baseline + selected misaligned lens
    for lens_name, mode_id in [
        ("std", "FM3_baseline_for_comparison"),
        (best_lens, "FM3_misaligned_lens"),
    ]:
        for alpha in alpha_values:
            for tau in tau_values:
                key = (lens_name, alpha, tau)
                vals = deltas[key]
                idx = 0
                for seed in seeds:
                    for t in range(trials_per_seed_fm3):
                        delta = vals[idx]
                        idx += 1
                        rows.append(
                            {
                                "mode_id": mode_id,
                                "lens_name": lens_name,
                                "alpha": alpha,
                                "tau": tau,
                                "seed": seed,
                                "trial": t,
                                "mismatch_tv": "",
                                "idem_tv": "",
                                "macro_drift_tv": "",
                                "delta_tv": delta,
                                "K": params.K,
                                "m": params.m,
                                "N": params.N,
                                "lam": params.lam,
                                "gamma": params.gamma,
                            }
                        )

    # Plot: alpha vs mean delta for tau=2 (baseline vs selected misaligned)
    plt.figure(figsize=(8, 4.5))
    for lens_name, label in [("std", "baseline std"), (best_lens, f"misaligned {best_lens}")]:
        means = [float(np.mean(deltas[(lens_name, a, 2)])) for a in alpha_values]
        plt.plot(alpha_values, means, label=label)
    plt.xlabel("alpha")
    plt.ylabel("mean idempotence defect (tau=2)")
    plt.title(f"Failure mode FM3 (K={params.K}, m={params.m}, lam={params.lam}, gamma={params.gamma})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(plot_path, dpi=150)
    plt.close()

    # Write CSV
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    print(f"OK: wrote {len(rows)} rows; FM3 lens={best_lens}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
