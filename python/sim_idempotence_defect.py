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
class Params:
    K: int
    m: int
    N: int
    lam: float
    gamma: float


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


def Q(mu: np.ndarray, params: Params) -> np.ndarray:
    K, m = params.K, params.m
    return mu.reshape(K, m).sum(axis=1)


def U(nu: np.ndarray, params: Params) -> np.ndarray:
    K, m, N = params.K, params.m, params.N
    out = np.zeros(N)
    for x in range(K):
        out[x * m : (x + 1) * m] = nu[x] / m
    return out


def macro_transition(Ptau: np.ndarray, params: Params) -> np.ndarray:
    K = params.K
    M = np.zeros((K, K))
    for x in range(K):
        ex = np.zeros(K)
        ex[x] = 1.0
        mu = U(ex, params)
        nu = Q(mu @ Ptau, params)
        M[x, :] = nu
    return M


def main() -> int:
    seed = 0
    rng = np.random.default_rng(seed)

    params = Params(K=6, m=10, N=60, lam=0.2, gamma=0.7)

    alpha_values = [i / 10.0 for i in range(11)]
    tau_values = [1, 2, 5, 10]
    trials_per_combo = 300

    artifacts_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "artifacts"))
    os.makedirs(artifacts_dir, exist_ok=True)

    csv_path = os.path.join(artifacts_dir, "idempotence_defect.csv")
    summary_path = os.path.join(artifacts_dir, "idempotence_defect_summary.csv")
    plot_path = os.path.join(artifacts_dir, "idempotence_defect.png")

    D = build_D(params)
    L = build_L(params)

    results: Dict[Tuple[float, int], List[float]] = {}

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["alpha", "tau", "trial", "delta", "K", "m", "N", "lam", "gamma", "seed"])
        for alpha in alpha_values:
            W = build_W(alpha, params)
            P = D @ W @ L
            for tau in tau_values:
                Ptau = np.linalg.matrix_power(P, tau)
                M = macro_transition(Ptau, params)
                key = (alpha, tau)
                results[key] = []
                for t in range(trials_per_combo):
                    mu = rng.dirichlet(np.ones(params.N))
                    nu1 = Q(mu @ Ptau, params)
                    nu2 = nu1 @ M
                    delta = 0.5 * np.sum(np.abs(nu2 - nu1))
                    results[key].append(float(delta))
                    writer.writerow(
                        [
                            alpha,
                            tau,
                            t,
                            delta,
                            params.K,
                            params.m,
                            params.N,
                            params.lam,
                            params.gamma,
                            seed,
                        ]
                    )

    # Summaries
    summaries: Dict[int, Dict[str, float]] = {}
    with open(summary_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "alpha",
                "tau",
                "mean_delta",
                "median_delta",
                "std_delta",
                "K",
                "m",
                "N",
                "lam",
                "gamma",
                "seed",
                "slope_mean_delta_vs_alpha",
                "corr_mean_delta_vs_alpha",
            ]
        )
        for tau in tau_values:
            means = []
            for alpha in alpha_values:
                vals = np.array(results[(alpha, tau)])
                mean = float(vals.mean())
                median = float(np.median(vals))
                std = float(vals.std(ddof=0))
                means.append(mean)
                writer.writerow(
                    [
                        alpha,
                        tau,
                        mean,
                        median,
                        std,
                        params.K,
                        params.m,
                        params.N,
                        params.lam,
                        params.gamma,
                        seed,
                        "",
                        "",
                    ]
                )
            x = np.array(alpha_values)
            y = np.array(means)
            slope = float(np.polyfit(x, y, 1)[0])
            corr = float(np.corrcoef(x, y)[0, 1])
            summaries[tau] = {"slope": slope, "corr": corr}
            writer.writerow(
                [
                    "all",
                    tau,
                    "",
                    "",
                    "",
                    params.K,
                    params.m,
                    params.N,
                    params.lam,
                    params.gamma,
                    seed,
                    slope,
                    corr,
                ]
            )

    # Plot
    plt.figure(figsize=(8, 4.5))
    for tau in tau_values:
        means = [float(np.mean(results[(alpha, tau)])) for alpha in alpha_values]
        plt.plot(alpha_values, means, label=f"tau={tau}")
    plt.xlabel("alpha")
    plt.ylabel("mean delta")
    plt.title(
        f"Idempotence defect vs alpha (K={params.K}, m={params.m}, lam={params.lam}, gamma={params.gamma}, trials={trials_per_combo})"
    )
    plt.legend()
    plt.tight_layout()
    plt.savefig(plot_path, dpi=150)
    plt.close()

    # Trend check
    for tau in [2, 5, 10]:
        mean0 = float(np.mean(results[(0.0, tau)]))
        mean1 = float(np.mean(results[(1.0, tau)]))
        if mean1 > mean0:
            print(
                f"Trend check failed for tau={tau}: mean(alpha=1)={mean1:.3e} > mean(alpha=0)={mean0:.3e}"
            )
            return 1

    total_trials = len(alpha_values) * len(tau_values) * trials_per_combo
    print(
        f"OK: {total_trials} trials; trend check passed for taus [2,5,10]"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
