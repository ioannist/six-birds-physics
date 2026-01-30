#!/usr/bin/env python3
import csv
import math
import os
import sys
from typing import Dict, List, Tuple

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def safe_pow2(exp: int) -> str:
    if exp < -1020:
        return ""
    return f"{2.0 ** exp:.12g}"


def log10_ratio(exp: int) -> float:
    return exp * math.log10(2.0)


def lens_partition(N: int, K: int) -> Tuple[int, np.ndarray]:
    if N % K != 0:
        raise ValueError("N must be divisible by K")
    r = N // K
    f = np.repeat(np.arange(K), r)
    return r, f


def is_measurable(pred: np.ndarray, K: int, r: int) -> bool:
    reshaped = pred.reshape(K, r)
    return bool(np.all(reshaped == reshaped[:, :1]))


def brute_force_count(N: int, K: int) -> int:
    r, _ = lens_partition(N, K)
    count = 0
    for i in range(2 ** N):
        bits = ((i >> np.arange(N)) & 1).astype(np.int8)
        if is_measurable(bits, K, r):
            count += 1
    return count


def mc_estimate(N: int, K: int, samples: int, rng: np.random.Generator) -> float:
    r, _ = lens_partition(N, K)
    batch = 10000
    hits = 0
    total = 0
    while total < samples:
        take = min(batch, samples - total)
        arr = rng.integers(0, 2, size=(take, N), dtype=np.int8)
        arr = arr.reshape(take, K, r)
        ok = np.all(arr == arr[:, :, :1], axis=2)
        ok = np.all(ok, axis=1)
        hits += int(np.sum(ok))
        total += take
    return hits / samples


def extra_bits_atoms(N: int, K: int, m_bits: int, seed: int) -> int:
    r, f = lens_partition(N, K)
    rng = np.random.default_rng(seed)
    if m_bits == 0:
        h = np.zeros(N, dtype=np.int64)
    else:
        h = rng.integers(0, 2 ** m_bits, size=N, dtype=np.int64)
    pair_id = f * (2 ** m_bits) + h
    return int(np.unique(pair_id).size)


def main() -> int:
    artifacts_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "artifacts"))
    os.makedirs(artifacts_dir, exist_ok=True)

    csv_path = os.path.join(artifacts_dir, "definability_ratio.csv")
    plot_path = os.path.join(artifacts_dir, "definability_ratio.png")

    seed = 12345
    rng = np.random.default_rng(seed)

    rows: List[Dict[str, object]] = []

    # B) Exact formula checks (small sizes)
    small_pairs = [(6, 3), (8, 2), (8, 4), (10, 5), (12, 3), (12, 6)]
    for N, K in small_pairs:
        r, _ = lens_partition(N, K)
        count = brute_force_count(N, K)
        expected = 2 ** K
        checks_passed = count == expected
        if not checks_passed:
            print(f"Brute force mismatch for (N,K)=({N},{K}): {count} != {expected}")
            return 1
        exp = K - N
        rows.append(
            {
                "mode": "base",
                "N": N,
                "K": K,
                "r": r,
                "m_bits": 0,
                "seed": -1,
                "atoms": K,
                "log2_ratio": exp,
                "log10_ratio": log10_ratio(exp),
                "theory_log2_ratio_base": exp,
                "empirical_prob": "",
                "theory_ratio": safe_pow2(exp),
                "checks_passed": True,
            }
        )

    # C) Monte Carlo checks (moderate sizes)
    mc_configs = [
        (12, 6, 50000),
        (20, 10, 100000),
        (24, 12, 200000),
    ]
    for N, K, samples in mc_configs:
        r, _ = lens_partition(N, K)
        emp = mc_estimate(N, K, samples, rng)
        exp = K - N
        theory = 2.0 ** exp
        ratio = emp / theory if theory > 0 else float("inf")
        ok = 0.5 <= ratio <= 2.0
        if not ok:
            print(
                f"MC check failed for (N,K)=({N},{K}): emp={emp:.6g}, theory={theory:.6g}, ratio={ratio:.3g}"
            )
            return 1
        rows.append(
            {
                "mode": "base",
                "N": N,
                "K": K,
                "r": r,
                "m_bits": 0,
                "seed": seed,
                "atoms": K,
                "log2_ratio": exp,
                "log10_ratio": log10_ratio(exp),
                "theory_log2_ratio_base": exp,
                "empirical_prob": emp,
                "theory_ratio": theory,
                "checks_passed": True,
            }
        )

    # D) Extra-bits refinement
    K = 6
    N_values = [60, 120, 240]
    m_bits_values = list(range(0, 9))
    replicates = 10
    for N in N_values:
        r, _ = lens_partition(N, K)
        for m_bits in m_bits_values:
            for rep in range(replicates):
                h_seed = 1000 + N * 10 + m_bits * 100 + rep
                A = extra_bits_atoms(N, K, m_bits, h_seed)
                exp = A - N
                rows.append(
                    {
                        "mode": "extra_bits",
                        "N": N,
                        "K": K,
                        "r": r,
                        "m_bits": m_bits,
                        "seed": h_seed,
                        "atoms": A,
                        "log2_ratio": exp,
                        "log10_ratio": log10_ratio(exp),
                        "theory_log2_ratio_base": K - N,
                        "empirical_prob": "",
                        "theory_ratio": safe_pow2(exp),
                        "checks_passed": True,
                    }
                )

    # Write CSV
    fieldnames = [
        "mode",
        "N",
        "K",
        "r",
        "m_bits",
        "seed",
        "atoms",
        "log2_ratio",
        "log10_ratio",
        "theory_log2_ratio_base",
        "empirical_prob",
        "theory_ratio",
        "checks_passed",
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    # Plot: mean log10_ratio vs m_bits for N in {60,120,240}, K=6
    plt.figure(figsize=(8, 4.5))
    for N in N_values:
        means = []
        for m_bits in m_bits_values:
            vals = [
                row["log10_ratio"]
                for row in rows
                if row["mode"] == "extra_bits"
                and row["N"] == N
                and row["K"] == K
                and row["m_bits"] == m_bits
            ]
            means.append(float(np.mean(vals)))
        plt.plot(m_bits_values, means, label=f"N={N}, K={K}")
    plt.xlabel("m_bits")
    plt.ylabel("log10_ratio")
    plt.title("Definability ratio vs extra bits (mean log10 ratio)")
    plt.legend()
    plt.tight_layout()
    plt.savefig(plot_path, dpi=150)
    plt.close()

    print("OK: checks passed and artifacts written")
    return 0


if __name__ == "__main__":
    sys.exit(main())
