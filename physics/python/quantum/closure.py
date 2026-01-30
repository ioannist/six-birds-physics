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
    trace_distance,
    symmetrize_hermitian,
    assert_density_matrix,
)


def dephase_standard(rho: np.ndarray) -> np.ndarray:
    d = rho.shape[0]
    return symmetrize_hermitian(rho * np.eye(d))


def partial_dephase(rho: np.ndarray, lam: float) -> np.ndarray:
    if lam < 0 or lam > 1:
        raise ValueError("lam must be in [0,1]")
    return symmetrize_hermitian((1.0 - lam) * rho + lam * dephase_standard(rho))


def random_hermitian(d: int, rng: np.random.Generator) -> np.ndarray:
    A = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    return symmetrize_hermitian(A)


def unitary_from_hermitian(H: np.ndarray, t: float) -> np.ndarray:
    evals, evecs = np.linalg.eigh(H)
    phase = np.exp(-1j * evals * t)
    return evecs @ np.diag(phase) @ np.conjugate(evecs).T


def evolve_unitary(rho: np.ndarray, H: np.ndarray, t: float) -> np.ndarray:
    U = unitary_from_hermitian(H, t)
    out = U @ rho @ np.conjugate(U).T
    out = symmetrize_hermitian(out)
    tr = float(np.trace(out).real)
    if tr <= 0:
        raise ValueError("Non-positive trace after unitary evolution")
    if abs(tr - 1.0) > 1e-12:
        out = out / tr
    return symmetrize_hermitian(out)


def route_mismatch(rho: np.ndarray, H: np.ndarray, t: float, lam: float) -> float:
    A = partial_dephase(evolve_unitary(rho, H, t), lam)
    B = evolve_unitary(partial_dephase(rho, lam), H, t)
    return trace_distance(A, B)


def main(seed: int = 0, d: int = 4) -> List[Dict]:
    rng = np.random.default_rng(seed)
    rho = random_density_matrix(d, rng)
    H = random_hermitian(d, rng)

    lam_list = [0.5, 0.7, 0.85, 0.93, 0.97, 1.0]
    t_list = np.linspace(0.0, 10.0, 200)

    # Idempotence defects
    idem_defs = []
    for lam in lam_list:
        x = partial_dephase(rho, lam)
        y = partial_dephase(x, lam)
        idem_def = trace_distance(y, x)
        idem_defs.append(idem_def)
    for i in range(len(idem_defs) - 1):
        if idem_defs[i + 1] > idem_defs[i] + 1e-12:
            raise ValueError("Idempotence defect not monotone decreasing")
    if idem_defs[-1] > 1e-12:
        raise ValueError("Idempotence defect at lam=1 too large")

    # Route mismatch grid
    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    os.makedirs(artifacts_dir, exist_ok=True)
    csv_path = os.path.join(artifacts_dir, "quantum_route_mismatch.csv")
    plot_idem_path = os.path.join(artifacts_dir, "quantum_closure_idempotence.png")
    plot_mismatch_path = os.path.join(artifacts_dir, "quantum_route_mismatch.png")

    rows = []
    max_mismatch = {lam: 0.0 for lam in lam_list}
    nan_count = 0

    for lam in lam_list:
        for t in t_list:
            m = route_mismatch(rho, H, float(t), lam)
            if not np.isfinite(m):
                nan_count += 1
            max_mismatch[lam] = max(max_mismatch[lam], float(m))
            rows.append({"seed": seed, "d": d, "lam": lam, "t": float(t), "mismatch": float(m)})

    if nan_count != 0:
        raise ValueError("NaN/inf in route mismatch")

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=["seed", "d", "lam", "t", "mismatch"])
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    plt.figure(figsize=(6.5, 4.0))
    plt.plot(lam_list, idem_defs, marker="o")
    plt.xlabel("lambda")
    plt.ylabel("idempotence defect")
    plt.title(f"Quantum closure idempotence (seed={seed}, d={d})")
    plt.tight_layout()
    plt.savefig(plot_idem_path, dpi=150)
    plt.close()

    plt.figure(figsize=(7.0, 4.5))
    for lam in lam_list:
        y = [row["mismatch"] for row in rows if row["lam"] == lam]
        plt.plot(t_list, y, label=f"lam={lam}")
    plt.xlabel("t")
    plt.ylabel("route mismatch")
    plt.title(f"Quantum route mismatch (seed={seed}, d={d})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(plot_mismatch_path, dpi=150)
    plt.close()

    entries = [
        {
            "path": "physics/artifacts/quantum_closure_idempotence.png",
            "kind": "png",
            "desc": "Quantum closure idempotence plot",
            "created_by": "physics/python/quantum/closure.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/quantum_route_mismatch.png",
            "kind": "png",
            "desc": "Quantum route mismatch plot",
            "created_by": "physics/python/quantum/closure.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/quantum_route_mismatch.csv",
            "kind": "csv",
            "desc": "Quantum route mismatch grid",
            "created_by": "physics/python/quantum/closure.py",
            "seed": seed,
        },
    ]

    print("OK: quantum closure")
    return entries


if __name__ == "__main__":
    main()
