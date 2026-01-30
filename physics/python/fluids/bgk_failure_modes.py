#!/usr/bin/env python3
import csv
import os
import sys
from typing import List, Dict, Tuple

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python.fluids.bgk_discrete import (
    moments,
    feq_from_rho_u,
    evolve,
    E_tau,
    tv_flat,
    random_f0,
)

V = np.array([-1.0, 0.0, 1.0])


def base_f0_gradient(Nx: int, rng: np.random.Generator) -> np.ndarray:
    # Two separated blocks with opposing velocity bias
    weights = np.ones(Nx) * 0.2
    left = np.arange(0, Nx // 4)
    right = np.arange(3 * Nx // 4, Nx)
    weights[left] += 1.0
    weights[right] += 1.0
    rho = weights / weights.sum()

    f = np.zeros((Nx, 3))
    for x in range(Nx):
        if x in left:
            p = np.array([0.1, 0.2, 0.7])
        elif x in right:
            p = np.array([0.7, 0.2, 0.1])
        else:
            p = np.array([0.33, 0.34, 0.33])
        f[x, :] = rho[x] * p

    noise = rng.normal(scale=1e-3, size=f.shape)
    f = np.maximum(f + noise, 0)
    return f / np.sum(f)


def E_wrong(f: np.ndarray) -> np.ndarray:
    rho, _, _ = moments(f)
    u0 = np.zeros_like(rho)
    return feq_from_rho_u(rho, u0)


def E_tau_wrong(f: np.ndarray, omega: float, tau: int) -> np.ndarray:
    return E_wrong(evolve(f, omega, tau))


def E_rho_u_e(f: np.ndarray) -> np.ndarray:
    rho, mom, u = moments(f)
    e = f[:, 0] + f[:, 2]
    e_rel = np.zeros_like(rho)
    mask = rho >= 1e-12
    e_rel[mask] = e[mask] / rho[mask]
    u = np.clip(u, -1.0, 1.0)
    e_rel = np.clip(e_rel, 0.0, 1.0)

    p_plus = np.clip((e_rel + u) / 2.0, 0.0, 1.0)
    p_minus = np.clip((e_rel - u) / 2.0, 0.0, 1.0)
    p_zero = 1.0 - (p_plus + p_minus)
    p_zero = np.clip(p_zero, 0.0, 1.0)

    norm = p_plus + p_minus + p_zero
    norm = np.where(norm > 0, norm, 1.0)
    p_plus /= norm
    p_minus /= norm
    p_zero /= norm

    f_eq = np.zeros((rho.size, 3))
    f_eq[:, 0] = rho * p_minus
    f_eq[:, 1] = rho * p_zero
    f_eq[:, 2] = rho * p_plus
    return f_eq


def E_tau_rho_u_e(f: np.ndarray, omega: float, tau: int) -> np.ndarray:
    return E_rho_u_e(evolve(f, omega, tau))


def base_f0_energy_variation(Nx: int, rng: np.random.Generator) -> np.ndarray:
    rho = rng.dirichlet(np.ones(Nx))
    f = np.zeros((Nx, 3))
    half = Nx // 2
    for x in range(Nx):
        if x < half:
            p_plus, p_minus, p_zero = 0.4, 0.4, 0.2
        else:
            p_plus, p_minus, p_zero = 0.1, 0.1, 0.8
        f[x, :] = rho[x] * np.array([p_minus, p_zero, p_plus])
    return f / np.sum(f)


def e_rel(f: np.ndarray) -> np.ndarray:
    rho, _, _ = moments(f)
    e = f[:, 0] + f[:, 2]
    e_rel = np.zeros_like(rho)
    mask = rho >= 1e-15
    e_rel[mask] = e[mask] / rho[mask]
    return e_rel


def weighted_mean_abs(diff: np.ndarray, rho: np.ndarray) -> float:
    w = np.maximum(rho, 0)
    if float(np.sum(w)) <= 0:
        return 0.0
    return float(np.sum(w * np.abs(diff)) / np.sum(w))


def main(seed: int = 0, Nx: int = 16, Nv: int = 3, trials_per_case: int = 200) -> List[Dict]:
    if Nv != 3:
        raise ValueError("Nv must be 3")

    rng = np.random.default_rng(seed)
    tau_list = [2, 5, 10]

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    notes_dir = os.path.join(ROOT, "physics", "notes")
    os.makedirs(artifacts_dir, exist_ok=True)
    os.makedirs(notes_dir, exist_ok=True)

    csv_path = os.path.join(artifacts_dir, "bgk_failure_modes.csv")
    plot_path = os.path.join(artifacts_dir, "bgk_failure_modes.png")
    note_path = os.path.join(notes_dir, "bgk_failure_modes.md")

    rows: List[Dict] = []

    # FM1: low omega + strong gradients
    omega_fm1 = 0.0
    for trial in range(trials_per_case):
        f0 = base_f0_gradient(Nx, rng)
        for tau in tau_list:
            g = E_tau(f0, omega_fm1, tau)
            h = E_tau(g, omega_fm1, tau)
            delta = tv_flat(h, g)
            rows.append(
                {
                    "case_id": "FM1_low_omega_strong_gradient",
                    "seed": seed,
                    "trial": trial,
                    "Nx": Nx,
                    "Nv": Nv,
                    "omega": omega_fm1,
                    "tau": tau,
                    "delta": delta,
                    "delta_correct": "",
                    "delta_wrong": "",
                    "delta_missing": "",
                    "delta_extended": "",
                }
            )

    # FM2: wrong completion family
    omega_fm2 = 0.5
    for trial in range(trials_per_case):
        f0 = random_f0(Nx, Nv, rng)
        for tau in tau_list:
            f_t = evolve(f0, omega_fm2, tau)
            rho_t, _, u_t = moments(f_t)
            u_err = weighted_mean_abs(u_t, rho_t)

            g_c = E_tau(f0, omega_fm2, tau)
            h_c = E_tau(g_c, omega_fm2, tau)
            delta_correct = tv_flat(h_c, g_c)

            g_w = E_tau_wrong(f0, omega_fm2, tau)
            h_w = E_tau_wrong(g_w, omega_fm2, tau)
            delta_wrong = tv_flat(h_w, g_w)

            rows.append(
                {
                    "case_id": "FM2_wrong_equilibrium_family",
                    "seed": seed,
                    "trial": trial,
                    "Nx": Nx,
                    "Nv": Nv,
                    "omega": omega_fm2,
                    "tau": tau,
                    "delta": "",
                    "delta_correct": delta_correct,
                    "delta_wrong": delta_wrong,
                    "delta_missing": "",
                    "delta_extended": "",
                    "u_err": u_err,
                    "e_err_missing": "",
                    "e_err_extended": "",
                }
            )

    # FM3: lens missing slow mode
    omega_fm3 = 0.0
    for trial in range(trials_per_case):
        f0 = base_f0_energy_variation(Nx, rng)
        for tau in tau_list:
            f_t = evolve(f0, omega_fm3, tau)
            rho_t, _, _ = moments(f_t)
            e_true = e_rel(f_t)

            g_m = E_tau(f0, omega_fm3, tau)
            h_m = E_tau(g_m, omega_fm3, tau)
            delta_missing = tv_flat(h_m, g_m)
            e_missing = e_rel(g_m)
            e_err_missing = weighted_mean_abs(e_missing - e_true, rho_t)

            g_e = E_tau_rho_u_e(f0, omega_fm3, tau)
            h_e = E_tau_rho_u_e(g_e, omega_fm3, tau)
            delta_extended = tv_flat(h_e, g_e)
            e_extended = e_rel(g_e)
            e_err_extended = weighted_mean_abs(e_extended - e_true, rho_t)

            rows.append(
                {
                    "case_id": "FM3_lens_missing_slow_mode",
                    "seed": seed,
                    "trial": trial,
                    "Nx": Nx,
                    "Nv": Nv,
                    "omega": omega_fm3,
                    "tau": tau,
                    "delta": "",
                    "delta_correct": "",
                    "delta_wrong": "",
                    "delta_missing": delta_missing,
                    "delta_extended": delta_extended,
                    "u_err": "",
                    "e_err_missing": e_err_missing,
                    "e_err_extended": e_err_extended,
                }
            )

    # Write CSV
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "case_id",
                "seed",
                "trial",
                "Nx",
                "Nv",
                "omega",
                "tau",
                "delta",
                "delta_correct",
                "delta_wrong",
                "delta_missing",
                "delta_extended",
                "u_err",
                "e_err_missing",
                "e_err_extended",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

    # Plot mean deltas for tau=5
    def mean_for(case_id: str, key: str) -> float:
        vals = [float(r[key]) for r in rows if r["case_id"] == case_id and r["tau"] == 5 and r[key] != ""]
        return float(np.mean(vals)) if vals else float("nan")

    labels = ["FM1_delta", "FM2_u_err", "FM3_e_missing", "FM3_e_extended"]
    means = [
        mean_for("FM1_low_omega_strong_gradient", "delta"),
        mean_for("FM2_wrong_equilibrium_family", "u_err"),
        mean_for("FM3_lens_missing_slow_mode", "e_err_missing"),
        mean_for("FM3_lens_missing_slow_mode", "e_err_extended"),
    ]

    plt.figure(figsize=(8, 4.5))
    plt.bar(labels, means)
    plt.ylabel("mean delta (tau=5)")
    plt.title(f"BGK failure modes (Nx={Nx}, Nv={Nv})")
    plt.tight_layout()
    plt.savefig(plot_path, dpi=150)
    plt.close()

    # Notes
    with open(note_path, "w", encoding="utf-8") as f:
        f.write("# BGK failure modes\n\n")
        f.write("## FM1_low_omega_strong_gradient\n")
        f.write(f"Params: Nx={Nx}, Nv={Nv}, omega={omega_fm1}, taus={tau_list}, seed={seed}.\n")
        f.write("Failure: streaming dominance prevents closure idempotence improvement.\n")
        f.write("Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM1_low_omega_strong_gradient).\n\n")
        f.write("## FM2_wrong_equilibrium_family\n")
        f.write(f"Params: Nx={Nx}, Nv={Nv}, omega={omega_fm2}, taus={tau_list}, seed={seed}.\n")
        f.write("Failure: mis-specified completion kills momentum; u_err captures lost u information.\n")
        f.write("Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM2_wrong_equilibrium_family, u_err).\n\n")
        f.write("## FM3_lens_missing_slow_mode\n")
        f.write(f"Params: Nx={Nx}, Nv={Nv}, omega={omega_fm3}, taus={tau_list}, seed={seed}.\n")
        f.write("Failure: rho/u-only lens loses energy-like mode; e_err shows loss, extended lens reduces it.\n")
        f.write("Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM3_lens_missing_slow_mode, e_err_*); "
                "physics/artifacts/bgk_failure_modes.png.\n")

    entries = [
        {
            "path": "physics/artifacts/bgk_failure_modes.csv",
            "kind": "csv",
            "desc": "BGK closure failure modes",
            "created_by": "physics/python/fluids/bgk_failure_modes.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/bgk_failure_modes.png",
            "kind": "png",
            "desc": "BGK failure modes plot",
            "created_by": "physics/python/fluids/bgk_failure_modes.py",
            "seed": seed,
        },
        {
            "path": "physics/notes/bgk_failure_modes.md",
            "kind": "md",
            "desc": "BGK failure modes note",
            "created_by": "physics/python/fluids/bgk_failure_modes.py",
            "seed": seed,
        },
    ]

    print("OK: bgk failure modes")
    return entries


if __name__ == "__main__":
    main()
