#!/usr/bin/env python3
import json
import os
import sys
from typing import Dict, List

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python.quantum.core import (
    random_density_matrix,
    validate_density_matrix,
    quantum_relative_entropy,
    apply_kraus,
    kraus_dephasing,
    kraus_depolarizing,
    kraus_projective_measurement_standard,
    random_cptp_kraus,
)


def main(seed: int = 0) -> List[Dict]:
    rng = np.random.default_rng(seed)
    d_list = [2, 3, 4]
    trials = 50

    tol = 1e-10
    max_trace_err = 0.0
    worst_min_eig = 1.0
    clamp_count = 0
    worst_completeness = 0.0
    max_abs_self = 0.0
    nan_count = 0

    for d in d_list:
        for _ in range(trials):
            rho = random_density_matrix(d, rng)
            sigma = random_density_matrix(d, rng)

            s_self, diag_self = quantum_relative_entropy(rho, rho)
            max_abs_self = max(max_abs_self, abs(s_self))
            s_rs, diag_rs = quantum_relative_entropy(rho, sigma)
            if not np.isfinite(s_rs):
                nan_count += 1
            clamp_count += diag_self.get("clipped_rho", 0) + diag_self.get("clipped_sigma", 0)
            clamp_count += diag_rs.get("clipped_rho", 0) + diag_rs.get("clipped_sigma", 0)

            channels = [
                kraus_dephasing(d, p=0.3),
                kraus_depolarizing(d, p=0.2),
                kraus_projective_measurement_standard(d),
            ]
            rand_kraus, diag = random_cptp_kraus(d, r=4, rng=rng)
            worst_completeness = max(worst_completeness, diag["completeness_error"])
            clamp_count += diag["clipped_count"]
            channels.append(rand_kraus)

            for ks in channels:
                out = apply_kraus(rho, ks)
                info = validate_density_matrix(out, tol=tol)
                max_trace_err = max(max_trace_err, info["trace_err"])
                worst_min_eig = min(worst_min_eig, info["min_eig"])
                if not info["is_valid"]:
                    raise ValueError("Invalid output density matrix")

    if nan_count != 0:
        raise ValueError("NaN detected in relative entropy")
    if max_abs_self > 1e-8:
        raise ValueError(f"S(rho||rho) too large: {max_abs_self}")

    summary = {
        "seed": seed,
        "dims": d_list,
        "trials": trials,
        "tol": tol,
        "max_trace_err": max_trace_err,
        "worst_min_eig": worst_min_eig,
        "clamp_count": int(clamp_count),
        "worst_completeness_error": worst_completeness,
        "max_abs_self_entropy": max_abs_self,
        "nan_count": nan_count,
    }

    out_path = os.path.join(ROOT, "physics", "artifacts", "quantum_checks_summary.json")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, sort_keys=True)
        f.write("\n")

    entries = [
        {
            "path": "physics/artifacts/quantum_checks_summary.json",
            "kind": "json",
            "desc": "Quantum checks summary",
            "created_by": "physics/python/quantum/_checks.py",
            "seed": seed,
        }
    ]

    print("OK: quantum checks")
    return entries


if __name__ == "__main__":
    main()
