#!/usr/bin/env python3
import os
import sys
from typing import List, Dict

import numpy as np
import matplotlib.pyplot as plt

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python.core import lens_partition, Q_f, U_uniform, tv, kl
from physics.python.io import write_csv, save_plot, update_manifest


def main(seed: int = 0) -> List[Dict]:
    rng = np.random.default_rng(seed)
    N = 12
    K = 3
    _, fibers = lens_partition(N, K, mode="contiguous")

    mu = rng.dirichlet(np.ones(N))
    nu = Q_f(mu, fibers)
    mu_hat = U_uniform(nu, fibers)

    tv_val = tv(mu, mu_hat)
    kl_val = kl(mu, mu_hat)

    artifacts_dir = os.path.join(ROOT, "physics", "artifacts")
    csv_path = os.path.join(artifacts_dir, "smoke_core.csv")
    png_path = os.path.join(artifacts_dir, "smoke_core.png")

    write_csv(csv_path, [{"N": N, "K": K, "tv": tv_val, "kl": kl_val}], sort_keys=True)

    x = np.arange(N)
    plt.figure(figsize=(8, 3.5))
    plt.bar(x - 0.2, mu, width=0.4, label="mu", alpha=0.8)
    plt.bar(x + 0.2, mu_hat, width=0.4, label="mu_hat", alpha=0.6)
    plt.xlabel("micro state")
    plt.ylabel("probability")
    plt.legend()
    save_plot(png_path)

    entries = [
        {
            "path": "physics/artifacts/smoke_core.csv",
            "kind": "csv",
            "desc": "Smoke test CSV for core calculus",
            "created_by": "physics/python/_smoke_test.py",
            "seed": seed,
        },
        {
            "path": "physics/artifacts/smoke_core.png",
            "kind": "png",
            "desc": "Smoke test plot for core calculus",
            "created_by": "physics/python/_smoke_test.py",
            "seed": seed,
        },
    ]

    manifest_path = os.path.join(artifacts_dir, "manifest.json")
    update_manifest(manifest_path, entries)

    print(f"tv {tv_val} kl {kl_val}")
    return entries


if __name__ == "__main__":
    main()
