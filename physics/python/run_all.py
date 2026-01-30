#!/usr/bin/env python3
import datetime as _dt
import os
import sys
from typing import List, Dict

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from physics.python import io
from physics.python import _smoke_test
from physics.python.quantum import _checks as quantum_checks
from physics.python.quantum import dpi as quantum_dpi
from physics.python.quantum import closure as quantum_closure
from physics.python.fluids import bgk_discrete
from physics.python.fluids import bgk_failure_modes
from physics.python.les import burgers_1d
from physics.python.les import subgrid_term
from physics.python.gravity import backreaction_toy
from physics.python.gravity import packaging_view


def main(seed_base: int = 0) -> int:
    entries: List[Dict] = []

    print("run: physics/python/_smoke_test.py")
    entries.extend(_smoke_test.main(seed=seed_base))

    print("run: physics/python/quantum/_checks.py")
    entries.extend(quantum_checks.main(seed=seed_base + 10))

    print("run: physics/python/quantum/dpi.py")
    entries.extend(quantum_dpi.main(seed=seed_base + 20, trials_per_dim=300, tol=1e-8, eps=1e-12))

    print("run: physics/python/quantum/closure.py")
    entries.extend(quantum_closure.main(seed=seed_base + 30, d=4))

    print("run: physics/python/fluids/bgk_discrete.py")
    entries.extend(bgk_discrete.main(seed=seed_base + 40, Nx=16, Nv=3, trials_per_combo=200))

    print("run: physics/python/fluids/bgk_failure_modes.py")
    entries.extend(bgk_failure_modes.main(seed=seed_base + 50, Nx=16, Nv=3, trials_per_case=200))

    print("run: physics/python/les/burgers_1d.py")
    entries.extend(burgers_1d.main(seed=seed_base + 60, N=128, nu=0.1, dt=0.002, tmax=1.0))

    print("run: physics/python/les/subgrid_term.py")
    entries.extend(subgrid_term.main(seed=seed_base + 70, N=128, nu=0.1, dt=0.002, tmax=1.0))

    print("run: physics/python/gravity/backreaction_toy.py")
    entries.extend(backreaction_toy.main(seed=seed_base + 80, M=20000))

    print("run: physics/python/gravity/packaging_view.py")
    entries.extend(packaging_view.main(seed=seed_base + 90, Nbin=401))

    manifest_path = os.path.join(ROOT, "physics", "artifacts", "manifest.json")
    io.update_manifest(manifest_path, entries)

    data = io.load_manifest(manifest_path)
    meta = data.get("meta", {})
    meta.update(
        {
            "generated_at": _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
            "generator": "physics/python/run_all.py",
            "seed_base": seed_base,
        }
    )
    data["meta"] = meta
    with open(manifest_path, "w", encoding="utf-8") as f:
        import json

        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")

    print(f"registered {len(entries)} artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
