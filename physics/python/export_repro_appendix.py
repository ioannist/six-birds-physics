#!/usr/bin/env python3
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REQUIRED = ROOT / "physics" / "artifacts" / "required_artifacts.txt"
OUT_DIR = ROOT / "physics" / "tex" / "autogen"
OUT_FILE = OUT_DIR / "repro.tex"

GENERATORS = {
    "physics/artifacts/manifest.json": "physics/python/run_all.py",
    "physics/artifacts/smoke_core.csv": "physics/python/_smoke_test.py (via physics/python/run_all.py)",
    "physics/artifacts/smoke_core.png": "physics/python/_smoke_test.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_checks_summary.json": "physics/python/quantum/_checks.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_dpi_summary.csv": "physics/python/quantum/dpi.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_dpi_hist.png": "physics/python/quantum/dpi.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_closure_idempotence.png": "physics/python/quantum/closure.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_route_mismatch.csv": "physics/python/quantum/closure.py (via physics/python/run_all.py)",
    "physics/artifacts/quantum_route_mismatch.png": "physics/python/quantum/closure.py (via physics/python/run_all.py)",
    "physics/artifacts/bgk_idempotence_defect.csv": "physics/python/fluids/bgk_discrete.py (via physics/python/run_all.py)",
    "physics/artifacts/bgk_summary.csv": "physics/python/fluids/bgk_discrete.py (via physics/python/run_all.py)",
    "physics/artifacts/bgk_idempotence_defect.png": "physics/python/fluids/bgk_discrete.py (via physics/python/run_all.py)",
    "physics/artifacts/bgk_failure_modes.csv": "physics/python/fluids/bgk_failure_modes.py (via physics/python/run_all.py)",
    "physics/artifacts/bgk_failure_modes.png": "physics/python/fluids/bgk_failure_modes.py (via physics/python/run_all.py)",
    "physics/artifacts/les_route_mismatch.csv": "physics/python/les/burgers_1d.py (via physics/python/run_all.py)",
    "physics/artifacts/les_route_mismatch.png": "physics/python/les/burgers_1d.py (via physics/python/run_all.py)",
    "physics/artifacts/les_subgrid_term.csv": "physics/python/les/subgrid_term.py (via physics/python/run_all.py)",
    "physics/artifacts/les_subgrid_term.png": "physics/python/les/subgrid_term.py (via physics/python/run_all.py)",
    "physics/artifacts/gravity_backreaction.csv": "physics/python/gravity/backreaction_toy.py (via physics/python/run_all.py)",
    "physics/artifacts/gravity_backreaction.png": "physics/python/gravity/backreaction_toy.py (via physics/python/run_all.py)",
    "physics/artifacts/gravity_packaging_mismatch.csv": "physics/python/gravity/packaging_view.py (via physics/python/run_all.py)",
    "physics/artifacts/gravity_packaging_mismatch.png": "physics/python/gravity/packaging_view.py (via physics/python/run_all.py)",
}


def main() -> None:
    if not REQUIRED.exists():
        raise SystemExit("Missing required artifacts list: physics/artifacts/required_artifacts.txt")

    required_lines = []
    for line in REQUIRED.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        required_lines.append(line)

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with OUT_FILE.open("w", encoding="utf-8") as f:
        f.write("\\subsection*{Commands}\n")
        f.write("\\begin{verbatim}\n")
        f.write("bash scripts/check_physics.sh\n")
        f.write("bash scripts/build_physics_paper.sh\n")
        f.write("\\end{verbatim}\n\n")

        f.write("\\subsection*{Required physics artifacts}\n")
        f.write("\\begin{verbatim}\n")
        for line in required_lines:
            f.write(f"{line}\n")
        f.write("\\end{verbatim}\n\n")

        f.write("\\subsection*{Generation map}\n")
        f.write("\\small\n")
        f.write("\\begin{itemize}[leftmargin=*,itemsep=0pt]\n")
        for line in required_lines:
            gen = GENERATORS.get(line, "(unknown)")
            # Extract just the artifact name and generator script name
            artifact = line.split("/")[-1]
            gen_short = gen.replace("physics/python/", "").replace(" (via physics/python/run_all.py)", " (via run\\_all.py)")
            # Use footnotesize for long lines to prevent overfull hbox
            f.write(f"  \\item {{\\footnotesize \\texttt{{{artifact.replace('_', chr(92)+'_')}}} $\\leftarrow$ \\texttt{{{gen_short.replace('_', chr(92)+'_')}}}}}\n")
        f.write("\\end{itemize}\n")
        f.write("\\normalsize\n")


if __name__ == "__main__":
    main()
