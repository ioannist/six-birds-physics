#!/usr/bin/env python3
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = ROOT / "physics" / "tex" / "autogen"
OUT_FILE = OUT_DIR / "lean_results.tex"

LEMMA_SPECS = [
    ("EmergenceCalc.U_uniform", "lean/EmergenceCalc/Physics/UniformLift.lean", "uniform lift/completion for equal-fiber partition lens (Prod.fst : X×Fin m → X)"),
    ("EmergenceCalc.section_uniform", "lean/EmergenceCalc/Physics/UniformLift.lean", "proves Q_f (U_uniform ν) = ν (section axiom)"),
    ("EmergenceCalc.E_idempotent_uniform", "lean/EmergenceCalc/Physics/UniformLift.lean", "idempotence of the induced closure E = U∘Q for uniform lift"),
    ("EmergenceCalc.FactorsThrough", "lean/EmergenceCalc/Physics/Factorization.lean", "factorization property: micro dynamics respects coarse map and preserves uniform fibers"),
    ("EmergenceCalc.commutes_of_factorsThrough", "lean/EmergenceCalc/Physics/Factorization.lean", "commutation E(T μ)=T(E μ) under factorization"),
    ("EmergenceCalc.TV_Q_f_le", "lean/EmergenceCalc/Physics/TotalVariation.lean", "total variation contraction under deterministic pushforward"),
    ("EmergenceCalc.card_DefPred", "lean/EmergenceCalc/Physics/DefinabilityCount.lean", "fiber-constant predicates count = 2^(card X) under surjective lens"),
    ("EmergenceCalc.card_DefPred_range", "lean/EmergenceCalc/Physics/DefinabilityCount.lean", "generalization: count = 2^(card (range f))"),
    ("EmergenceCalc.card_DefPred_fst", "lean/EmergenceCalc/Physics/DefinabilityCount.lean", "specialization for Prod.fst : X×Fin m → X"),
]


def read_text(rel_path: str) -> str:
    path = ROOT / rel_path
    if not path.exists():
        raise SystemExit(f"Missing file: {rel_path}")
    return path.read_text(encoding="utf-8", errors="ignore")


def main() -> None:
    for name, rel_path, _ in LEMMA_SPECS:
        text = read_text(rel_path)
        simple = name.split(".")[-1]
        if name not in text and simple not in text:
            raise SystemExit(f"Missing lemma '{name}' in {rel_path}")

    OUT_DIR.mkdir(parents=True, exist_ok=True)

    lines = []
    def esc_tt(s: str) -> str:
        return s.replace("_", "\\_")

    def esc_text(s: str) -> str:
        # Handle common patterns
        s = s.replace("2^(card X)", "$2^{\\text{card }X}$")
        s = s.replace("2^(card (range f))", "$2^{\\text{card(range }f)}$")
        return (
            s.replace("_", "\\_")
            .replace("ν", "$\\nu$")
            .replace("μ", "$\\mu$")
            .replace("∘", "$\\circ$")
            .replace("×", "$\\times$")
            .replace("→", "$\\to$")
        )

    lines.append("\\subsection*{Lean coverage}")
    lines.append("\\begin{itemize}[leftmargin=*]")
    for name, rel_path, desc in LEMMA_SPECS:
        # Break into multiple lines for readability
        lines.append("  \\item \\texttt{" + esc_tt(name) + "}\\\\")
        lines.append("    " + esc_text(desc) + ".\\\\")
        lines.append("    {\\footnotesize\\texttt{" + esc_tt(rel_path) + "}}")
    lines.append("\\end{itemize}")
    lines.append("")
    lines.append("\\subsection*{Build command}")
    lines.append("\\begin{verbatim}")
    lines.append("cd lean && lake build")
    lines.append("\\end{verbatim}")

    toolchain_path = ROOT / "lean" / "lean-toolchain"
    mathlib_pin = ROOT / "lean" / "mathlib_pin.txt"
    if toolchain_path.exists() or mathlib_pin.exists():
        lines.append("")
        lines.append("\\subsection*{Toolchain pins}")
        lines.append("\\begin{verbatim}")
        if toolchain_path.exists():
            lines.append(f"lean/lean-toolchain: {toolchain_path.read_text(encoding='utf-8').strip()}")
        if mathlib_pin.exists():
            lines.append(f"lean/mathlib_pin.txt: {mathlib_pin.read_text(encoding='utf-8').strip()}")
        lines.append("\\end{verbatim}")

    OUT_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
