# Six Birds: Physics Instantiation

This repository contains the **physics-layer instantiation** for the paper:

> **To Become a Stone with Six Birds: A Physics is A Theory**
>
> DOI: [10.5281/zenodo.18412131](https://doi.org/10.5281/zenodo.18412131)
>
> Archived at: https://zenodo.org/records/18412131

This paper demonstrates how several familiar physics layers can be expressed with the same Six-Birds dictionary: lens (what is retained), completion (how missing information is filled in), closure/packaging (the induced projection family), audit monotonicity (data processing), and route mismatch (noncommutation between evolve-then-close and close-then-evolve).

## What this repository provides

Four reproducible instantiations showing physics theories as scale-dependent closures:

- **Quantum to classical** as dephasing closure, with numerical regression checks of quantum relative-entropy data processing and a controlled unitary-vs-closure commutator
- **Kinetic to fluids** via a discrete BGK-like model with moment lens and local-equilibrium completion, including coherence trends and explicit failure regimes
- **Filtering/LES** on viscous Burgers, where filter-then-evolve differs from evolve-then-filter and the mismatch yields the canonical subgrid rewrite term
- **Nonlinear averaging/backreaction** toy illustrating that average-then-evolve differs from evolve-then-average under heterogeneity, expressed in explicit (Q/U/E) operator form

See also: [six-birds-neural](https://github.com/ioannist/six-birds-neural) for the neural/meta-layer substrate.

## Scope and limitations

These materials are intended as a reproducible "closure ledger" for comparing multi-scale theories:

- All figures and tables are generated deterministically from scripts
- A one-command build reproduces the PDF
- A small Lean4/mathlib backbone certifies key algebraic facts about finite-state lenses and closures (section implies idempotence, factorization implies commutation, total-variation contraction, and definability counting)

This is not a derivation of continuum limits or a claim about the foundations of quantum-to-classical transition.

## Requirements

- Python 3.8+
- TeX Live with `latexmk` and `pdflatex`
- `texlive-extra-utils` (provides `latexpand` for flattened TeX output)
- Lean 4 / Lake (for formal proofs, optional for paper build)

On Ubuntu/Debian:
```bash
sudo apt-get install texlive-latex-base texlive-latex-extra texlive-extra-utils latexmk
```

## Build

Build the paper PDF:

```bash
bash scripts/build_physics_paper.sh
```

Run all checks:

```bash
bash scripts/check.sh
```

## Artifacts

Generated artifacts are stored in `artifacts/` and `physics/artifacts/`.
