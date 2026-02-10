# TechRxiv QA Report

## Build Verification

- **Build command**: `cd physics/tex && latexmk -pdf -interaction=nonstopmode physics_instantiation.tex`
- **Result**: SUCCESS (31 pages, 1,027,698 bytes)
- **Undefined references**: 0
- **Undefined citations**: 0
- **Missing figures**: 0
- **Overfull boxes**: 4 (cosmetic only, no content loss)

## Figures Verified Present (10/10)

All referenced in `\includegraphics` via autogen manifest and confirmed at `physics/tex/figures/`:

1. smoke_core.png
2. quantum_dpi_hist.png
3. quantum_closure_idempotence.png
4. quantum_route_mismatch.png
5. bgk_idempotence_defect.png
6. bgk_failure_modes.png
7. les_route_mismatch.png
8. les_subgrid_term.png
9. gravity_backreaction.png
10. gravity_packaging_mismatch.png

## Tables Verified (8/8)

1. tab:quantum-dpi-summary (Section 4 -- Quantum DPI audit)
2. tab:bgk-endpoints (Section 5 -- BGK idempotence endpoints)
3. tab:bgk-failure-modes (Section 5 -- BGK failure modes)
4. tab:les-route-mismatch (Section 6 -- LES route mismatch)
5. tab:les-subgrid-term (Section 6 -- LES subgrid term)
6. tab:gravity-backreaction (Section 7 -- Gravity backreaction)
7. tab:gravity-packaging (Section 7 -- Gravity packaging mismatch)
8. tab:certificate-ledger (Appendix B -- Cross-domain certificate ledger)

## Reproducibility Pipeline

| Command | Status |
|---------|--------|
| `python physics/python/run_all.py` | PASS (22 artifacts registered) |
| `cd lean && lake build` | PASS (7902 jobs, linter warnings only) |

### Individual suite results:

| Suite | Script | Status |
|-------|--------|--------|
| Smoke test | `_smoke_test.py` | PASS |
| Quantum checks | `quantum/_checks.py` | PASS |
| Quantum DPI | `quantum/dpi.py` | PASS |
| Quantum closure | `quantum/closure.py` | PASS |
| BGK discrete | `fluids/bgk_discrete.py` | PASS |
| BGK failure modes | `fluids/bgk_failure_modes.py` | PASS |
| LES Burgers | `les/burgers_1d.py` | PASS |
| LES subgrid | `les/subgrid_term.py` | PASS |
| Gravity backreaction | `gravity/backreaction_toy.py` | PASS |
| Gravity packaging | `gravity/packaging_view.py` | PASS |

## Changes Made (TechRxiv Preparation)

### Cover Page Template
- Added `\usepackage{orcidlink}` and inline ORCID display
- Added affiliation helper macros (HAL-compatible author block)
- Updated `\author{}` to use `\orcidlink{0009-0009-7659-5964}`
- Set `\affiliation{}` to empty (matches DE paper template)
- Added version/revision date line with Zenodo DOI
- Updated footer: `Automorph Inc., Wilmington, DE, USA | ioannis@automorph.io | CC-BY 4.0 | Preprint --- not peer reviewed`
- Changed `\usepackage{hyperref}` to `\usepackage[hidelinks]{hyperref}`

### Scope-Framing (CS/Tech Positioning)
- Rewrote abstract opening to lead with "reproducible computational framework" and "Lean 4 mechanized proofs"
- Expanded keywords from 5 to 11 CS/IT-aligned terms
- Added theory disambiguation sentence to introduction ("This is a research article...")
- Added "Computational contributions" paragraph listing 4 CS deliverables
- Added code DOI (10.5281/zenodo.18451876) to Code availability sections

### Declarations Section
- Added full Declarations section after Discussion: corresponding author, competing interests, funding, ethics, data availability, code availability, author contributions, AI/LLM disclosure

### Language Pass
- "keep the story honest" → "prevent overclaiming" (08_discussion_limitations.tex)
- "Toy model:" → "Minimal model:" (07_gravity_backreaction.tex subsection heading)
- "toy specification" → "model specification" (05_kinetic_to_fluids.tex)

## Human Must-Fill Items

None. All DOIs are resolved and metadata is complete.
