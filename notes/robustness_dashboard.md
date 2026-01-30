# Math robustness dashboard

## Evidence assets
- Lean modules:
  - lean/EmergenceCalc/Emergence/Lens.lean — Q_f, Q_f_pure, Q_id, Q_comp
  - lean/EmergenceCalc/Emergence/Completion.lean — SectionAxiom, E, E_idempotent
  - lean/EmergenceCalc/Emergence/RouteMismatch.lean — routeMismatch, Commutes, commutes_of_intertwine
  - lean/EmergenceCalc/Emergence/Info.lean — KL wrapper; DPI_KL_Qf (Prop + TODO)
- Simulation assets:
  - artifacts/dpi_kl_summary.csv; artifacts/dpi_kl_hist.png
  - artifacts/idempotence_defect_summary.csv; artifacts/idempotence_defect.png
  - artifacts/failure_modes.csv; artifacts/failure_modes.png; notes/failure_modes.md
  - artifacts/definability_ratio.csv; artifacts/definability_ratio.png

## Status counts
- Sim:DPI: 10
- Sim:Idempotence: 68
- Sim:Definability: 7
- CE:FailureModes: 12
- Lean:Core: 13
- Lean:Stub: 21
- Unknown: 22

## High-risk claim watchlist
- rem:tk-interoperability — Unknown — Introduction
- remark@L233 — Sim:DPI — Conventions and notation > Paths, time reversal, and relative entropy
- def:tk-theory-package — Unknown — Conventions and notation > A unified theory package viewpoint
- thm:T-IC-02 — Lean:Core, Lean:Stub, Sim:Idempotence — Idempotent endomaps and induced closures > Dynamics-induced empirical endomaps
- thm:T-IC-01 — Lean:Core, Lean:Stub, Sim:Idempotence — Idempotent endomaps and induced closures > Dynamics-induced empirical endomaps
- remark@L698 — Lean:Core, Lean:Stub, Sim:Idempotence — Idempotent endomaps and induced closures > Dynamics-induced empirical endomaps
- remark@L873 — Lean:Stub, Sim:DPI — Arrow-of-time as path reversal asymmetry
- definition@L878 — Lean:Stub, Sim:DPI — Arrow-of-time as path reversal asymmetry
- lemma@L1060 — Sim:Definability — Generic extension and the finite forcing lemma > Finite forcing: generic extensions are non-definable
- thm:ect-summary — Sim:Idempotence — Appendix E: Toolkit theory---defects > Summary: slots and divergence consequence
- def:ect-bal — Sim:Idempotence — Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay
- lem:ect-bal-kmass — Sim:Idempotence — Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay
- cor:ect-bal-icap — Sim:Idempotence — Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay
- lem:ect-shrink — Sim:Idempotence — Appendix E: Toolkit theory---defects > Coercivity from feasibility gating (P2)

## Top 5 remaining high-risk gaps
- def:tk-theory-package — context: Conventions and notation > A unified theory package viewpoint; missing: unknown
- rem:tk-interoperability — context: Introduction; missing: unknown
- cor:ect-bal-icap — context: Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay; missing: no lean tag
- def:ect-bal — context: Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay; missing: no lean tag
- lem:ect-bal-kmass — context: Appendix E: Toolkit theory---defects > Dissipative atoms and semigroup decay; missing: no lean tag
