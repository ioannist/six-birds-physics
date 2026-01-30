# Failure modes (counterexamples)

## FM1 — Macro preserved, micro funnel (commutation fails)
Parameters: K=6, m=10, N=60, tau=1. Lens: f_std(z)=z//m. Seeds: [0,1,2,3,4].
What failed: commutation (coarse-then-evolve vs evolve-then-coarse).
Evidence pointers: artifacts/failure_modes.csv with mode_id=FM1_macro_preserved_micro_funnel (field mismatch_tv).

## FM2 — Bad completion (non-section) makes idempotence fail
Parameters: K=6, m=10, N=60, tau=0. Lens: f_std(z)=z//m. Seeds: [0,1,2,3,4].
What failed: idempotence (E_bad(E_bad(μ)) != E_bad(μ)).
Evidence pointers: artifacts/failure_modes.csv with mode_id=FM2_bad_completion_nonsection (fields idem_tv, macro_drift_tv).

## FM3 — Misaligned lens vs metastable structure (mixing knob doesn’t help much)
Parameters: K=6, m=10, N=60, gamma=0.7, lam=0.2. Alphas: 0.0..1.0 step 0.1. Taus: [2,5,10]. Seeds: [0,1,2,3,4].
What failed: audit monotonicity intuition (reduced improvement with increasing alpha for misaligned lens).
Evidence pointers: artifacts/failure_modes.csv with mode_id=FM3_misaligned_lens and mode_id=FM3_baseline_for_comparison; plot artifacts/failure_modes.png.
