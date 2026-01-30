# BGK failure modes

## FM1_low_omega_strong_gradient
Params: Nx=16, Nv=3, omega=0.0, taus=[2, 5, 10], seed=50.
Failure: streaming dominance prevents closure idempotence improvement.
Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM1_low_omega_strong_gradient).

## FM2_wrong_equilibrium_family
Params: Nx=16, Nv=3, omega=0.5, taus=[2, 5, 10], seed=50.
Failure: mis-specified completion kills momentum; u_err captures lost u information.
Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM2_wrong_equilibrium_family, u_err).

## FM3_lens_missing_slow_mode
Params: Nx=16, Nv=3, omega=0.0, taus=[2, 5, 10], seed=50.
Failure: rho/u-only lens loses energy-like mode; e_err shows loss, extended lens reduces it.
Evidence: physics/artifacts/bgk_failure_modes.csv (case_id=FM3_lens_missing_slow_mode, e_err_*); physics/artifacts/bgk_failure_modes.png.
