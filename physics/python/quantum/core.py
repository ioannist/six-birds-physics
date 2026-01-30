#!/usr/bin/env python3
"""Finite-dimensional quantum utilities (numpy-only)."""
from __future__ import annotations

import math
from typing import List, Tuple, Dict

import numpy as np


def dagger(A: np.ndarray) -> np.ndarray:
    """Conjugate transpose."""
    return np.conjugate(A).T


def symmetrize_hermitian(A: np.ndarray) -> np.ndarray:
    """Return the Hermitian part of A."""
    return 0.5 * (A + dagger(A))


def eigen_hermitian(A: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Eigen-decomposition for Hermitian matrices."""
    return np.linalg.eigh(A)


def random_density_matrix(
    d: int, rng: np.random.Generator, rank: int | None = None
) -> np.ndarray:
    """Sample a random density matrix via Ginibre/Wishart."""
    if rank is None:
        rank = d
    if rank <= 0 or rank > d:
        raise ValueError("rank must be in 1..d")
    G = rng.normal(size=(d, rank)) + 1j * rng.normal(size=(d, rank))
    A = G @ dagger(G)
    A = symmetrize_hermitian(A)
    tr = np.trace(A)
    if tr == 0:
        raise ValueError("trace is zero in random_density_matrix")
    rho = A / tr
    return symmetrize_hermitian(rho)


def validate_density_matrix(rho: np.ndarray, tol: float = 1e-10) -> Dict[str, float | bool]:
    """Validate density matrix properties and return diagnostics."""
    shape_ok = rho.ndim == 2 and rho.shape[0] == rho.shape[1]
    if not shape_ok:
        return {
            "shape_ok": False,
            "hermitian_err": float("inf"),
            "trace_err": float("inf"),
            "min_eig": float("-inf"),
            "is_psd": False,
            "is_valid": False,
        }
    rho_h = symmetrize_hermitian(rho)
    herm_err = float(np.linalg.norm(rho - rho_h, ord="fro"))
    tr = float(np.trace(rho_h).real)
    trace_err = abs(tr - 1.0)
    evals, _ = eigen_hermitian(rho_h)
    min_eig = float(np.min(evals))
    is_psd = min_eig >= -tol
    is_valid = shape_ok and herm_err <= tol and trace_err <= tol and is_psd
    return {
        "shape_ok": shape_ok,
        "hermitian_err": herm_err,
        "trace_err": trace_err,
        "min_eig": min_eig,
        "is_psd": is_psd,
        "is_valid": is_valid,
    }


def assert_density_matrix(rho: np.ndarray, tol: float = 1e-10) -> None:
    """Raise if rho is not a valid density matrix."""
    info = validate_density_matrix(rho, tol=tol)
    if not info["is_valid"]:
        raise ValueError(
            f"Invalid density matrix: herm_err={info['hermitian_err']:.3e}, "
            f"trace_err={info['trace_err']:.3e}, min_eig={info['min_eig']:.3e}"
        )


def psd_matrix_log(rho: np.ndarray, eps: float = 1e-12) -> Tuple[np.ndarray, int]:
    """Matrix log for PSD matrices with eigenvalue clamping."""
    rho_h = symmetrize_hermitian(rho)
    evals, evecs = eigen_hermitian(rho_h)
    clipped = np.sum(evals < eps)
    evals = np.maximum(evals, eps)
    log_diag = np.diag(np.log(evals))
    log_rho = evecs @ log_diag @ dagger(evecs)
    return symmetrize_hermitian(log_rho), int(clipped)


def psd_matrix_sqrt(rho: np.ndarray, eps: float = 0.0) -> np.ndarray:
    """Matrix square root for PSD matrices."""
    rho_h = symmetrize_hermitian(rho)
    evals, evecs = eigen_hermitian(rho_h)
    evals = np.maximum(evals, eps)
    sqrt_diag = np.diag(np.sqrt(evals))
    return symmetrize_hermitian(evecs @ sqrt_diag @ dagger(evecs))


def psd_matrix_invsqrt(rho: np.ndarray, eps: float = 1e-12) -> Tuple[np.ndarray, int]:
    """Matrix inverse square root for PSD matrices with clamping."""
    rho_h = symmetrize_hermitian(rho)
    evals, evecs = eigen_hermitian(rho_h)
    clipped = np.sum(evals < eps)
    evals = np.maximum(evals, eps)
    invsqrt_diag = np.diag(1.0 / np.sqrt(evals))
    invsqrt = evecs @ invsqrt_diag @ dagger(evecs)
    return symmetrize_hermitian(invsqrt), int(clipped)


def quantum_relative_entropy(
    rho: np.ndarray, sigma: np.ndarray, eps: float = 1e-12
) -> Tuple[float, Dict[str, int]]:
    """Quantum relative entropy S(rho||sigma)."""
    log_rho, clip_rho = psd_matrix_log(rho, eps=eps)
    log_sigma, clip_sigma = psd_matrix_log(sigma, eps=eps)
    val = np.trace(rho @ (log_rho - log_sigma)).real
    if not math.isfinite(val):
        raise ValueError("Non-finite relative entropy")
    return float(val), {"clipped_rho": clip_rho, "clipped_sigma": clip_sigma}


def trace_distance(rho: np.ndarray, sigma: np.ndarray) -> float:
    """Trace distance between two density matrices."""
    delta = symmetrize_hermitian(rho - sigma)
    evals, _ = eigen_hermitian(delta)
    return 0.5 * float(np.sum(np.abs(evals)))


def fidelity(rho: np.ndarray, sigma: np.ndarray, eps: float = 1e-12) -> float:
    """Uhlmann fidelity (optional helper)."""
    sqrt_rho = psd_matrix_sqrt(rho, eps=eps)
    inner = symmetrize_hermitian(sqrt_rho @ sigma @ sqrt_rho)
    sqrt_inner = psd_matrix_sqrt(inner, eps=eps)
    val = float(np.trace(sqrt_inner).real)
    return max(0.0, min(1.0, val * val))


def apply_kraus(rho: np.ndarray, kraus: List[np.ndarray]) -> np.ndarray:
    """Apply a CPTP map given by Kraus operators."""
    out = np.zeros_like(rho, dtype=complex)
    for K in kraus:
        out = out + K @ rho @ dagger(K)
    out = symmetrize_hermitian(out)
    tr = float(np.trace(out).real)
    if tr <= 0:
        raise ValueError("Non-positive trace after channel application")
    if abs(tr - 1.0) > 1e-10:
        out = out / tr
    return symmetrize_hermitian(out)


def kraus_completeness_error(kraus: List[np.ndarray]) -> float:
    """Frobenius norm of \u03a3 K\u2020K - I."""
    d = kraus[0].shape[0]
    acc = np.zeros((d, d), dtype=complex)
    for K in kraus:
        acc = acc + dagger(K) @ K
    diff = acc - np.eye(d)
    return float(np.linalg.norm(diff, ord="fro"))


def random_cptp_kraus(
    d: int, r: int, rng: np.random.Generator, eps: float = 1e-12
) -> Tuple[List[np.ndarray], Dict[str, float | int]]:
    """Generate a random CPTP channel via Kraus normalization."""
    if r <= 0:
        raise ValueError("r must be positive")
    As = []
    for _ in range(r):
        A = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        As.append(A)
    S = np.zeros((d, d), dtype=complex)
    for A in As:
        S = S + dagger(A) @ A
    S_inv_sqrt, clip = psd_matrix_invsqrt(S, eps=eps)
    Ks = [A @ S_inv_sqrt for A in As]
    err = kraus_completeness_error(Ks)
    return Ks, {"clipped_count": int(clip), "completeness_error": float(err)}


def kraus_dephasing(d: int, p: float) -> List[np.ndarray]:
    """Dephasing channel Kraus operators."""
    if p < 0 or p > 1:
        raise ValueError("p must be in [0,1]")
    K0 = math.sqrt(1 - p) * np.eye(d)
    Ks = [K0]
    for i in range(d):
        proj = np.zeros((d, d), dtype=complex)
        proj[i, i] = math.sqrt(p)
        Ks.append(proj)
    return Ks


def kraus_projective_measurement_standard(d: int) -> List[np.ndarray]:
    """Projective measurement in the standard basis."""
    Ks = []
    for i in range(d):
        proj = np.zeros((d, d), dtype=complex)
        proj[i, i] = 1.0
        Ks.append(proj)
    return Ks


def kraus_depolarizing(d: int, p: float) -> List[np.ndarray]:
    """Depolarizing channel Kraus operators."""
    if p < 0 or p > 1:
        raise ValueError("p must be in [0,1]")
    Ks = [math.sqrt(1 - p) * np.eye(d)]
    scale = math.sqrt(p / d)
    for i in range(d):
        for j in range(d):
            op = np.zeros((d, d), dtype=complex)
            op[i, j] = scale
            Ks.append(op)
    return Ks
