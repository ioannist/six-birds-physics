#!/usr/bin/env python3
import math
from typing import List, Tuple

import numpy as np


def assert_prob(x: np.ndarray, tol: float = 1e-9) -> None:
    if np.any(x < -tol):
        raise ValueError("Negative probability detected")
    s = float(np.sum(x))
    if not math.isfinite(s) or abs(s - 1.0) > tol:
        raise ValueError(f"Probability does not sum to 1 (sum={s})")


def assert_row_stochastic(P: np.ndarray, tol: float = 1e-9) -> None:
    if np.any(P < -tol):
        raise ValueError("Negative transition probability detected")
    row_sums = np.sum(P, axis=1)
    if not np.all(np.isfinite(row_sums)):
        raise ValueError("Non-finite row sums")
    if np.max(np.abs(row_sums - 1.0)) > tol:
        raise ValueError("Row sums are not 1 within tolerance")


def lens_partition(N: int, K: int, mode: str = "contiguous", seed: int | None = None) -> Tuple[np.ndarray, List[np.ndarray]]:
    if K <= 0 or N <= 0:
        raise ValueError("N and K must be positive")
    if N % K != 0:
        raise ValueError("N must be divisible by K")
    r = N // K

    if mode == "contiguous":
        f = np.repeat(np.arange(K), r)
    elif mode == "random_equal":
        rng = np.random.default_rng(seed)
        perm = rng.permutation(N)
        f = np.empty(N, dtype=int)
        for i, z in enumerate(perm):
            f[z] = i // r
    else:
        raise ValueError("mode must be 'contiguous' or 'random_equal'")

    fibers: List[np.ndarray] = []
    for x in range(K):
        idx = np.where(f == x)[0]
        if idx.size == 0:
            raise ValueError("Empty fiber detected")
        fibers.append(idx)
    if sum(len(fib) for fib in fibers) != N:
        raise ValueError("Fiber coverage mismatch")

    return f, fibers


def Q_f(mu: np.ndarray, fibers: List[np.ndarray]) -> np.ndarray:
    assert_prob(mu)
    K = len(fibers)
    nu = np.zeros(K)
    for x, idx in enumerate(fibers):
        nu[x] = float(np.sum(mu[idx]))
    assert_prob(nu)
    return nu


def U_uniform(nu: np.ndarray, fibers: List[np.ndarray]) -> np.ndarray:
    assert_prob(nu)
    N = sum(len(fib) for fib in fibers)
    mu = np.zeros(N)
    for x, idx in enumerate(fibers):
        mu[idx] = nu[x] / len(idx)
    assert_prob(mu)
    return mu


def E(mu: np.ndarray, fibers: List[np.ndarray]) -> np.ndarray:
    return U_uniform(Q_f(mu, fibers), fibers)


def T_tau(mu: np.ndarray, P: np.ndarray, tau: int) -> np.ndarray:
    if tau < 0:
        raise ValueError("tau must be nonnegative")
    assert_row_stochastic(P)
    if tau == 0:
        return mu
    Ptau = np.linalg.matrix_power(P, tau)
    return mu @ Ptau


def E_tau(mu: np.ndarray, P: np.ndarray, tau: int, fibers: List[np.ndarray]) -> np.ndarray:
    return E(T_tau(mu, P, tau), fibers)


def tv(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def kl(p: np.ndarray, q: np.ndarray, eps: float = 1e-12) -> float:
    p = np.array(p, dtype=float)
    q = np.array(q, dtype=float)
    p = (p + eps) / (float(np.sum(p)) + eps * p.size)
    q = (q + eps) / (float(np.sum(q)) + eps * q.size)
    val = float(np.sum(p * np.log(p / q)))
    if not math.isfinite(val):
        return float("inf")
    return val


def random_prob(n: int, rng: np.random.Generator) -> np.ndarray:
    return rng.dirichlet(np.ones(n))


def random_stochastic(n: int, rng: np.random.Generator, sparsity: float = 0.0) -> np.ndarray:
    mat = rng.random((n, n))
    if sparsity > 0:
        mask = rng.random((n, n)) < sparsity
        mat = mat * (~mask)
        for i in range(n):
            if np.all(mat[i] == 0):
                j = int(rng.integers(0, n))
                mat[i, j] = 1.0
    mat = mat / np.sum(mat, axis=1, keepdims=True)
    assert_row_stochastic(mat)
    return mat
