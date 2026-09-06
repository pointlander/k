#!/usr/bin/env python3
"""Discrete analog of k: sample, weight, merge.

This is not gravity. It is the shape of the k-cycle on a finite integer
skeleton:

  1. A quantum state |Ω⟩ lives in a separable (here finite) Hilbert space
     whose computational basis is indexed by bitstrings — the analog of ℵ₀.
  2. Sampling draws a string s from Born weights |⟨s|Ω⟩|².
  3. Each string is a "universe": a classical spin configuration on a cycle.
     The analog of GR inflation is the identification of s with that
     configuration, plus a smoothness penalty that stands in for off-shell
     Einstein cost.
  4. The analog of gravitational Kolmogorov complexity is
         K̂_G(s) = compressed_length(s) + β · E_smooth(s)
     where E_smooth is a discrete curvature (nearest-neighbour mismatch).
  5. Universes are merged with weights W(s) ∝ |ψ_s|² · 2^{-K̂_G(s)}.

The continuum (𝔠) is missing on purpose: n is finite, gzip is not K, and a
cycle graph is not Einstein. What survives is Einsteinian-style dominance
of smooth compressible samples, a well-defined countable (finite) merge,
and an output that is again a vector in the skeleton space.
"""

from __future__ import annotations

import argparse
import gzip
import math
import sys
from dataclasses import dataclass

# Prefer numpy if present; otherwise run on the standard library.
try:
    import numpy as np
except ImportError:  # pragma: no cover
    np = None


def bits_to_bytes(s: str) -> bytes:
    pad = (8 - len(s) % 8) % 8
    padded = s + "0" * pad
    return bytes(int(padded[i : i + 8], 2) for i in range(0, len(padded), 8))


def gzip_bits(s: str) -> int:
    raw = gzip.compress(bits_to_bytes(s), compresslevel=9)
    return max(8 * len(raw) - 18 * 8, 1)


def program_length(s: str) -> int:
    """Shortest description in a tiny language: raw dump, constants, one block,
    or small period. A computable upper bound on K, honest at small n where
    gzip's container dominates."""
    n = len(s)
    cands = [n + 1]
    if s == "0" * n or s == "1" * n:
        cands.append(2)
    flips = [i for i in range(n) if s[i] != s[(i - 1) % n]]
    if len(flips) == 2:
        cands.append(3 + 2 * math.ceil(math.log2(n)))
    for p in range(1, n // 2 + 1):
        if s == (s[:p] * (n // p + 1))[:n]:
            cands.append(p + 1 + math.ceil(math.log2(n)))
    return min(cands)


def compressed_length(s: str) -> int:
    """Computable upper bound on Kolmogorov complexity, in bits."""
    return min(program_length(s), gzip_bits(s))


def smooth_energy(s: str) -> int:
    """Discrete curvature: number of bit flips around the cycle."""
    n = len(s)
    return sum(int(s[i]) != int(s[(i + 1) % n]) for i in range(n))


def kg_hat(s: str, beta: float) -> float:
    return compressed_length(s) + beta * smooth_energy(s)


def all_strings(n: int) -> list[str]:
    return [format(i, f"0{n}b") for i in range(2**n)]


def kolmogorov_vacuum(n: int, kind: str):
    """A short-program state on n bits.

    'smooth'  — superposition of the two constant strings (the shortest
                Einstein analog: empty curvature).
    'ghz'     — GHZ cat, still a short program, but the two branches are
                each maximally smooth.
    'w'       — W state: single-excitation superposition, short and locally
                smooth.
    'random'  — Haar-like amplitudes (seeded), a long program, for contrast.
    """
    dim = 2**n
    strings = all_strings(n)
    if np is None:
        psi = [0.0] * dim
        if kind == "smooth":
            psi[0] = 1 / math.sqrt(2)
            psi[-1] = 1 / math.sqrt(2)
        elif kind == "ghz":
            psi[0] = 1 / math.sqrt(2)
            psi[-1] = 1 / math.sqrt(2)
        elif kind == "w":
            amp = 1 / math.sqrt(n)
            for i in range(n):
                psi[1 << i] = amp
        elif kind == "random":
            import random

            rng = random.Random(0)
            re = [rng.gauss(0, 1) for _ in range(dim)]
            im = [rng.gauss(0, 1) for _ in range(dim)]
            norm = math.sqrt(sum(a * a + b * b for a, b in zip(re, im)))
            psi = [complex(a, b) / norm for a, b in zip(re, im)]
        else:
            raise ValueError(kind)
        return strings, psi

    psi = np.zeros(dim, dtype=np.complex128)
    if kind in ("smooth", "ghz"):
        psi[0] = 1 / math.sqrt(2)
        psi[-1] = 1 / math.sqrt(2)
    elif kind == "w":
        amp = 1 / math.sqrt(n)
        for i in range(n):
            psi[1 << i] = amp
    elif kind == "random":
        rng = np.random.default_rng(0)
        psi = rng.normal(size=dim) + 1j * rng.normal(size=dim)
        psi /= np.linalg.norm(psi)
    else:
        raise ValueError(kind)
    return strings, psi


@dataclass
class Universe:
    s: str
    born: float
    k_hat: float
    e_smooth: int
    w: float


def merge(strings, psi, beta: float) -> tuple[list[Universe], list[float], float]:
    born = []
    for i, _s in enumerate(strings):
        amp = psi[i]
        born.append(float(abs(amp) ** 2))

    universes: list[Universe] = []
    raw = []
    for s, b in zip(strings, born):
        e = smooth_energy(s)
        k = kg_hat(s, beta)
        weight = b * (2.0 ** (-k))
        raw.append(weight)
        universes.append(Universe(s=s, born=b, k_hat=k, e_smooth=e, w=0.0))

    z = sum(raw)
    if z == 0:
        raise RuntimeError("all weights vanished")
    for u, r in zip(universes, raw):
        u.w = r / z

    n = len(strings[0])
    barycentre = []
    for i in range(n):
        barycentre.append(sum(u.w * int(u.s[i]) for u in universes))
    entropy = -sum(u.w * math.log2(u.w) for u in universes if u.w > 0)
    return universes, barycentre, entropy


def typical(universes: list[Universe]) -> Universe:
    return max(universes, key=lambda u: u.w)


def render_soft(barycentre: list[float]) -> str:
    """Hard projection of the decoherent mean. '.' marks a bit the merge
    does not decide (bimodal weight, typical of a cat state)."""
    out = []
    for x in barycentre:
        if x > 0.5 + 1e-9:
            out.append("1")
        elif x < 0.5 - 1e-9:
            out.append("0")
        else:
            out.append(".")
    return "".join(out)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("-n", type=int, default=8, help="skeleton length (integer bits), default 8")
    p.add_argument("--beta", type=float, default=2.0, help="GR-penalty strength in K̂_G")
    p.add_argument(
        "--state",
        choices=("smooth", "ghz", "w", "random"),
        default="smooth",
        help="Kolmogorov-vacuum analog",
    )
    p.add_argument("--top", type=int, default=8, help="how many heaviest universes to print")
    args = p.parse_args(argv)

    if args.n < 2 or args.n > 12:
        p.error("n must be in [2, 12]; the analog enumerates 2^n universes")

    strings, psi = kolmogorov_vacuum(args.n, args.state)
    universes, barycentre, entropy = merge(strings, psi, args.beta)
    star = typical(universes)

    born_entropy = 0.0
    for u in universes:
        if u.born > 0:
            born_entropy -= u.born * math.log2(u.born)

    print("k-cycle analog")
    print(f"  skeleton          n = {args.n}   (2^{args.n} = {2**args.n} sampled universes)")
    print(f"  state             |Ω⟩ = {args.state}")
    print(f"  weight            W(s) ∝ |ψ_s|² · 2^{{-K̂_G(s)}},  K̂_G = K_upper + {args.beta}·E_smooth")
    print(f"  Born entropy      {born_entropy:.3f} bits  (of {args.n} max)")
    print(f"  merge entropy     {entropy:.3f} bits")
    print(f"  typical universe  {star.s}   W = {star.w:.4f}   E_smooth = {star.e_smooth}   K̂_G = {star.k_hat:.1f}")
    print(f"  merged barycentre {render_soft(barycentre)}   soft = [{', '.join(f'{x:.2f}' for x in barycentre)}]")
    print()
    print(f"  {'rank':<6}{'universe':<{args.n + 2}}{'W':>10}{'Born':>10}{'K̂_G':>10}{'E_smooth':>10}")
    ranked = sorted(universes, key=lambda u: -u.w)
    for i, u in enumerate(ranked[: args.top], 1):
        print(f"  {i:<6}{u.s:<{args.n + 2}}{u.w:10.4f}{u.born:10.4f}{u.k_hat:10.1f}{u.e_smooth:10d}")

    # Dominance diagnostic: mass on the two constant (zero-curvature) strings.
    elite = sum(u.w for u in universes if u.e_smooth == 0)
    print()
    print(f"  weight on zero-curvature samples (Einstein analog): {elite:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
