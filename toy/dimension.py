#!/usr/bin/env python3
"""3+1 dimensionality analog of k.

Dzhunushaliev: 3+1 Einstein is the shortest well-posed compressor of Cauchy
data.  This analog makes that a merge on a finite catalog of gravity plugins,
not a slogan.

  1. A plugin is (D, Lovelock terms, compactification moduli).
  2. Local graviton polarizations are D(D−3)/2 (clamped at 0).
  3. The p-th Lovelock density is identically zero for D < 2p, topological
     at D = 2p, and dynamical for D > 2p.  Einstein–Hilbert is p = 1;
     Gauss–Bonnet is p = 2 (topological in 4d, dynamical for D ≥ 5).
  4. I_dead = 1 if the plugin does not compress Cauchy data into a radiating
     geometry (zero local gravitons, or no dynamical term).
  5. K̂_G = K(plugin) + β I_dead.
     4d Einstein–Hilbert with no junk is the 2-bit vacuum.
     Other D pay |D−4|; extra Lovelock terms and moduli pay their bits.
  6. Merge with W ∝ |ψ|² 2^{−K̂_G}.  Choquet–Bruhat well-posedness for D ≥ 3
     is an input, like the GR-machine elsewhere.

Units: bits.  Stdlib only.

A catalog is not 3+1 gravity, and D(D−3)/2 is not a Cauchy-problem proof.
What survives is the compressor count: 2+1 is dead, 4+1 pays moduli,
curvature junk is longer, 3+1 Einstein is Kolmogorov-elite.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Lovelock / dof algebra
# ---------------------------------------------------------------------------


def dof(D: int) -> int:
    """Local graviton polarizations of GR in D spacetime dimensions."""
    n = D * (D - 3) // 2
    return max(n, 0)


def lovelock_status(p: int, D: int) -> str:
    """zero / topological / dynamical for the p-th Lovelock density in D."""
    if D < 2 * p:
        return "zero"
    if D == 2 * p:
        return "topological"
    return "dynamical"


# ---------------------------------------------------------------------------
# Plugins
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Plugin:
    """Gravity plugin: spacetime dimension, Einstein–Hilbert, Gauss–Bonnet, moduli bits."""

    D: int
    has_eh: bool
    has_gb: bool
    moduli: int

    @property
    def name(self) -> str:
        bits = [f"D={self.D}"]
        if self.has_eh:
            bits.append("EH")
        if self.has_gb:
            bits.append("GB")
        if self.moduli:
            bits.append(f"m={self.moduli}")
        if not self.has_eh and not self.has_gb:
            bits.append("empty")
        return " ".join(bits)

    def n_dyn(self) -> int:
        n = 0
        if self.has_eh and lovelock_status(1, self.D) == "dynamical":
            n += 1
        if self.has_gb and lovelock_status(2, self.D) == "dynamical":
            n += 1
        return n

    def is_compressor(self) -> bool:
        return dof(self.D) > 0 and self.n_dyn() > 0

    def i_dead(self) -> int:
        return 0 if self.is_compressor() else 1

    def k_data(self) -> int:
        """Shortest description in a tiny language over plugins.

        4d Einstein–Hilbert with no Gauss–Bonnet and no moduli is the vacuum
        (2 bits).  Other dimensions pay |D−4|; extra terms and moduli pay
        their bits; dropping Einstein costs 2.
        """
        if self.D == 4 and self.has_eh and not self.has_gb and self.moduli == 0:
            return 2
        cost = 2 + abs(self.D - 4) + self.moduli
        if self.has_gb:
            cost += 1
        if not self.has_eh:
            cost += 2
        return cost

    def kg_hat(self, beta: float) -> float:
        return float(self.k_data()) + beta * self.i_dead()


def catalog(Ds: tuple[int, ...] = (2, 3, 4, 5, 6), moduli: tuple[int, ...] = (0, 1, 2, 4)) -> list[Plugin]:
    out: list[Plugin] = []
    for D in Ds:
        for has_eh in (True, False):
            for has_gb in (True, False):
                for m in moduli:
                    out.append(Plugin(D, has_eh, has_gb, m))
    return out


# ---------------------------------------------------------------------------
# Merge
# ---------------------------------------------------------------------------


def logsumexp(vals: list[float]) -> float:
    finite = [v for v in vals if math.isfinite(v)]
    if not finite:
        return float("-inf")
    m = max(finite)
    return m + math.log(sum(math.exp(v - m) for v in finite))


@dataclass
class Universe:
    plugin: Plugin
    born: float
    k_hat: float
    w: float = 0.0


def run_cycle(plugins: list[Plugin], beta: float, state: str) -> list[Universe]:
    universes: list[Universe] = []
    log_borns: list[float] = []
    log_ws: list[float] = []
    for p in plugins:
        k = p.kg_hat(beta)
        if state == "uniform":
            lb = 0.0
        elif state == "vacuum":
            # Kolmogorov vacuum: the 4d Einstein plugin is the short sample.
            lb = -float(p.k_data()) * math.log(2.0)
        else:
            raise ValueError(state)
        log_borns.append(lb)
        log_ws.append(lb - k * math.log(2.0))
        universes.append(Universe(p, lb, k))
    if not universes:
        raise RuntimeError("empty plugin catalog")
    lZ = logsumexp(log_ws)
    lB = logsumexp(log_borns)
    for u, lw, lb in zip(universes, log_ws, log_borns):
        u.w = math.exp(lw - lZ)
        u.born = math.exp(lb - lB)
    return universes


def entropy(ws: list[float]) -> float:
    return -sum(w * math.log2(w) for w in ws if w > 0.0)


def mass_where(us: list[Universe], pred) -> float:
    return sum(u.w for u in us if pred(u.plugin))


# ---------------------------------------------------------------------------
# Self-check
# ---------------------------------------------------------------------------


def self_check() -> int:
    if dof(2) != 0 or dof(3) != 0 or dof(4) != 2 or dof(5) != 5 or dof(6) != 9:
        print(f"FAIL: dof { {d: dof(d) for d in range(2, 7)} }")
        return 1
    if lovelock_status(1, 2) != "topological" or lovelock_status(1, 4) != "dynamical":
        print("FAIL: Einstein Lovelock status")
        return 1
    if lovelock_status(2, 3) != "zero" or lovelock_status(2, 4) != "topological" or lovelock_status(2, 5) != "dynamical":
        print("FAIL: Gauss–Bonnet Lovelock status")
        return 1

    eh4 = Plugin(4, True, False, 0)
    eh3 = Plugin(3, True, False, 0)
    eh5 = Plugin(5, True, False, 0)
    eh5m = Plugin(5, True, False, 1)
    eh4gb = Plugin(4, True, True, 0)
    eh5gb = Plugin(5, True, True, 0)
    empty4 = Plugin(4, False, False, 0)

    if eh4.k_data() != 2 or eh4.i_dead() != 0:
        print(f"FAIL: 4d EH vacuum K={eh4.k_data()} I_dead={eh4.i_dead()}")
        return 1
    if eh3.i_dead() != 1 or eh3.n_dyn() != 1:
        # EH is dynamical in D=3 but dof=0, so dead as a compressor.
        print(f"FAIL: 3d EH should be dead (dof=0), n_dyn={eh3.n_dyn()} I_dead={eh3.i_dead()}")
        return 1
    if dof(3) != 0:
        print("FAIL: 2+1 has local gravitons")
        return 1
    if eh4gb.k_data() <= eh4.k_data():
        print("FAIL: topological GB should cost bits")
        return 1
    if eh4gb.i_dead() != 0:
        print("FAIL: 4d EH+GB is still a compressor (EH dynamical)")
        return 1
    if eh5gb.n_dyn() != 2:
        print(f"FAIL: 5d EH+GB should have two dynamical terms, got {eh5gb.n_dyn()}")
        return 1
    if eh5m.k_data() <= eh5.k_data():
        print("FAIL: a modulus should cost bits")
        return 1
    if empty4.i_dead() != 1:
        print("FAIL: empty 4d Lagrangian should be dead")
        return 1

    beta = 8.0
    us = run_cycle(catalog(), beta, "uniform")
    w4 = mass_where(us, lambda p: p.D == 4 and p.has_eh and not p.has_gb and p.moduli == 0)
    wD4 = mass_where(us, lambda p: p.D == 4)
    wD3 = mass_where(us, lambda p: p.D == 3)
    wD5 = mass_where(us, lambda p: p.D == 5)
    w_comp = mass_where(us, lambda p: p.is_compressor())
    b_comp = sum(u.born for u in us if u.plugin.is_compressor())
    star = max(us, key=lambda u: u.w)
    second = sorted(us, key=lambda u: -u.w)[1]
    if star.plugin != eh4:
        print(f"FAIL: typical plugin {star.plugin.name} want D=4 EH")
        return 1
    if w4 <= second.w:
        print(f"FAIL: 4d EH {w4:.4f} should beat second {second.plugin.name} {second.w:.4f}")
        return 1
    if not (wD4 > wD5 > wD3):
        print(f"FAIL: expected W(D=4) > W(D=5) > W(D=3): {wD4:.4f} {wD5:.4f} {wD3:.4f}")
        return 1
    if w_comp <= b_comp:
        print(f"FAIL: compressor dominance absent W={w_comp:.4f} Born={b_comp:.4f}")
        return 1

    print("self-check ok")
    print("  dof(2,3,4,5,6)              0, 0, 2, 5, 9")
    print("  Gauss–Bonnet                zero D<4, topological D=4, dynamical D≥5")
    print(f"  4d EH  K̂_G                  {eh4.kg_hat(beta):.0f}   (vacuum)")
    print(f"  3d EH  K̂_G                  {eh3.kg_hat(beta):.0f}   (dead, dof=0)")
    print(f"  5d EH+modulus K̂_G           {eh5m.kg_hat(beta):.0f}")
    print(f"  typical plugin              {star.plugin.name}   W={star.w:.4f}")
    print(f"  W(4d EH)                    {w4:.4f}   (unique maximizer)")
    print(f"  W(D=4)                      {wD4:.4f}    W(D=5)={wD5:.4f}    W(D=3)={wD3:.4f}")
    print(f"  compressor merge mass       {w_comp:.4f}   Born={b_comp:.4f}")
    return 0


def print_compare(args: argparse.Namespace) -> int:
    us = run_cycle(catalog(), args.beta, args.state)
    print("3+1 dimensionality catalog")
    print(f"  β={args.beta:g}  |Ω⟩={args.state}  dof = D(D−3)/2")
    print("  4d EH is the 2-bit vacuum; 2+1 is dead; D>4 pays |D−4| and moduli.")
    print()
    print(
        f"  {'plugin':<22}{'D':>3}{'dof':>5}{'dyn':>5}{'dead':>6}"
        f"{'K':>5}{'K̂_G':>7}{'W':>10}{'Born':>10}"
    )
    ranked = sorted(us, key=lambda u: -u.w)
    for u in ranked[: args.top]:
        p = u.plugin
        print(
            f"  {p.name:<22}{p.D:3d}{dof(p.D):5d}{p.n_dyn():5d}{p.i_dead():6d}"
            f"{p.k_data():5d}{u.k_hat:7.1f}{u.w:10.4f}{u.born:10.4f}"
        )
    w4 = mass_where(us, lambda p: p.D == 4 and p.has_eh and not p.has_gb and p.moduli == 0)
    print()
    print(f"  W(4d Einstein–Hilbert) = {w4:.4f}   (Kolmogorov-elite Cauchy problem)")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--beta", type=float, default=8.0, help="I_dead coefficient in K̂_G")
    p.add_argument("--state", choices=("uniform", "vacuum"), default="uniform")
    p.add_argument("--compare", action="store_true", help="full catalog ranked by W")
    p.add_argument("--top", type=int, default=12)
    p.add_argument("--self-check", action="store_true")
    args = p.parse_args(argv)

    if args.self_check:
        return self_check()
    if args.compare:
        return print_compare(args)

    us = run_cycle(catalog(), args.beta, args.state)
    w4 = mass_where(us, lambda p: p.D == 4 and p.has_eh and not p.has_gb and p.moduli == 0)
    w3 = mass_where(us, lambda p: p.D == 3)
    w5 = mass_where(us, lambda p: p.D == 5)
    w2 = mass_where(us, lambda p: p.D == 2)
    w_comp = mass_where(us, lambda p: p.is_compressor())
    b_comp = sum(u.born for u in us if u.plugin.is_compressor())
    w_gb_junk = mass_where(us, lambda p: p.D == 4 and p.has_eh and p.has_gb)
    star = max(us, key=lambda u: u.w)
    born_H = entropy([u.born for u in us])
    merge_H = entropy([u.w for u in us])

    print("3+1 dimensionality k-cycle")
    print(f"  skeleton       D=2..6 × EH × GB × moduli {{0,1,2,4}}   ({len(us)} plugins)")
    print(f"  state          |Ω⟩ = {args.state}")
    print(f"  weight         W ∝ |ψ|² 2^{{-K̂_G}},  K̂_G = K(plugin) + {args.beta:g} I_dead")
    print(f"  Born entropy   {born_H:.3f} bits")
    print(f"  merge entropy  {merge_H:.3f} bits")
    print()
    print("  Einsteinian / dimensional dominance")
    print(f"    compressor Born mass     {b_comp:.4f}")
    print(f"    compressor merge mass    {w_comp:.4f}")
    print(f"    4d EH                    {w4:.4f}")
    print(f"    4d EH+GB (topological)   {w_gb_junk:.4f}")
    print(f"    D=5                      {w5:.4f}")
    print(f"    D=3 (2+1, dof=0)         {w3:.4f}")
    print(f"    D=2                      {w2:.4f}")
    print()
    q = star.plugin
    print(
        f"  typical plugin   {q.name}  compressor={q.is_compressor()}  "
        f"dof={dof(q.D)}  dyn={q.n_dyn()}"
    )
    print(
        f"                   W={star.w:.4f}  Born={star.born:.4f}  "
        f"K̂_G={star.k_hat:.1f}  I_dead={q.i_dead()}"
    )
    print()
    print(
        f"  {'rank':<5}{'plugin':<22}{'D':>3}{'dof':>5}{'dyn':>5}"
        f"{'W':>10}{'Born':>10}{'K̂_G':>7}{'dead':>6}"
    )
    ranked = sorted(us, key=lambda u: -u.w)
    for i, u in enumerate(ranked[: args.top], 1):
        q = u.plugin
        print(
            f"  {i:<5}{q.name:<22}{q.D:3d}{dof(q.D):5d}{q.n_dyn():5d}"
            f"{u.w:10.4f}{u.born:10.4f}{u.k_hat:7.1f}{q.i_dead():6d}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
