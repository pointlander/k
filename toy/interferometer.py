#!/usr/bin/env python3
"""Few-qubit Born-correction analog of k.

Prediction 2 of the paper: for two laboratory outcomes a, b,

    W(a)/W(b) = (|ψ_a|² / |ψ_b|²)  2^{−(K_G(a)−K_G(b))}.

This is the most direct empirical signature, and the easiest to overclaim.
The analog is the isolation theorem, not a claim that a fridge will beat Born.

  1. The integer skeleton is an n-qubit computational-basis record.
  2. Γ is identity: the sample *is* the laboratory record (no Einstein solver).
  3. Two branches with independently bounded K: a short history (constant)
     versus an incompressible dump.
  4. Isolated device: K̂_G = K(register).  ΔK ~ n, merge mass moves to the
     short branch by 2^{ΔK} on top of Born.
  5. Thermal bath of length L: K̂_G = max(K(env), K(register)).  Once L is
     at least the dump length, both records cost L and W tracks Born.
  6. Additive scoring K(env)+K(register) is also reported: a large fridge
     does *not* cancel ΔK under additivity.  Laboratory unobservability is
     thermal typicality or ΔK = O(1) clicks, not the mere existence of L bits.
  7. Two short clicks (0^n vs 1^n) have ΔK = 0 even when isolated; W = Born.

Units: bits.  Stdlib only.

Gzip is not K, n < ∞, and a qubit register is not a universe.  What survives
is the shape of eq. (born-corr): isolated short-vs-dump disagrees with Born;
thermal records and short clicks do not.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Kolmogorov upper bound
# ---------------------------------------------------------------------------


def k_bits(s: str) -> int:
    """Shortest description in a tiny language: dump, constants, one run,
    or small period. A computable upper bound on K, honest at small n."""
    n = len(s)
    if n == 0:
        return 0
    cands = [n + 1]
    if s == "0" * n or s == "1" * n:
        cands.append(2)
    flips = [i for i in range(1, n) if s[i] != s[i - 1]]
    if len(flips) <= 1:
        cands.append(3 + math.ceil(math.log2(n)) if n > 1 else 2)
    for p in range(1, n // 2 + 1):
        if s == (s[:p] * (n // p + 1))[:n]:
            cands.append(p + 1 + math.ceil(math.log2(n)))
    return min(cands)


def dump_bits(n: int) -> str:
    """Incompressible-looking n-bit string: raw dump in k_bits (K = n+1)."""
    if n <= 0:
        return ""
    if n == 1:
        return "1"
    if n == 2:
        return "10"
    return "1" + "0" * (n - 2) + "1"


def short_bits(n: int) -> str:
    return "0" * n


def click_bits(n: int, which: int) -> str:
    return ("0" if which == 0 else "1") * n


def typical_env(L: int) -> str:
    """Typical L-bit bath record (same shape as dump_bits)."""
    return dump_bits(L)


# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------


def k_env(env: str) -> int:
    return 0 if not env else k_bits(env)


def kg_isolated(reg: str) -> int:
    return k_bits(reg)


def kg_additive(reg: str, env: str) -> int:
    return k_env(env) + k_bits(reg)


def kg_thermal(reg: str, env: str) -> int:
    """Coarse thermal bound: K̂ = max(K(env), K(reg)).

    A typical bath of length L ≥ K(dump) makes both branches cost L.
    Isolated (env empty) reduces to K(reg).
    """
    return max(k_env(env), k_bits(reg))


SCORERS = {
    "isolated": lambda reg, env: kg_isolated(reg),
    "additive": kg_additive,
    "thermal": kg_thermal,
}


# ---------------------------------------------------------------------------
# Two-path interferometer and full merge
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Branch:
    name: str
    reg: str
    env: str
    born: float
    k_hat: int


@dataclass
class Pair:
    a: Branch
    b: Branch
    w_a: float
    w_b: float

    @property
    def delta_k(self) -> int:
        return self.b.k_hat - self.a.k_hat

    @property
    def born_ratio(self) -> float:
        return self.a.born / self.b.born if self.b.born > 0 else float("inf")

    @property
    def w_ratio(self) -> float:
        return self.w_a / self.w_b if self.w_b > 0 else float("inf")

    @property
    def occam(self) -> float:
        return 2.0 ** (-self.delta_k)


def _normalize_pair(a: Branch, b: Branch) -> Pair:
    M = max(a.k_hat, b.k_hat)
    wa = a.born * (2.0 ** (M - a.k_hat))
    wb = b.born * (2.0 ** (M - b.k_hat))
    z = wa + wb
    if z <= 0.0:
        raise RuntimeError("interferometer weights vanished")
    return Pair(a, b, wa / z, wb / z)


def make_branch(name: str, reg: str, env: str, born: float, scorer: str) -> Branch:
    return Branch(name, reg, env, born, SCORERS[scorer](reg, env))


def interferometer(
    n: int,
    p: float,
    scorer: str,
    L: int,
    kind: str,
) -> Pair:
    """Two-path device. `kind` is dump, clicks, or d=<int> extra dump bits."""
    env = typical_env(L)
    if kind == "dump":
        ra, rb = short_bits(n), dump_bits(n)
        na, nb = "short", "dump"
    elif kind == "clicks":
        ra, rb = click_bits(n, 0), click_bits(n, 1)
        na, nb = "click0", "click1"
    elif kind.startswith("d="):
        d = int(kind.split("=", 1)[1])
        d = max(0, min(d, n))
        ra = short_bits(n)
        rb = dump_bits(d) + "0" * (n - d) if d > 0 else short_bits(n)
        na, nb = "short", f"dump{d}"
    else:
        raise ValueError(kind)
    a = make_branch(na, ra, env, p, scorer)
    b = make_branch(nb, rb, env, 1.0 - p, scorer)
    return _normalize_pair(a, b)


def logsumexp(vals: list[float]) -> float:
    finite = [v for v in vals if math.isfinite(v)]
    if not finite:
        return float("-inf")
    m = max(finite)
    return m + math.log(sum(math.exp(v - m) for v in finite))


@dataclass
class Universe:
    s: str
    born: float
    k_hat: int
    w: float = 0.0


def full_cycle(n: int, scorer: str, L: int) -> list[Universe]:
    """Merge over the whole computational basis, uniform Born."""
    env = typical_env(L)
    N = 1 << n
    born_each = 1.0 / N
    us: list[Universe] = []
    log_ws: list[float] = []
    for i in range(N):
        s = format(i, f"0{n}b")
        k = SCORERS[scorer](s, env)
        us.append(Universe(s, born_each, k))
        log_ws.append(math.log(born_each) - k * math.log(2.0))
    lZ = logsumexp(log_ws)
    for u, lw in zip(us, log_ws):
        u.w = math.exp(lw - lZ)
    return us


def entropy(ws: list[float]) -> float:
    return -sum(w * math.log2(w) for w in ws if w > 0.0)


# ---------------------------------------------------------------------------
# Self-check
# ---------------------------------------------------------------------------


def self_check() -> int:
    n = 6
    p = 0.5
    dump = dump_bits(n)
    short = short_bits(n)
    if k_bits(short) != 2:
        print(f"FAIL: short K={k_bits(short)} want 2")
        return 1
    if k_bits(dump) != n + 1:
        print(f"FAIL: dump K={k_bits(dump)} want {n + 1}")
        return 1
    if k_bits(click_bits(n, 1)) != 2:
        print(f"FAIL: click1 K={k_bits(click_bits(n, 1))} want 2")
        return 1

    iso = interferometer(n, p, "isolated", 0, "dump")
    want_occam = 2.0 ** (k_bits(short) - k_bits(dump))  # 2^{-ΔK} in W_dump/W_short
    if iso.delta_k != k_bits(dump) - k_bits(short):
        print(f"FAIL: isolated ΔK={iso.delta_k}")
        return 1
    if abs(iso.w_ratio / iso.born_ratio - 2.0 ** iso.delta_k) > 1e-9:
        print(f"FAIL: isolated W/Born ratio {iso.w_ratio / iso.born_ratio} want {2.0 ** iso.delta_k}")
        return 1
    if iso.w_a <= 0.9:
        print(f"FAIL: isolated short mass {iso.w_a:.4f}")
        return 1
    _ = want_occam

    clicks = interferometer(n, p, "isolated", 0, "clicks")
    if clicks.delta_k != 0:
        print(f"FAIL: clicks ΔK={clicks.delta_k}")
        return 1
    if abs(clicks.w_a - p) > 1e-12 or abs(clicks.w_b - (1.0 - p)) > 1e-12:
        print(f"FAIL: clicks should track Born: W={clicks.w_a:.4f} Born={p}")
        return 1

    L = n
    th = interferometer(n, p, "thermal", L, "dump")
    if th.delta_k != 0:
        print(f"FAIL: thermal ΔK={th.delta_k} at L={L} (want 0)")
        return 1
    if abs(th.w_a - p) > 1e-12:
        print(f"FAIL: thermal should track Born: W={th.w_a:.4f} Born={p}")
        return 1

    add = interferometer(n, p, "additive", L, "dump")
    if add.delta_k != iso.delta_k:
        print(f"FAIL: additive ΔK={add.delta_k} should equal isolated {iso.delta_k}")
        return 1
    if abs(add.w_a - iso.w_a) > 1e-12:
        print(f"FAIL: additive should not swamp: W={add.w_a:.4f} isolated={iso.w_a:.4f}")
        return 1

    # Crossover: extra dump bits d=0 tracks Born; d=n agrees with isolated dump.
    d0 = interferometer(n, p, "isolated", 0, "d=0")
    if abs(d0.w_a - p) > 1e-12:
        print(f"FAIL: d=0 should track Born {d0.w_a}")
        return 1
    dn = interferometer(n, p, "isolated", 0, f"d={n}")
    if abs(dn.w_a - iso.w_a) > 1e-12:
        print(f"FAIL: d=n should match dump {dn.w_a} vs {iso.w_a}")
        return 1

    us = full_cycle(n, "isolated", 0)
    w_short = sum(u.w for u in us if k_bits(u.s) == 2)
    b_short = sum(u.born for u in us if k_bits(u.s) == 2)
    if w_short <= b_short:
        print(f"FAIL: full merge short mass {w_short:.4f} Born {b_short:.4f}")
        return 1
    star = max(us, key=lambda u: u.w)
    if star.s not in (short, click_bits(n, 1)):
        print(f"FAIL: typical isolated sample {star.s}")
        return 1

    print("self-check ok")
    print(f"  isolated short vs dump   ΔK={iso.delta_k}  W_short={iso.w_a:.4f}  Born={p:.2f}")
    print(f"  isolated clicks          ΔK=0   W={clicks.w_a:.4f}  (tracks Born)")
    print(f"  thermal L={L}            ΔK={th.delta_k}   W={th.w_a:.4f}  (tracks Born)")
    print(f"  additive L={L}           ΔK={add.delta_k}  W={add.w_a:.4f}  (no swamp)")
    print(f"  full merge short mass    W={w_short:.4f}  Born={b_short:.4f}")
    return 0


def print_crossover(args: argparse.Namespace) -> int:
    n, p = args.bits, args.p
    print("Born-correction crossover")
    print(f"  n={n}  p={args.p:g}  equal-Born two-path interferometer")
    print()
    print("  Isolated: extra incompressible bits d in the dump branch.")
    print("  d=0 is two short clicks (W tracks Born); d=n is short vs dump.")
    print(
        f"  {'d':>3}{'K_a':>6}{'K_b':>6}{'ΔK':>5}{'W_a':>10}{'W_b':>10}"
        f"{'W_a/Born':>10}{'2^{ΔK}':>10}"
    )
    for d in range(n + 1):
        pair = interferometer(n, p, "isolated", 0, f"d={d}")
        print(
            f"  {d:3d}{pair.a.k_hat:6d}{pair.b.k_hat:6d}{pair.delta_k:5d}"
            f"{pair.w_a:10.4f}{pair.w_b:10.4f}"
            f"{pair.w_a / p:10.4f}{2.0 ** pair.delta_k:10.4g}"
        )
    print()
    print("  Thermal bath: K̂ = max(K(env), K(reg)), dump vs short, L = 0..2n.")
    print("  Additive K(env)+K(reg) is the control that a fridge does not swamp.")
    print(
        f"  {'L':>3}{'th ΔK':>8}{'th W_a':>10}{'add ΔK':>8}{'add W_a':>10}{'tracks?':>10}"
    )
    for L in range(0, 2 * n + 1):
        th = interferometer(n, p, "thermal", L, "dump")
        add = interferometer(n, p, "additive", L, "dump")
        tracks = "Born" if th.delta_k == 0 else "biased"
        print(
            f"  {L:3d}{th.delta_k:8d}{th.w_a:10.4f}{add.delta_k:8d}{add.w_a:10.4f}{tracks:>10}"
        )
    print()
    print("  Isolated dump disagrees with Born; thermal L ≥ n tracks Born.")
    print("  Additive ΔK is independent of L.  Clicks (d=0) track Born with no bath.")
    return 0


def print_pair(args: argparse.Namespace) -> int:
    pair = interferometer(args.bits, args.p, args.scorer, args.env, args.kind)
    a, b = pair.a, pair.b
    print("few-qubit interferometer")
    print(f"  register       n={args.bits} qubits")
    print(f"  branches       {a.name} = {a.reg}   vs   {b.name} = {b.reg}")
    print(f"  environment    L={args.env}   scorer={args.scorer}")
    print(f"  Born           p({a.name})={a.born:g}  p({b.name})={b.born:g}  ratio={pair.born_ratio:.4g}")
    print(f"  K̂_G            {a.k_hat} vs {b.k_hat}   ΔK={pair.delta_k}")
    print(f"  W              {pair.w_a:.4f} vs {pair.w_b:.4f}   ratio={pair.w_ratio:.4g}")
    print(f"  W/Born         {pair.w_ratio / pair.born_ratio:.4g}   (want 2^{{ΔK}} = {2.0 ** pair.delta_k:.4g})")
    print()
    if pair.delta_k == 0:
        print("  ΔK = 0: W tracks Born.  Laboratory clicks, or a thermal bath with L ≥ K(dump).")
    else:
        print(f"  ΔK = {pair.delta_k}: short branch takes merge mass {pair.w_a:.4f} against Born {a.born:g}.")
        print("  This is eq. (born-corr) on an isolated register, not a tabletop claim.")
    return 0


def print_full(args: argparse.Namespace) -> int:
    us = full_cycle(args.bits, args.scorer, args.env)
    born_H = entropy([u.born for u in us])
    merge_H = entropy([u.w for u in us])
    w_short = sum(u.w for u in us if k_bits(u.s) == 2)
    b_short = sum(u.born for u in us if k_bits(u.s) == 2)
    star = max(us, key=lambda u: u.w)
    print("few-qubit full merge")
    print(f"  skeleton       n={args.bits}  ({1 << args.bits} computational-basis samples)")
    print(f"  scorer         {args.scorer}  L={args.env}")
    print(f"  Born entropy   {born_H:.3f} bits")
    print(f"  merge entropy  {merge_H:.3f} bits")
    print(f"  short Born     {b_short:.4f}")
    print(f"  short merge    {w_short:.4f}")
    print(
        f"  typical        s={star.s}  W={star.w:.4f}  Born={star.born:.4f}  "
        f"K̂_G={star.k_hat}"
    )
    print()
    print(f"  {'rank':<5}{'s':<{args.bits + 2}}{'W':>10}{'Born':>10}{'K̂_G':>8}")
    ranked = sorted(us, key=lambda u: -u.w)
    for i, u in enumerate(ranked[: args.top], 1):
        print(f"  {i:<5}{u.s:<{args.bits + 2}}{u.w:10.4f}{u.born:10.4f}{u.k_hat:8d}")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--bits", type=int, default=6, help="register qubits n (2–10). default 6")
    p.add_argument("--p", type=float, default=0.5, help="Born weight of the short/click0 branch")
    p.add_argument("--env", type=int, default=0, help="thermal / additive environment bits L")
    p.add_argument(
        "--scorer",
        choices=("isolated", "thermal", "additive"),
        default="isolated",
        help="isolated: K(reg); thermal: max(K(env),K(reg)); additive: K(env)+K(reg)",
    )
    p.add_argument(
        "--kind",
        default="dump",
        help="dump | clicks | d=k  (two-path). dump = short vs incompressible",
    )
    p.add_argument("--crossover", action="store_true", help="sweep dump-bits d and bath L")
    p.add_argument("--full", action="store_true", help="merge the whole computational basis")
    p.add_argument("--top", type=int, default=8)
    p.add_argument("--self-check", action="store_true")
    args = p.parse_args(argv)

    if args.self_check:
        return self_check()
    if args.bits < 2 or args.bits > 10:
        p.error("--bits must be in [2, 10]")
    if not (0.0 < args.p < 1.0):
        p.error("--p must be in (0, 1)")
    if args.env < 0:
        p.error("--env must be ≥ 0")
    if args.crossover:
        return print_crossover(args)
    if args.full:
        return print_full(args)
    return print_pair(args)


if __name__ == "__main__":
    sys.exit(main())
