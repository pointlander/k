#!/usr/bin/env python3
"""Finite language for field-theory plugins, with GUT Higgs/breaking in-word.

Open problems 4 and 7: the Standard Model is a minimization over a fixed
encoding of field theories.  Breaking is not a 2-bit discount.  It is a
Higgs word in the same grammar.

  plugin ::= gravity  group  nFerm  nGen  degV  higgs
  group  ::= U(1) | SU(n) | SO(n) | G × H
  higgs  ::= unary(k)  rep^k
  rep    ::= fund | afund | adj | spinor

SM Higgs is one fund (the doublet).  SU(5) pays adj+fund (24 and 5).
SO(10) pays adj+fund+spinor (45, 10, 16).  Adjoint is a short program
given G ("all generators"), not unary-24.

K̂_G = |encode(plugin)| + β I_dead + γ I_wrong.
I_wrong is an input (needs 4d Einstein plus SM quantum numbers).
The merge then either selects the SM or fails in public.

Stdlib only.  Import `dimension` from the same directory.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

# `python3 toy/plugin.py` puts this directory on path[0].
sys.path.insert(0, str(Path(__file__).resolve().parent))
import dimension as dim


# ---------------------------------------------------------------------------
# Prefix-free code
# ---------------------------------------------------------------------------


def unary(n: int) -> str:
    if n < 0:
        raise ValueError(n)
    return "1" * n + "0"


def encode_nat(n: int) -> str:
    return unary(n)


@dataclass(frozen=True)
class Group:
    """Simple groups and finite products. `n` is the SU(n)/SO(n) rank argument."""

    kind: str  # u1 | su | so | prod
    n: int = 0
    left: Group | None = None
    right: Group | None = None

    def encode(self) -> str:
        if self.kind == "u1":
            return "00"
        if self.kind == "su":
            return "01" + unary(self.n)
        if self.kind == "so":
            return "10" + unary(self.n)
        if self.kind == "prod":
            assert self.left is not None and self.right is not None
            return "11" + self.left.encode() + self.right.encode()
        raise ValueError(self.kind)

    def __str__(self) -> str:
        if self.kind == "u1":
            return "U(1)"
        if self.kind == "su":
            return f"SU({self.n})"
        if self.kind == "so":
            return f"SO({self.n})"
        return f"({self.left}×{self.right})"


U1 = Group("u1")
SU2 = Group("su", 2)
SU3 = Group("su", 3)
SU5 = Group("su", 5)
SO10 = Group("so", 10)
SM = Group("prod", left=SU3, right=Group("prod", left=SU2, right=U1))


def decode_unary(s: str, i: int = 0) -> tuple[int, int] | None:
    n = 0
    while i < len(s) and s[i] == "1":
        n += 1
        i += 1
    if i >= len(s) or s[i] != "0":
        return None
    return n, i + 1


def decode_group(s: str, i: int = 0) -> tuple[Group, int] | None:
    if i + 1 >= len(s):
        return None
    tag = s[i : i + 2]
    i += 2
    if tag == "00":
        return U1, i
    if tag == "01":
        got = decode_unary(s, i)
        if got is None:
            return None
        n, i = got
        return Group("su", n), i
    if tag == "10":
        got = decode_unary(s, i)
        if got is None:
            return None
        n, i = got
        return Group("so", n), i
    if tag == "11":
        left = decode_group(s, i)
        if left is None:
            return None
        g, i = left
        right = decode_group(s, i)
        if right is None:
            return None
        h, i = right
        return Group("prod", left=g, right=h), i
    return None


def log2len(n: int) -> int:
    """Self-delimiting binary length bound: 2 (⌊log₂ n⌋ + 1).  n = 0 uses 2."""
    if n <= 0:
        return 2
    L = n.bit_length()  # ⌊log₂ n⌋ + 1 for n ≥ 1
    return 2 * L


def raw_list_len(n: int, g: Group) -> int:
    """n concatenated copies, wrapped by a count: 01 ++ unary(n) ++ gⁿ."""
    return 2 + (n + 1) + n * len(g.encode())


def gen_list_len(n: int, g: Group) -> int:
    """Generated n copies: 10 ++ g ++ self-delimiting n."""
    return 2 + len(g.encode()) + log2len(n)


# ---------------------------------------------------------------------------
# Higgs / breaking sector
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Rep:
    """Irrep word.  fund/afund/adj/spinor are short names given G."""

    kind: str  # fund | afund | adj | spinor

    def encode(self) -> str:
        return {"fund": "00", "afund": "01", "adj": "10", "spinor": "11"}[self.kind]

    def __str__(self) -> str:
        return {"fund": "fund", "afund": "afund", "adj": "adj", "spinor": "spinor"}[self.kind]


FUND = Rep("fund")
AFUND = Rep("afund")
ADJ = Rep("adj")
SPINOR = Rep("spinor")

# SM: one weak doublet.  SU(5): 24 + 5.  SO(10): 45 + 10 + 16.
SM_HIGGS = (FUND,)
SU5_HIGGS = (ADJ, FUND)
SO10_HIGGS = (ADJ, FUND, SPINOR)


def encode_higgs(reps: tuple[Rep, ...]) -> str:
    return unary(len(reps)) + "".join(r.encode() for r in reps)


def decode_higgs(s: str, i: int = 0) -> tuple[tuple[Rep, ...], int] | None:
    got = decode_unary(s, i)
    if got is None:
        return None
    k, i = got
    reps: list[Rep] = []
    table = {"00": FUND, "01": AFUND, "10": ADJ, "11": SPINOR}
    for _ in range(k):
        if i + 1 >= len(s):
            return None
        tag = s[i : i + 2]
        if tag not in table:
            return None
        reps.append(table[tag])
        i += 2
    return tuple(reps), i


# ---------------------------------------------------------------------------
# Theories
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Theory:
    """A field-theory plugin: gravity word plus matter word, or a landscape."""

    name: str
    gravity: dim.Plugin
    group: Group
    n_ferm: int
    n_gen: int
    deg_v: int
    higgs: tuple[Rep, ...] = ()
    kind: str = "theory"  # theory | raw | gen
    copies: int = 1

    def group_len(self) -> int:
        if self.kind == "raw":
            return raw_list_len(self.copies, self.group)
        if self.kind == "gen":
            return gen_list_len(self.copies, self.group)
        return len(self.group.encode())

    def encode_len(self) -> int:
        """|encode(plugin)| in the tiny language, ignoring I_dead / I_wrong."""
        return (
            self.gravity.k_data()
            + self.group_len()
            + (self.n_ferm + 1)
            + (self.n_gen + 1)
            + (self.deg_v + 1)
            + len(encode_higgs(self.higgs))
        )

    def i_wrong(self, sample: str) -> int:
        """Incompatibility with a low-energy sample.  Input, not derived."""
        if sample == "none":
            return 0
        if sample == "sm":
            if self.gravity.D != 4 or not self.gravity.is_compressor():
                return 1
            if self.kind in ("raw", "gen") and self.group != SM:
                return 1
            if self.kind == "theory" and self.group not in (SM, SU5, SO10):
                return 1
            if self.n_gen < 1:
                return 1
            return 0
        raise ValueError(sample)

    def kg_hat(self, beta: float, gamma: float, sample: str) -> float:
        return (
            float(self.encode_len())
            + beta * self.gravity.i_dead()
            + gamma * self.i_wrong(sample)
        )


def named_theories() -> list[Theory]:
    eh4 = dim.Plugin(4, True, False, 0)
    eh3 = dim.Plugin(3, True, False, 0)
    eh5m = dim.Plugin(5, True, False, 1)
    return [
        Theory("4d EH", eh4, U1, 0, 0, 0),
        Theory("4d EH+U(1)", eh4, U1, 1, 1, 2, higgs=SM_HIGGS),
        Theory("4d EH+SM", eh4, SM, 5, 3, 4, higgs=SM_HIGGS),
        Theory("4d EH+SU(5)", eh4, SU5, 2, 3, 4, higgs=SU5_HIGGS),
        Theory("4d EH+SO(10)", eh4, SO10, 1, 3, 4, higgs=SO10_HIGGS),
        Theory("raw 16×U(1)", eh4, U1, 1, 1, 2, higgs=SM_HIGGS, kind="raw", copies=16),
        Theory("gen 16×U(1)", eh4, U1, 1, 1, 2, higgs=SM_HIGGS, kind="gen", copies=16),
        Theory("raw 16×SM", eh4, SM, 5, 3, 4, higgs=SM_HIGGS, kind="raw", copies=16),
        Theory("gen 16×SM", eh4, SM, 5, 3, 4, higgs=SM_HIGGS, kind="gen", copies=16),
        Theory("3d EH+SM", eh3, SM, 5, 3, 4, higgs=SM_HIGGS),
        Theory("5d EH+m+SM", eh5m, SM, 5, 3, 4, higgs=SM_HIGGS),
    ]


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
    theory: Theory
    born: float
    k_hat: float
    w: float = 0.0


def run_cycle(
    theories: list[Theory],
    beta: float,
    gamma: float,
    sample: str,
) -> list[Universe]:
    universes: list[Universe] = []
    log_ws: list[float] = []
    log_borns: list[float] = []
    for t in theories:
        if sample != "none" and t.i_wrong(sample) != 0:
            continue
        k = t.kg_hat(beta, gamma, sample)
        lb = 0.0
        log_borns.append(lb)
        log_ws.append(lb - k * math.log(2.0))
        universes.append(Universe(t, lb, k))
    if not universes:
        raise RuntimeError("no plugin compatible with the sample")
    lZ = logsumexp(log_ws)
    lB = logsumexp(log_borns)
    for u, lw, lb in zip(universes, log_ws, log_borns):
        u.w = math.exp(lw - lZ)
        u.born = math.exp(lb - lB)
    return universes


def is_prefix_free(words: list[str]) -> bool:
    for i, p in enumerate(words):
        for j, q in enumerate(words):
            if i != j and q.startswith(p):
                return False
    return True


# ---------------------------------------------------------------------------
# Self-check
# ---------------------------------------------------------------------------


def self_check() -> int:
    for g, n in ((U1, None), (SU2, 2), (SU3, 3), (SU5, 5), (SO10, 10), (SM, None)):
        w = g.encode()
        got = decode_group(w)
        if got is None or got[0] != g or got[1] != len(w):
            print(f"FAIL: roundtrip {g} -> {w} -> {got}")
            return 1
        if n is not None and len(w) != 2 + n + 1:
            print(f"FAIL: |{g}|={len(w)} want {2 + n + 1}")
            return 1
    if len(U1.encode()) != 2:
        print("FAIL: |U(1)|")
        return 1
    if not (len(SU5.encode()) < len(SM.encode())):
        print(f"FAIL: SU(5) should be shorter than SM: {len(SU5.encode())} vs {len(SM.encode())}")
        return 1

    groups = [U1, SU2, SU3, SU5, SO10, SM]
    words = [g.encode() for g in groups]
    if len(set(words)) != len(words):
        print("FAIL: encodings collide")
        return 1
    if not is_prefix_free(words):
        print("FAIL: group code is not prefix-free")
        return 1

    n = 16
    raw_u1 = raw_list_len(n, U1)
    gen_u1 = gen_list_len(n, U1)
    if raw_u1 < n:
        print(f"FAIL: raw list shorter than N: {raw_u1}")
        return 1
    if not (gen_u1 < raw_u1):
        print(f"FAIL: generator should beat raw: gen {gen_u1} raw {raw_u1}")
        return 1
    if not (len(SM.encode()) < raw_list_len(n, U1)):
        print("FAIL: SM word should beat 16 raw U(1)s")
        return 1

    for reps in (SM_HIGGS, SU5_HIGGS, SO10_HIGGS):
        w = encode_higgs(reps)
        got = decode_higgs(w)
        if got is None or got[0] != reps or got[1] != len(w):
            print(f"FAIL: Higgs roundtrip {reps} -> {w} -> {got}")
            return 1
    if len(encode_higgs(SM_HIGGS)) != 4 or len(encode_higgs(SU5_HIGGS)) != 7:
        print("FAIL: Higgs lengths")
        return 1
    if not (len(encode_higgs(SM_HIGGS)) < len(encode_higgs(SU5_HIGGS))):
        print("FAIL: SM Higgs should be shorter than 24+5")
        return 1

    eh4 = dim.Plugin(4, True, False, 0)
    sm = Theory("4d EH+SM", eh4, SM, 5, 3, 4, higgs=SM_HIGGS)
    su5 = Theory("4d EH+SU(5)", eh4, SU5, 2, 3, 4, higgs=SU5_HIGGS)
    so10 = Theory("4d EH+SO(10)", eh4, SO10, 1, 3, 4, higgs=SO10_HIGGS)
    if sm.i_wrong("sm") != 0 or su5.i_wrong("sm") != 0 or so10.i_wrong("sm") != 0:
        print("FAIL: SM, SU(5), SO(10) should fit the SM sample")
        return 1
    u1t = Theory("4d EH+U(1)", eh4, U1, 1, 1, 2, higgs=SM_HIGGS)
    if u1t.i_wrong("sm") != 1:
        print("FAIL: U(1) should not fit the SM sample")
        return 1

    beta, gamma = 8.0, 8.0
    us = run_cycle(named_theories(), beta, gamma, "sm")
    star = max(us, key=lambda u: u.w)
    w_raw = sum(u.w for u in us if u.theory.kind == "raw")
    w_sm = sum(u.w for u in us if u.theory.name == "4d EH+SM")
    w_su5 = sum(u.w for u in us if u.theory.name == "4d EH+SU(5)")
    w_so10 = sum(u.w for u in us if u.theory.name == "4d EH+SO(10)")
    if w_raw > w_sm:
        print(f"FAIL: raw landscape mass {w_raw:.4f} vs SM {w_sm:.4f}")
        return 1
    # Who minimizes is a result, not a wish.  Record it.
    winner = star.theory.name

    print("self-check ok")
    print(f"  |U(1)|={len(U1.encode())}  |SU(5)|={len(SU5.encode())}  |SM|={len(SM.encode())}  |SO(10)|={len(SO10.encode())}")
    print(f"  Higgs |SM|={len(encode_higgs(SM_HIGGS))}  |SU(5) 24+5|={len(encode_higgs(SU5_HIGGS))}  |SO(10) 45+10+16|={len(encode_higgs(SO10_HIGGS))}")
    print(f"  prefix-free on {len(groups)} named groups")
    print(f"  raw 16×U(1)={raw_u1}   gen 16×U(1)={gen_u1}   |SM group|={len(SM.encode())}")
    print(f"  encode SM={sm.encode_len()}   SU(5)+24+5={su5.encode_len()}   SO(10)+45+10+16={so10.encode_len()}")
    print(f"  typical |Ω⟩=SM-sample   {winner}   W={star.w:.4f}")
    print(f"  W(SU(5))={w_su5:.4f}  W(SO(10))={w_so10:.4f}  W(SM)={w_sm:.4f}  W(raw)={w_raw:.4f}")
    if winner != "4d EH+SM":
        print("  minimizer is not the SM: GUT Higgs-in-word is still cheaper than the product group.")
    return 0


def print_compare(args: argparse.Namespace) -> int:
    us = run_cycle(named_theories(), args.beta, args.gamma, args.sample)
    print("field-theory plugin language")
    print(f"  sample={args.sample}  β={args.beta:g}  γ={args.gamma:g}")
    print("  group ::= U(1) | SU(n) | SO(n) | G×H     higgs ::= unary(k) rep^k")
    print("  SM Higgs = fund;  SU(5) = adj+fund (24+5);  SO(10) = adj+fund+spinor")
    print()
    print(
        f"  {'theory':<18}{'group':<22}{'higgs':>12}{'|enc|':>6}"
        f"{'K̂_G':>7}{'W':>10}"
    )
    ranked = sorted(us, key=lambda u: -u.w)
    for u in ranked[: args.top]:
        t = u.theory
        hg = "+".join(str(r) for r in t.higgs) if t.higgs else "—"
        print(
            f"  {t.name:<18}{str(t.group):<22}{hg:>12}{t.encode_len():6d}"
            f"{u.k_hat:7.1f}{u.w:10.4f}"
        )
    star = ranked[0]
    print()
    print(f"  typical  {star.theory.name}   W={star.w:.4f}   K̂_G={star.k_hat:.1f}")
    if args.sample == "sm":
        if star.theory.name == "4d EH+SM":
            print("  Minimizer is the SM product once GUT Higgs is in the word.")
        else:
            print("  Minimizer is not the SM: adjoint+fund is still a shorter breaking sector")
            print("  than writing SU(3)×SU(2)×U(1).  Raw N-lists lose either way.")
    return 0


def print_landscape(args: argparse.Namespace) -> int:
    n = args.landscape
    print("landscape length vs SM word")
    print(f"  N={n}   raw = N · |G| wrapped    gen = |G| + O(log N)")
    print()
    print(f"  {'G':<22}{'|G|':>6}{'raw N':>8}{'gen N':>8}{'|SM|':>8}{'raw>SM':>8}{'gen<raw':>9}")
    sml = len(SM.encode())
    for g, label in ((U1, "U(1)"), (SM, "SM"), (SU5, "SU(5)")):
        raw = raw_list_len(n, g)
        gen = gen_list_len(n, g)
        print(
            f"  {label:<22}{len(g.encode()):6d}{raw:8d}{gen:8d}{sml:8d}"
            f"{str(raw > sml):>8}{str(gen < raw):>9}"
        )
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--beta", type=float, default=8.0, help="I_dead coefficient")
    p.add_argument("--gamma", type=float, default=8.0, help="I_wrong coefficient")
    p.add_argument("--sample", choices=("none", "sm"), default="sm", help="low-energy sample filter")
    p.add_argument("--compare", action="store_true")
    p.add_argument("--landscape", type=int, default=0, metavar="N", help="print raw vs gen lengths at N")
    p.add_argument("--top", type=int, default=12)
    p.add_argument("--self-check", action="store_true")
    args = p.parse_args(argv)

    if args.self_check:
        return self_check()
    if args.landscape:
        return print_landscape(args)
    return print_compare(args)


if __name__ == "__main__":
    sys.exit(main())
