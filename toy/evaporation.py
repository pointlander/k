#!/usr/bin/env python3
"""1+1 evaporation k-cycle: Vaidya mass loss plus outgoing radiation.

This is the smallest setting where holography is a process, not a static
Kraft list.

  1. The integer skeleton is an N-bit black-hole microstate s, together with
     a time t (energy already in radiation) and a remaining mass m.
  2. Γ is discrete Vaidya: one Planck unit of Bondi mass becomes outgoing
     flux per tick (CGHS-like constant luminosity), until m = 0.
  3. Einstein supplies the remaining mass: on-shell, m + t = N.
     I_E = |m + t − N|.
  4. Holography of the leftover hole: at most m independent bits fit in
     remaining area m (units 4ℓ_P² = 1).  I_H = max(0, bits_in_hole − m).
  5. Three families of programs for the same s:
       page      — radiation is a reversible function of s; leftover bits
                   = m; K̂_G stays K(s).
       remnant   — all N bits stay inside as m drops; I_H = t.
       scramble  — independent incompressible radiation of length t, and
                   the interior still holds s; pays t extra bits and I_H = t.
  6. K̂_G = K(data | Einstein) + β I_E² + β I_H².
  7. Merge with W ∝ |ψ|² 2^{−K̂_G}.

Units: 4ℓ_P² = ħ = c = 1, so area = bits = mass.  Stdlib only.

This is still an analog — 1+1 is not 3+1, a tick is not a Cauchy
development, and K̂_G is a computable upper bound — but the constraint
is Einstein and the area bound is Kraft.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Kolmogorov upper bound on a bitstring
# ---------------------------------------------------------------------------


def k_bits(s: str) -> int:
    """Shortest description in a tiny language: dump, constants, one run,
    or small period. A computable upper bound on K, honest at small N."""
    n = len(s)
    if n == 0:
        return 2
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


def all_microstates(N: int) -> list[str]:
    return [format(i, f"0{N}b") for i in range(1 << N)]


# ---------------------------------------------------------------------------
# Cauchy data and constraints
# ---------------------------------------------------------------------------


FAMILIES = ("page", "remnant", "scramble")


@dataclass(frozen=True)
class Slice:
    """Evaporation Cauchy data at retarded time t."""

    N: int
    t: int
    m: int
    s: str
    family: str
    on_shell: bool

    @property
    def e(self) -> int:
        """Energy already in radiation (one unit per tick)."""
        return self.t

    def stored_in_hole(self) -> int:
        """Independent bits charged to the remaining hole."""
        if self.family == "page":
            return max(self.N - self.t, 0)
        if self.family in ("remnant", "scramble"):
            return self.N
        raise ValueError(self.family)

    def i_energy(self) -> int:
        """Bondi constraint |m + t − N|. Vanishes on a Vaidya history."""
        return abs(self.m + self.t - self.N)

    def i_holo(self) -> int:
        """Holographic leftover: bits in the hole minus remaining area."""
        return max(self.stored_in_hole() - self.m, 0)

    def k_data(self) -> int:
        """K(data | Einstein). On-shell, Einstein supplies m."""
        ks = k_bits(self.s)
        if self.family in ("page", "remnant"):
            return ks
        if self.family == "scramble":
            return ks + self.t
        raise ValueError(self.family)

    def kg_hat(self, beta: float, crash: bool = False) -> float:
        extra = beta * (self.i_energy() ** 2) + beta * (self.i_holo() ** 2)
        if crash:
            extra += 40.0
        return float(self.k_data()) + extra


def on_shell_mass(N: int, t: int) -> int:
    return max(N - t, 0)


def make_slice(N: int, t: int, s: str, family: str, m: int | None = None) -> Slice:
    on_shell = m is None
    if m is None:
        m = on_shell_mass(N, t)
    return Slice(N=N, t=t, m=m, s=s, family=family, on_shell=on_shell)


# ---------------------------------------------------------------------------
# Einstein inflation Γ: discrete Vaidya
# ---------------------------------------------------------------------------


@dataclass
class Development:
    """Γ(s): a Vaidya evaporation history, or a crash past complete evaporation."""

    times: list[int]
    mass: list[int]
    kg: list[float]
    i_energy: list[int]
    i_holo: list[int]
    crashed: bool


def step(sl: Slice) -> Slice:
    """One tick of constant 1+1 luminosity: t → t+1, on-shell m → m−1."""
    t2 = sl.t + 1
    m2 = on_shell_mass(sl.N, t2) if sl.on_shell else sl.m
    return Slice(N=sl.N, t=t2, m=m2, s=sl.s, family=sl.family, on_shell=sl.on_shell)


def evaporate(sl: Slice, beta: float, t_max: int | None = None) -> Development:
    """Integrate from the current slice until complete evaporation (or t_max)."""
    stop = sl.N if t_max is None else min(t_max, sl.N)
    cur = sl
    crashed = False
    times = [cur.t]
    mass = [cur.m]
    kg = [cur.kg_hat(beta)]
    iE = [cur.i_energy()]
    iH = [cur.i_holo()]
    while cur.t < stop:
        nxt = step(cur)
        if nxt.t > cur.N:
            crashed = True
            break
        cur = nxt
        times.append(cur.t)
        mass.append(cur.m)
        kg.append(cur.kg_hat(beta))
        iE.append(cur.i_energy())
        iH.append(cur.i_holo())
    return Development(times, mass, kg, iE, iH, crashed)


# ---------------------------------------------------------------------------
# Born measure, universe, merge
# ---------------------------------------------------------------------------


def log_born(s: str, state: str) -> float:
    """log |ψ|² on microstates. Families share the Born mass of s."""
    if state == "uniform":
        return 0.0
    if state == "schwarzschild":
        # Kolmogorov vacuum: short holes (constants) are cheap samples.
        return -float(k_bits(s)) * math.log(2.0)
    raise ValueError(state)


def logsumexp(vals: list[float]) -> float:
    finite = [v for v in vals if math.isfinite(v)]
    if not finite:
        return float("-inf")
    m = max(finite)
    return m + math.log(sum(math.exp(v - m) for v in finite))


@dataclass
class Universe:
    data: Slice
    born: float
    k_hat: float
    i_energy: int
    i_holo: int
    w: float = 0.0


def run_cycle(
    N: int,
    t: int,
    beta: float,
    state: str,
    include_offshell: bool,
) -> list[Universe]:
    """Merge at a fixed retarded time t over microstates and families."""
    samples: list[Slice] = []
    for s in all_microstates(N):
        for family in FAMILIES:
            samples.append(make_slice(N, t, s, family))
            if include_offshell:
                # Energy-violating: remaining mass frozen at N while flux has left.
                if t > 0:
                    samples.append(make_slice(N, t, s, family, m=N))
                # Energy-violating: leftover gone too early.
                if t < N:
                    samples.append(make_slice(N, t, s, family, m=0))

    universes: list[Universe] = []
    log_borns: list[float] = []
    log_ws: list[float] = []
    for data in samples:
        lb = log_born(data.s, state)
        if not math.isfinite(lb):
            continue
        crash = data.t > data.N
        k = data.kg_hat(beta, crash=crash)
        log_borns.append(lb)
        log_ws.append(lb - k * math.log(2.0))
        universes.append(
            Universe(
                data=data,
                born=lb,
                k_hat=k,
                i_energy=data.i_energy(),
                i_holo=data.i_holo(),
            )
        )

    if not universes:
        raise RuntimeError("all evaporation weights vanished")
    lZ = logsumexp(log_ws)
    lB = logsumexp(log_borns)
    for u, lw, lb in zip(universes, log_ws, log_borns):
        u.w = math.exp(lw - lZ)
        u.born = math.exp(lb - lB)
    return universes


def entropy(ws: list[float]) -> float:
    return -sum(w * math.log2(w) for w in ws if w > 0.0)


def family_mass(us: list[Universe], family: str, on_shell: bool | None = True) -> float:
    tot = 0.0
    for u in us:
        if u.data.family != family:
            continue
        if on_shell is not None and u.data.on_shell != on_shell:
            continue
        tot += u.w
    return tot


def family_mean_k(us: list[Universe], family: str) -> float:
    num = 0.0
    den = 0.0
    for u in us:
        if u.data.family != family or not u.data.on_shell:
            continue
        num += u.w * u.k_hat
        den += u.w
    return num / den if den > 0.0 else float("nan")


# ---------------------------------------------------------------------------
# Self-check
# ---------------------------------------------------------------------------


def self_check() -> int:
    """Constraint identities, constant Page K, remnant growth, merge dominance."""
    N = 6
    beta = 1.0
    s0 = "0" * N
    s1 = "101100"

    page0 = make_slice(N, 0, s0, "page")
    if page0.i_energy() != 0 or page0.i_holo() != 0:
        print(f"FAIL: initial Page constraints {page0.i_energy()} {page0.i_holo()}")
        return 1
    if page0.m != N:
        print(f"FAIL: initial mass {page0.m} != {N}")
        return 1

    # Page K̂_G is constant along the Vaidya history.
    hist = evaporate(page0, beta)
    k0 = hist.kg[0]
    if any(abs(k - k0) > 1e-12 for k in hist.kg):
        print(f"FAIL: Page K̂_G not constant: {hist.kg}")
        return 1
    if hist.mass[-1] != 0 or hist.times[-1] != N:
        print(f"FAIL: complete evaporation m={hist.mass[-1]} t={hist.times[-1]}")
        return 1
    if any(e != 0 for e in hist.i_energy):
        print("FAIL: Page I_E along history")
        return 1
    if any(h != 0 for h in hist.i_holo):
        print("FAIL: Page I_H along history")
        return 1

    # Remnant pays t², scramble pays t plus t².
    for t in range(N + 1):
        p = make_slice(N, t, s1, "page")
        r = make_slice(N, t, s1, "remnant")
        c = make_slice(N, t, s1, "scramble")
        if p.i_energy() != 0 or r.i_energy() != 0 or c.i_energy() != 0:
            print(f"FAIL: on-shell I_E at t={t}")
            return 1
        if p.i_holo() != 0:
            print(f"FAIL: Page I_H={p.i_holo()} at t={t}")
            return 1
        if r.i_holo() != t:
            print(f"FAIL: remnant I_H={r.i_holo()} want {t}")
            return 1
        if c.i_holo() != t:
            print(f"FAIL: scramble I_H={c.i_holo()} want {t}")
            return 1
        kp, kr, kc = p.kg_hat(beta), r.kg_hat(beta), c.kg_hat(beta)
        if abs(kr - (kp + beta * t * t)) > 1e-12:
            print(f"FAIL: remnant K={kr} want {kp + beta * t * t}")
            return 1
        if abs(kc - (kp + t + beta * t * t)) > 1e-12:
            print(f"FAIL: scramble K={kc} want {kp + t + beta * t * t}")
            return 1

    off = make_slice(N, 2, s0, "page", m=N)
    if off.i_energy() != 2:
        print(f"FAIL: off-shell I_E={off.i_energy()} want 2")
        return 1
    if off.on_shell:
        print("FAIL: frozen-mass slice should be off-shell")
        return 1

    # Merge: Page family takes over after a few ticks.
    t = N // 2
    us = run_cycle(N, t, beta, state="uniform", include_offshell=True)
    w_page = family_mass(us, "page")
    w_rem = family_mass(us, "remnant")
    w_scr = family_mass(us, "scramble")
    w_on = sum(u.w for u in us if u.data.on_shell)
    b_on = sum(u.born for u in us if u.data.on_shell)
    if w_page <= 0.8:
        print(f"FAIL: Page merge mass {w_page:.4f} at t={t}")
        return 1
    if not (w_page > w_rem > w_scr - 1e-15):
        print(f"FAIL: expected W_page > W_remnant > W_scramble: {w_page} {w_rem} {w_scr}")
        return 1
    if w_on <= b_on:
        print(f"FAIL: on-shell dominance absent W_on={w_on:.4f} Born_on={b_on:.4f}")
        return 1

    # Schwarzschild (constant s) is the shortest Page program.
    k_short = k_bits(s0)
    k_typ = k_bits(s1)
    if k_short != 2:
        print(f"FAIL: Schwarzschild K={k_short} want 2")
        return 1
    if not (k_typ > k_short):
        print(f"FAIL: typical microstate should be longer than Schwarzschild")
        return 1

    print("self-check ok")
    print(f"  Page I_E, I_H along history     0")
    print(f"  Page K̂_G constant               {k0:.3f}   (Schwarzschild s=0^{N})")
    print(f"  remnant K̂_G(t)                  K_page + β t²")
    print(f"  scramble K̂_G(t)                 K_page + t + β t²")
    print(f"  t={t}  W_page={w_page:.4f}  W_remnant={w_rem:.4f}  W_scramble={w_scr:.4f}")
    print(f"  on-shell Born mass              {b_on:.4f}")
    print(f"  on-shell merge mass             {w_on:.4f}   (Einsteinian dominance)")
    return 0


def _row(t: int, us: list[Universe]) -> dict:
    star = max((u for u in us if u.data.on_shell), key=lambda u: u.w)
    return {
        "t": t,
        "m": on_shell_mass(star.data.N, t),
        "page": family_mass(us, "page"),
        "remnant": family_mass(us, "remnant"),
        "scramble": family_mass(us, "scramble"),
        "on": sum(u.w for u in us if u.data.on_shell),
        "k_page": family_mean_k(us, "page"),
        "k_rem": family_mean_k(us, "remnant"),
        "k_scr": family_mean_k(us, "scramble"),
        "entropy": entropy([u.w for u in us]),
        "typical_family": star.data.family,
        "typical_k": star.k_hat,
        "typical_s": star.data.s,
    }


def compare_families(args: argparse.Namespace) -> int:
    """Page vs remnant vs scramble at every tick."""
    print("Page vs remnant vs scramble")
    print(f"  N={args.bits}  β={args.beta:g}  |Ω⟩={args.state}  4ℓ_P²=1")
    print("  page:     radiation is a function of s; K̂_G = K(s)")
    print("  remnant:  bits stay inside; I_H = t, K̂_G = K(s) + β t²")
    print("  scramble: independent radiation; K̂_G = K(s) + t + β t²")
    print()
    print(
        f"  {'t':>3}{'m':>4}{'W_page':>10}{'W_rem':>10}{'W_scr':>10}"
        f"{'⟨K_p⟩':>8}{'⟨K_r⟩':>8}{'⟨K_s⟩':>8}{'on':>8}{'H(W)':>8}{'typ':>10}"
    )
    include_off = not args.no_offshell
    last = None
    for t in range(args.bits + 1):
        us = run_cycle(args.bits, t, args.beta, args.state, include_off)
        r = _row(t, us)
        last = r
        print(
            f"  {r['t']:3d}{r['m']:4d}{r['page']:10.4f}{r['remnant']:10.4f}{r['scramble']:10.4f}"
            f"{r['k_page']:8.2f}{r['k_rem']:8.2f}{r['k_scr']:8.2f}"
            f"{r['on']:8.4f}{r['entropy']:8.3f}{r['typical_family']:>10}"
        )
    assert last is not None
    print()
    print("  K̂_G of hole+radiation stays K(s) on the Page family and grows")
    print("  for remnants and scrambles. That is holography along the history.")
    return 0


def print_history(args: argparse.Namespace) -> int:
    """Vaidya trajectories of one short and one typical microstate."""
    N = args.bits
    beta = args.beta
    short = "0" * N
    # A non-constant, non-periodic string so K is the raw dump.
    typical = "".join("1" if (i * 3 + 1) % 5 < 2 else "0" for i in range(N))
    print("Vaidya histories")
    print(f"  N={N}  β={beta:g}")
    print(f"  Schwarzschild s={short}   K={k_bits(short)}")
    print(f"  typical        s={typical}   K={k_bits(typical)}")
    print()
    print(
        f"  {'t':>3}{'m':>4}"
        f"{'K_page0':>10}{'K_rem0':>10}{'K_scr0':>10}"
        f"{'K_page*':>10}{'K_rem*':>10}{'K_scr*':>10}"
    )
    for t in range(N + 1):
        row = [t, on_shell_mass(N, t)]
        for s in (short, typical):
            for family in FAMILIES:
                row.append(make_slice(N, t, s, family).kg_hat(beta))
        print(
            f"  {row[0]:3d}{row[1]:4d}"
            + "".join(f"{v:10.2f}" for v in row[2:])
        )
    print()
    print("  page0 = Schwarzschild Page (constant K̂_G); page* = typical Page.")
    print("  remnant/scramble columns grow; Page columns do not.")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--bits", type=int, default=6, help="initial area N in bits (2–10). default 6")
    p.add_argument("--beta", type=float, default=1.0, help="I_E² and I_H² coefficient in K̂_G")
    p.add_argument("--t", type=int, default=None, help="snapshot retarded time (default N/2)")
    p.add_argument("--state", choices=("uniform", "schwarzschild"), default="uniform")
    p.add_argument("--compare", action="store_true", help="Page vs remnant vs scramble at every tick")
    p.add_argument("--history", action="store_true", help="Vaidya K̂_G(t) for one short and one typical s")
    p.add_argument("--no-offshell", action="store_true", help="only the Einstein (m = N − t) slice")
    p.add_argument("--top", type=int, default=8)
    p.add_argument("--self-check", action="store_true")
    args = p.parse_args(argv)

    if args.self_check:
        return self_check()
    if args.bits < 2 or args.bits > 10:
        p.error("--bits must be in [2, 10]")
    if args.compare:
        return compare_families(args)
    if args.history:
        return print_history(args)

    t = args.bits // 2 if args.t is None else args.t
    if t < 0 or t > args.bits:
        p.error("--t must be in [0, N]")

    include_off = not args.no_offshell
    universes = run_cycle(args.bits, t, args.beta, args.state, include_off)

    n_on = sum(1 for u in universes if u.data.on_shell)
    n_off = len(universes) - n_on
    w_on = sum(u.w for u in universes if u.data.on_shell)
    b_on = sum(u.born for u in universes if u.data.on_shell)
    w_page = family_mass(universes, "page")
    w_rem = family_mass(universes, "remnant")
    w_scr = family_mass(universes, "scramble")

    star = max(universes, key=lambda u: u.w)
    born_H = entropy([u.born for u in universes])
    merge_H = entropy([u.w for u in universes])

    print("1+1 evaporation k-cycle")
    extra = "  + off-shell masses" if include_off else ""
    print(f"  skeleton       N={args.bits} bit microstates × 3 families{extra}")
    print(f"  samples        {len(universes)}   (on-shell {n_on}, off-shell {n_off})")
    print(f"  snapshot       t={t}  m={on_shell_mass(args.bits, t)}  (Page time is t=N/2)")
    print(f"  state          |Ω⟩ = {args.state}")
    print(f"  weight         W ∝ |ψ|² 2^{{-K̂_G}},  K̂_G = K(data|Einstein) + {args.beta:g} (I_E² + I_H²)")
    print(f"  Born entropy   {born_H:.3f} bits")
    print(f"  merge entropy  {merge_H:.3f} bits")
    print()
    print("  Einsteinian / holographic dominance")
    print(f"    on-shell Born mass     {b_on:.4f}")
    print(f"    on-shell merge mass    {w_on:.4f}")
    print(f"    Page merge mass        {w_page:.4f}")
    print(f"    remnant merge mass     {w_rem:.4f}")
    print(f"    scramble merge mass    {w_scr:.4f}")
    print()
    d = star.data
    print(
        f"  typical universe   family={d.family}  on_shell={d.on_shell}  "
        f"t={d.t}  m={d.m}  s={d.s}"
    )
    print(
        f"                     W={star.w:.4f}  Born={star.born:.4f}  "
        f"K̂_G={star.k_hat:.2f}  I_E={star.i_energy}  I_H={star.i_holo}"
    )
    print()
    print(
        f"  {'rank':<5}{'family':<10}{'shell':<8}{'t':>3}{'m':>4}"
        f"{'W':>10}{'Born':>10}{'K̂_G':>8}{'I_E':>6}{'I_H':>6}{'s':>14}"
    )
    ranked = sorted(universes, key=lambda u: -u.w)
    for i, u in enumerate(ranked[: args.top], 1):
        d = u.data
        shell = "on" if d.on_shell else "off"
        print(
            f"  {i:<5}{d.family:<10}{shell:<8}{d.t:3d}{d.m:4d}"
            f"{u.w:10.4f}{u.born:10.4f}{u.k_hat:8.2f}{u.i_energy:6d}{u.i_holo:6d}{d.s:>14}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
