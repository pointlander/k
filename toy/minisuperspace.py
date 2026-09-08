#!/usr/bin/env python3
"""Minisuperspace k-cycle: FLRW + a homogeneous scalar.

This is the smallest setting where inflation Γ is an Einstein solver.

  1. The integer skeleton is finite-bit Cauchy data (a, H, φ, φ̇).
  2. Sampling draws from a Born measure: Hartle–Hawking or Vilenkin
     minisuperspace |Ψ|² (or a Gaussian / uniform control), on the
     on-shell slice where Einstein's constraint solves for H.
  3. Γ integrates the minisuperspace Einstein–Klein–Gordon system (RK4).
  4. K̂_G = K(data | Einstein) + β I_off².
     On-shell 3-data does not pay for H (the constraint supplies it).
     Off-shell 4-data pays I_off = |3(H² + k/a²) − ρ|.
  5. Universes are merged with W(s) ∝ |ψ_s|² 2^{-K̂_G(s)}.

Units: 8πG = ħ = c = 1.  Stdlib only.

This is still an analog — minisuperspace is not full GR, RK4 is not a
maximal Cauchy development, and K̂_G is a computable upper bound — but
Γ is now Einstein, not a cycle graph.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# Potential
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Potential:
    """Scalar potential. `lambda` is a cosmological constant; `quadratic` is ½ m² φ²."""

    kind: str = "lambda"
    V0: float = 0.5
    m: float = 0.4

    def V(self, phi: float) -> float:
        if self.kind == "lambda":
            return self.V0
        if self.kind == "quadratic":
            return 0.5 * self.m * self.m * phi * phi
        raise ValueError(self.kind)

    def dV(self, phi: float) -> float:
        if self.kind == "lambda":
            return 0.0
        if self.kind == "quadratic":
            return self.m * self.m * phi
        raise ValueError(self.kind)


# ---------------------------------------------------------------------------
# Cauchy data and constraint
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Cauchy:
    """Minisuperspace Cauchy data in the N = 1 gauge."""

    a: float
    H: float
    phi: float
    p: float  # φ̇
    on_shell: bool
    indices: tuple[int, ...]

    def rho(self, pot: Potential) -> float:
        return 0.5 * self.p * self.p + pot.V(self.phi)

    def constraint(self, pot: Potential, curv: int) -> float:
        """Hamiltonian constraint C = 3(H² + k/a²) − ρ.  Vanishes on shell."""
        if self.a <= 0.0:
            return float("inf")
        return 3.0 * (self.H * self.H + curv / (self.a * self.a)) - self.rho(pot)

    def i_off(self, pot: Potential, curv: int) -> float:
        c = self.constraint(pot, curv)
        if not math.isfinite(c):
            return float("inf")
        return abs(c)


def H_from_constraint(a: float, phi: float, p: float, pot: Potential, curv: int) -> float | None:
    """Expanding-branch Hubble from the Friedmann constraint, or None if imaginary."""
    if a <= 0.0:
        return None
    rho = 0.5 * p * p + pot.V(phi)
    disc = rho / 3.0 - curv / (a * a)
    if disc < 0.0:
        return None
    return math.sqrt(disc)


# ---------------------------------------------------------------------------
# Einstein inflation Γ: RK4 of Einstein–Klein–Gordon
# ---------------------------------------------------------------------------

# State is (a, H, φ, p).  Off-shell H evolves as ȧ/a without substituting Friedmann.
# ä/a = −(ρ + 3p_fluid)/6 = (V − φ̇²)/3, independent of spatial curvature.


def _deriv(y: tuple[float, float, float, float], pot: Potential) -> tuple[float, float, float, float]:
    a, H, phi, p = y
    if a <= 0.0 or not all(math.isfinite(v) for v in y):
        return (0.0, 0.0, 0.0, 0.0)
    adot = H * a
    Hdot = (pot.V(phi) - p * p) / 3.0 - H * H
    phidot = p
    pdot = -3.0 * H * p - pot.dV(phi)
    return (adot, Hdot, phidot, pdot)


def _rk4_step(
    y: tuple[float, float, float, float], dt: float, pot: Potential
) -> tuple[float, float, float, float]:
    k1 = _deriv(y, pot)

    def add(yy, kk, s):
        return tuple(yi + s * ki for yi, ki in zip(yy, kk))

    k2 = _deriv(add(y, k1, 0.5 * dt), pot)
    k3 = _deriv(add(y, k2, 0.5 * dt), pot)
    k4 = _deriv(add(y, k3, dt), pot)
    return tuple(yi + (dt / 6.0) * (a + 2 * b + 2 * c + d) for yi, a, b, c, d in zip(y, k1, k2, k3, k4))


@dataclass
class Development:
    """Γ(s): a minisuperspace Einstein development, or a crash."""

    times: list[float]
    scale: list[float]
    phi: list[float]
    crashed: bool
    n_e: float


def inflate(
    data: Cauchy,
    pot: Potential,
    t_max: float = 12.0,
    dt: float = 0.05,
    record_every: int = 4,
) -> Development:
    y: tuple[float, float, float, float] = (data.a, data.H, data.phi, data.p)
    t = 0.0
    times = [0.0]
    scale = [data.a]
    phi = [data.phi]
    crashed = False
    a0 = data.a
    step = 0
    nsteps = int(t_max / dt)
    for step in range(1, nsteps + 1):
        y = _rk4_step(y, dt, pot)
        t = step * dt
        a, H, ph, p = y
        if (
            a <= 1e-6
            or a > 1e6
            or abs(H) > 50.0
            or abs(p) > 50.0
            or not all(math.isfinite(v) for v in y)
        ):
            crashed = True
            break
        if step % record_every == 0 or step == nsteps:
            times.append(t)
            scale.append(a)
            phi.append(ph)
    a_final = scale[-1] if scale else a0
    n_e = math.log(a_final / a0) if a0 > 0.0 and a_final > 0.0 else float("-inf")
    if crashed:
        n_e = float("-inf")
    return Development(times=times, scale=scale, phi=phi, crashed=crashed, n_e=n_e)


# ---------------------------------------------------------------------------
# Kolmogorov upper bound on Cauchy data
# ---------------------------------------------------------------------------


def k_indices(idx: tuple[int, ...], nbits: int) -> int:
    """Shortest description in a tiny language over integer bins.

    The middle bin is the vacuum (φ = 0, modest a, modest H).  Index 0 is
    the edge of the range, not a short program.
    """
    raw = nbits * len(idx) + 1
    if not idx:
        return 2
    mid = (1 << nbits) // 2
    centered = tuple(i - mid for i in idx)
    if all(c == 0 for c in centered):
        return 2
    if all(c == centered[0] for c in centered):
        return 2 + nbits
    nz = [c for c in centered if c != 0]
    if len(nz) == 1:
        return 3 + nbits
    return raw


def kg_hat(
    data: Cauchy,
    pot: Potential,
    curv: int,
    nbits: int,
    beta: float,
    crash: bool,
) -> tuple[float, float]:
    """K̂_G = K(data | Einstein) + β I_off² + crash penalty.

    On-shell, Einstein supplies H, so those bits are not paid.
    """
    i_off = data.i_off(pot, curv)
    if data.on_shell:
        payload = data.indices  # already the 3-data (a, φ, p)
    else:
        payload = data.indices
    k_data = float(k_indices(payload, nbits))
    extra = 0.0 if i_off == float("inf") else beta * (i_off ** 2)
    if crash or i_off == float("inf"):
        extra += 40.0
    return k_data + extra, i_off


# ---------------------------------------------------------------------------
# Grid, Born measure, sampling
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Grid:
    nbits: int
    a_min: float = 0.4
    a_max: float = 8.0
    phi_max: float = 3.0
    H_max: float = 1.5
    p_max: float = 1.5

    @property
    def n(self) -> int:
        return 1 << self.nbits

    def decode_lin(self, k: int, lo: float, hi: float) -> float:
        return lo + (k + 0.5) * (hi - lo) / self.n

    def decode_log(self, k: int) -> float:
        lo = math.log(self.a_min)
        hi = math.log(self.a_max)
        return math.exp(self.decode_lin(k, lo, hi))

    def a(self, ia: int) -> float:
        return self.decode_log(ia)

    def phi(self, ip: int) -> float:
        return self.decode_lin(ip, -self.phi_max, self.phi_max)

    def H(self, ih: int) -> float:
        return self.decode_lin(ih, -self.H_max, self.H_max)

    def p(self, ip: int) -> float:
        return self.decode_lin(ip, -self.p_max, self.p_max)


# 24π² in 8πG = 1: S^4 equator |I_E| = 12π²/V, so |Ψ|² ~ exp(±24π² I_0)
# with I_0(turning point) = 1/V.
_TWENTY_FOUR_PI_SQ = 24.0 * math.pi * math.pi
_V_MIN = 1e-8


def instanton_I0(a: float, V: float, curv: int) -> float:
    """Halliwell under-barrier integral I_0, 8πG = 1.

    At the closed-FLRW turning point a² = 3/V, I_0 = 1/V, so
    24π² I_0 = 24π²/V, the standard HH/tunneling exponent.
    For k = 0 there is no compact cap; use the nucleation value 1/V.
    """
    V_eff = max(V, _V_MIN)
    if curv == 0:
        return 1.0 / V_eff
    a_tp = math.sqrt(3.0 / V_eff)
    if a_tp <= 0.0:
        return 1.0 / V_eff
    x = min(max(a, 0.0), a_tp) / a_tp
    return (a_tp * a_tp / 3.0) * (1.0 - (1.0 - x * x) ** 1.5)


def log_born(data: Cauchy, pot: Potential, state: str, curv: int, kappa: float = 4.0) -> float:
    """log |ψ|² for the Kolmogorov vacuum.

    hh / tunneling are minisuperspace WKB amplitudes, not Gaussians.
    `gaussian` is the old kinematic envelope, kept as a control.
    """
    V = pot.V(data.phi)
    expanding = 0.0 if data.H >= 0.0 else -4.0  # mild log-penalty for contracting
    if state == "uniform":
        return expanding
    if state == "gaussian":
        Hd = math.sqrt(max(V, 1e-12) / 3.0)
        dH = data.H - Hd
        chi2 = (dH / 1.5) ** 2 + (data.p / 1.5) ** 2 + (data.phi / 3.0) ** 2
        return expanding - 0.5 * kappa * chi2
    I0 = instanton_I0(data.a, V, curv)
    if not math.isfinite(I0):
        return float("-inf")
    s = _TWENTY_FOUR_PI_SQ * I0
    # Cap only the tunneling collapse; HH stays in log-space via log-sum-exp.
    if state == "hh":
        return expanding + s
    if state == "tunneling":
        if V <= _V_MIN:
            return float("-inf")
        return expanding - s
    raise ValueError(state)


def logsumexp(vals: list[float]) -> float:
    finite = [v for v in vals if math.isfinite(v)]
    if not finite:
        return float("-inf")
    m = max(finite)
    return m + math.log(sum(math.exp(v - m) for v in finite))


def on_shell_slice(grid: Grid, pot: Potential, curv: int) -> list[Cauchy]:
    """3-data (a, φ, p) with H supplied by the Friedmann constraint (expanding)."""
    out: list[Cauchy] = []
    n = grid.n
    for ia in range(n):
        for iphi in range(n):
            for ip in range(n):
                a = grid.a(ia)
                phi = grid.phi(iphi)
                p = grid.p(ip)
                H = H_from_constraint(a, phi, p, pot, curv)
                if H is None:
                    continue
                out.append(
                    Cauchy(
                        a=a,
                        H=H,
                        phi=phi,
                        p=p,
                        on_shell=True,
                        indices=(ia, iphi, ip),
                    )
                )
    return out


def off_shell_grid(grid: Grid) -> list[Cauchy]:
    """Generic 4-data: H is specified independently of Einstein."""
    out: list[Cauchy] = []
    n = grid.n
    for ia in range(n):
        for ih in range(n):
            for iphi in range(n):
                for ip in range(n):
                    out.append(
                        Cauchy(
                            a=grid.a(ia),
                            H=grid.H(ih),
                            phi=grid.phi(iphi),
                            p=grid.p(ip),
                            on_shell=False,
                            indices=(ia, ih, iphi, ip),
                        )
                    )
    return out


# ---------------------------------------------------------------------------
# Universe, merge
# ---------------------------------------------------------------------------


@dataclass
class Universe:
    data: Cauchy
    born: float
    i_off: float
    k_hat: float
    n_e: float
    crashed: bool
    w: float = 0.0
    scale: list[float] = field(default_factory=list)
    times: list[float] = field(default_factory=list)


def interpolate_a(dev: Development, t: float) -> float | None:
    if not dev.times or t > dev.times[-1] + 1e-12:
        return None
    if t <= dev.times[0]:
        return dev.scale[0]
    for i in range(1, len(dev.times)):
        if t <= dev.times[i]:
            t0, t1 = dev.times[i - 1], dev.times[i]
            a0, a1 = dev.scale[i - 1], dev.scale[i]
            if t1 == t0:
                return a1
            x = (t - t0) / (t1 - t0)
            return a0 + x * (a1 - a0)
    return dev.scale[-1]


def run_cycle(
    grid: Grid,
    pot: Potential,
    curv: int,
    beta: float,
    state: str,
    include_offshell: bool,
    t_max: float,
    dt: float,
) -> list[Universe]:
    samples = on_shell_slice(grid, pot, curv)
    if include_offshell:
        samples = samples + off_shell_grid(grid)

    universes: list[Universe] = []
    log_borns: list[float] = []
    log_ws: list[float] = []
    for data in samples:
        lb = log_born(data, pot, state, curv)
        if not math.isfinite(lb):
            continue
        dev = inflate(data, pot, t_max=t_max, dt=dt)
        k, i_off = kg_hat(data, pot, curv, grid.nbits, beta, dev.crashed)
        log_borns.append(lb)
        log_ws.append(lb - k * math.log(2.0))
        universes.append(
            Universe(
                data=data,
                born=lb,  # replaced by normalized mass below
                i_off=i_off if i_off != float("inf") else 1e9,
                k_hat=k,
                n_e=dev.n_e if math.isfinite(dev.n_e) else float("-inf"),
                crashed=dev.crashed,
                scale=dev.scale,
                times=dev.times,
            )
        )

    if not universes:
        raise RuntimeError("all minisuperspace weights vanished")
    lZ = logsumexp(log_ws)
    lB = logsumexp(log_borns)
    for u, lw, lb in zip(universes, log_ws, log_borns):
        u.w = math.exp(lw - lZ)
        u.born = math.exp(lb - lB)
    return universes


def merge_a(universes: list[Universe], times: list[float]) -> list[float]:
    """Survivor-renormalized weighted scale factor at each t."""
    out: list[float] = []
    for t in times:
        num = 0.0
        den = 0.0
        for u in universes:
            if u.crashed or not u.times:
                continue
            a = interpolate_a(
                Development(u.times, u.scale, [], u.crashed, u.n_e),
                t,
            )
            if a is None:
                continue
            num += u.w * a
            den += u.w
        out.append(num / den if den > 0.0 else float("nan"))
    return out


def entropy(ws: list[float]) -> float:
    return -sum(w * math.log2(w) for w in ws if w > 0.0)


def weighted_mean(universes: list[Universe], f) -> float:
    num = 0.0
    den = 0.0
    for u in universes:
        val = f(u)
        if not math.isfinite(val):
            continue
        num += u.w * val
        den += u.w
    return num / den if den > 0.0 else float("nan")


# ---------------------------------------------------------------------------
# Self-check
# ---------------------------------------------------------------------------


def self_check() -> int:
    """Closed-form de Sitter test of Γ, plus a tiny dominance check."""
    pot = Potential("lambda", V0=0.5)
    H = math.sqrt(pot.V0 / 3.0)
    data = Cauchy(a=1.0, H=H, phi=0.0, p=0.0, on_shell=True, indices=(0, 0, 0))
    i_off = data.i_off(pot, 0)
    if i_off > 1e-12:
        print(f"FAIL: on-shell de Sitter I_off = {i_off}")
        return 1
    dev = inflate(data, pot, t_max=2.0, dt=0.02, record_every=1)
    t = dev.times[-1]
    a_expected = math.exp(H * t)
    rel = abs(dev.scale[-1] - a_expected) / a_expected
    if rel > 0.02:
        print(f"FAIL: de Sitter a(t) relative error {rel:.4f} (got {dev.scale[-1]:.4f}, want {a_expected:.4f})")
        return 1
    if dev.crashed:
        print("FAIL: de Sitter crashed")
        return 1

    off = Cauchy(a=1.0, H=0.0, phi=0.0, p=0.0, on_shell=False, indices=(0, 0, 0, 0))
    if off.i_off(pot, 0) < 0.1:
        print("FAIL: off-shell Minkowski-with-V should violate Friedmann")
        return 1

    grid = Grid(nbits=2)
    us = run_cycle(grid, pot, curv=0, beta=8.0, state="hh", include_offshell=True, t_max=4.0, dt=0.1)
    w_on = sum(u.w for u in us if u.data.on_shell and not u.crashed)
    b_on = sum(u.born for u in us if u.data.on_shell and not u.crashed)
    if w_on <= b_on:
        print(f"FAIL: Einsteinian dominance absent: W_on={w_on:.4f} Born_on={b_on:.4f}")
        return 1

    qpot = Potential("quadratic", m=0.4)
    hh = run_cycle(grid, qpot, curv=0, beta=8.0, state="hh", include_offshell=False, t_max=6.0, dt=0.1)
    tun = run_cycle(grid, qpot, curv=0, beta=8.0, state="tunneling", include_offshell=False, t_max=6.0, dt=0.1)
    phi_hh = weighted_mean(hh, lambda u: abs(u.data.phi))
    phi_t = weighted_mean(tun, lambda u: abs(u.data.phi))
    ne_hh = weighted_mean(hh, lambda u: u.n_e)
    ne_t = weighted_mean(tun, lambda u: u.n_e)
    if not (phi_t > phi_hh):
        print(f"FAIL: tunneling should prefer larger |φ|: HH {phi_hh:.3f} T {phi_t:.3f}")
        return 1
    if not (ne_t > ne_hh):
        print(f"FAIL: tunneling should prefer more e-folds: HH {ne_hh:.3f} T {ne_t:.3f}")
        return 1

    print("self-check ok")
    print(f"  de Sitter I_off          {i_off:.2e}")
    print(f"  de Sitter a(t) rel err   {rel:.2e}   N_e = {dev.n_e:.3f}  (H t = {H * t:.3f})")
    print(f"  on-shell Born mass       {b_on:.4f}")
    print(f"  on-shell merge mass      {w_on:.4f}   (Einsteinian dominance)")
    print(f"  HH  ⟨|φ|⟩={phi_hh:.3f}  ⟨N_e⟩={ne_hh:.3f}")
    print(f"  T   ⟨|φ|⟩={phi_t:.3f}  ⟨N_e⟩={ne_t:.3f}   (tunneling: larger field, more inflation)")
    return 0


def _summarize(us: list[Universe], pot: Potential) -> dict:
    star = max(us, key=lambda u: u.w)
    return {
        "phi": weighted_mean(us, lambda u: abs(u.data.phi)),
        "V": weighted_mean(us, lambda u: pot.V(u.data.phi)),
        "Ne": weighted_mean(us, lambda u: u.n_e),
        "on": sum(u.w for u in us if u.data.on_shell),
        "typical_phi": star.data.phi,
        "typical_a": star.data.a,
        "typical_Ne": star.n_e,
        "typical_W": star.w,
        "entropy": entropy([u.w for u in us]),
    }


def compare_vacua(args: argparse.Namespace) -> int:
    """Hartle–Hawking vs Vilenkin horse race on the same grid."""
    pot = Potential(args.potential, V0=args.V0, m=args.m)
    grid = Grid(args.bits)
    include_off = not args.no_offshell
    rows = []
    for state in ("hh", "tunneling"):
        us = run_cycle(
            grid, pot, args.curvature, args.beta, state, include_off, args.t_max, args.dt
        )
        s = _summarize(us, pot)
        s["state"] = state
        rows.append((state, us, s))

    print("Hartle–Hawking vs tunneling")
    print(f"  potential   {args.potential}  V0={args.V0:g}  m={args.m:g}  k={args.curvature}")
    print(f"  |Ψ_HH|² ∝ exp(+24π² I_0)    |Ψ_T|² ∝ exp(−24π² I_0)")
    print(f"  I_0(turning point) = 1/V    (8πG=1)")
    print()
    print(f"  {'vacuum':<12}{'⟨|φ|⟩':>8}{'⟨V⟩':>10}{'⟨N_e⟩':>8}{'on-shell':>10}{'H(W)':>8}{'typ φ':>8}{'typ N_e':>8}")
    for state, _us, s in rows:
        print(
            f"  {state:<12}{s['phi']:8.3f}{s['V']:10.4f}{s['Ne']:8.3f}"
            f"{s['on']:10.4f}{s['entropy']:8.3f}{s['typical_phi']:8.3f}{s['typical_Ne']:8.3f}"
        )
    hh, tun = rows[0][2], rows[1][2]
    print()
    if args.potential == "lambda":
        print("  λ is constant, so HH and tunneling differ by a global factor;")
        print("  the typical Cauchy data agree. Use --potential quadratic to see the split.")
    else:
        print("  HH prefers small V (little inflation); tunneling prefers large V (more e-folds).")
        print(f"  Δ⟨|φ|⟩ = {tun['phi'] - hh['phi']:+.3f}    Δ⟨N_e⟩ = {tun['Ne'] - hh['Ne']:+.3f}")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--bits", type=int, default=3, help="bits per Cauchy variable (2–4). default 3")
    p.add_argument("--beta", type=float, default=8.0, help="I_off² coefficient in K̂_G")
    p.add_argument("--potential", choices=("lambda", "quadratic"), default="lambda")
    p.add_argument("--V0", type=float, default=0.5, help="cosmological constant (lambda potential)")
    p.add_argument("--m", type=float, default=0.4, help="inflaton mass (quadratic potential)")
    p.add_argument("--curvature", type=int, choices=(0, 1), default=0, help="spatial k in Friedmann")
    p.add_argument("--state", choices=("hh", "tunneling", "gaussian", "uniform"), default="hh")
    p.add_argument("--compare", action="store_true", help="Hartle–Hawking vs tunneling horse race")
    p.add_argument("--no-offshell", action="store_true", help="only the Einstein (constraint-solved) slice")
    p.add_argument("--t-max", type=float, default=8.0)
    p.add_argument("--dt", type=float, default=0.08)
    p.add_argument("--top", type=int, default=8)
    p.add_argument("--self-check", action="store_true")
    args = p.parse_args(argv)

    if args.self_check:
        return self_check()
    if args.compare:
        return compare_vacua(args)

    if args.bits < 2 or args.bits > 4:
        p.error("--bits must be in [2, 4]")

    pot = Potential(args.potential, V0=args.V0, m=args.m)
    grid = Grid(args.bits)
    include_off = not args.no_offshell
    universes = run_cycle(
        grid,
        pot,
        curv=args.curvature,
        beta=args.beta,
        state=args.state,
        include_offshell=include_off,
        t_max=args.t_max,
        dt=args.dt,
    )

    n_on = sum(1 for u in universes if u.data.on_shell)
    n_off = len(universes) - n_on
    w_on = sum(u.w for u in universes if u.data.on_shell)
    b_on = sum(u.born for u in universes if u.data.on_shell)
    w_exp = sum(u.w for u in universes if not u.crashed and u.n_e > 0.5)
    w_crash = sum(u.w for u in universes if u.crashed)
    ne_bar = sum(u.w * u.n_e for u in universes if math.isfinite(u.n_e) and not u.crashed)
    w_surv = sum(u.w for u in universes if not u.crashed)
    ne_bar = ne_bar / w_surv if w_surv > 0 else float("nan")

    star = max(universes, key=lambda u: u.w)
    report_times = [0.0, 1.0, 2.0, 4.0, min(args.t_max, 6.0), args.t_max]
    report_times = [t for t in report_times if t <= args.t_max + 1e-12]
    a_bar = merge_a(universes, report_times)

    born_H = entropy([u.born for u in universes])
    merge_H = entropy([u.w for u in universes])

    print("minisuperspace k-cycle")
    print(f"  skeleton       {args.bits} bits × 4  + on-shell 3-slice")
    print(f"  samples        {len(universes)}   (on-shell {n_on}, off-shell {n_off})")
    print(f"  potential      {args.potential}   V0={args.V0:g}  m={args.m:g}  k={args.curvature}")
    print(f"  state          |Ω⟩ = {args.state}   (hh/tunneling = minisuperspace |Ψ|²)")
    print(f"  weight         W ∝ |ψ|² 2^{{-K̂_G}},  K̂_G = K(data|Einstein) + {args.beta:g} I_off²")
    print(f"  Born entropy   {born_H:.3f} bits")
    print(f"  merge entropy  {merge_H:.3f} bits")
    print()
    print("  Einsteinian dominance")
    print(f"    on-shell Born mass     {b_on:.4f}")
    print(f"    on-shell merge mass    {w_on:.4f}")
    print(f"    expanding (N_e>0.5)    {w_exp:.4f}")
    print(f"    crashed                {w_crash:.4f}")
    print(f"    ⟨N_e⟩_surv             {ne_bar:.3f}")
    print()
    print("  merged ⟨a(t)⟩  (survivors)")
    print("    " + "  ".join(f"t={t:<4g} a={a:.3f}" for t, a in zip(report_times, a_bar)))
    print()
    d = star.data
    I0 = instanton_I0(d.a, pot.V(d.phi), args.curvature)
    print(
        f"  typical universe   on_shell={d.on_shell}  a={d.a:.3f}  H={d.H:.3f}  "
        f"φ={d.phi:.3f}  φ̇={d.p:.3f}"
    )
    print(f"                     I_0={I0:.4g}   24π² I_0={_TWENTY_FOUR_PI_SQ * I0:.4g}")
    print(
        f"                     W={star.w:.4f}  Born={star.born:.4f}  "
        f"K̂_G={star.k_hat:.2f}  I_off={star.i_off:.3e}  N_e={star.n_e:.3f}  crashed={star.crashed}"
    )
    print()
    print(
        f"  {'rank':<5}{'shell':<8}{'a':>7}{'H':>8}{'φ':>8}{'φ̇':>8}"
        f"{'W':>10}{'Born':>10}{'K̂_G':>8}{'I_off':>10}{'N_e':>8}"
    )
    ranked = sorted(universes, key=lambda u: -u.w)
    for i, u in enumerate(ranked[: args.top], 1):
        d = u.data
        shell = "on" if d.on_shell else "off"
        ne = f"{u.n_e:8.2f}" if math.isfinite(u.n_e) else f"{'crash':>8}"
        print(
            f"  {i:<5}{shell:<8}{d.a:7.3f}{d.H:8.3f}{d.phi:8.3f}{d.p:8.3f}"
            f"{u.w:10.4f}{u.born:10.4f}{u.k_hat:8.2f}{u.i_off:10.3e}{ne}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
