/-
Few-qubit Born-correction analog, matching `toy/interferometer.py`.

Prediction 2: `W(a)/W(b) = (born a / born b)  2^{−(K(a)−K(b))}`.
Isolated short-vs-dump disagrees with Born.  Two short clicks, and a
thermal bath with `K(env) ≥ K(register)` on both branches, track Born.
Additive `K(env)+K(register)` does *not* swamp: a large fridge is not
enough.  Laboratory unobservability is thermal typicality or ΔK = O(1)
clicks, not the mere existence of environment bits.

Circuit-level error bars are not proved.  What is proved is the
algebraic core the Python analog uses.
-/

import K.Complexity
import Init.Omega

namespace K
namespace Lab

/-- Isolated device: the register *is* the sample. -/
def kgIsolated (kReg : Nat) : Nat := kReg

/-- Additive scoring.  A shared fridge of length `kEnv` does not cancel ΔK. -/
def kgAdditive (kReg kEnv : Nat) : Nat := kReg + kEnv

/-- Coarse thermal bound: `K̂ = max(K(env), K(reg))`.

A typical bath of length `kEnv ≥ K(dump)` makes both branches cost `kEnv`. -/
def kgThermal (kReg kEnv : Nat) : Nat := max kReg kEnv

def weight (born kg M : Nat) : Nat :=
  born * 2 ^ (M - kg)

def shortK : Nat := 2

/-! ### Isolated bias and laboratory clicks -/

/-- Isolated short-vs-dump: equal Born, dump pays `c` extra bits, short
branch is favoured by `2^c`.  This is eq. (born-corr) on a register. -/
theorem isolated_bias
    (kShort kDump c bornShort bornDump M : Nat)
    (hc : kShort + c ≤ kDump)
    (hS : kShort ≤ M) (hD : kDump ≤ M) :
    weight bornDump kDump M * bornShort * 2 ^ c ≤
      weight bornShort kShort M * bornDump :=
  weight_ratio hc hS hD

/-- Two outcomes of equal program length: W tracks Born. -/
theorem equal_k_tracks_born (k bornA bornB M : Nat) (_hk : k ≤ M) :
    weight bornA k M * bornB = weight bornB k M * bornA := by
  simp [weight, Nat.mul_left_comm, Nat.mul_comm]

/-- Named detector clicks: both constants, `K = 2`, W tracks Born. -/
theorem clicks_track_born (bornA bornB M : Nat) (h : shortK ≤ M) :
    weight bornA shortK M * bornB = weight bornB shortK M * bornA :=
  equal_k_tracks_born shortK bornA bornB M h

/-! ### Additive environment: no swamp -/

theorem additive_delta (kA kB kEnv : Nat) (h : kA ≤ kB) :
    kgAdditive kB kEnv - kgAdditive kA kEnv = kB - kA := by
  simp [kgAdditive]
  omega

/-- The isolated ΔK is exactly the additive ΔK, for any fridge size. -/
theorem additive_no_swamp (kA kB kEnv : Nat) (h : kA ≤ kB) :
    kgAdditive kB kEnv - kgAdditive kA kEnv =
      kgIsolated kB - kgIsolated kA := by
  simp [kgIsolated, additive_delta kA kB kEnv h]

theorem additive_bias
    (kA kB c kEnv bornA bornB M : Nat)
    (hc : kA + c ≤ kB)
    (hA : kA + kEnv ≤ M) (hB : kB + kEnv ≤ M) :
    weight bornB (kgAdditive kB kEnv) M * bornA * 2 ^ c ≤
      weight bornA (kgAdditive kA kEnv) M * bornB := by
  have : kgAdditive kA kEnv + c ≤ kgAdditive kB kEnv := by
    simp [kgAdditive]
    omega
  exact weight_ratio this hA hB

/-! ### Thermal swamp -/

theorem thermal_swamp (kA kB kEnv : Nat)
    (hA : kA ≤ kEnv) (hB : kB ≤ kEnv) :
    kgThermal kA kEnv = kEnv ∧ kgThermal kB kEnv = kEnv := by
  simp [kgThermal]
  omega

/-- Once the bath is at least as costly as either register, thermal ΔK
vanishes and W tracks Born. -/
theorem thermal_tracks_born
    (kA kB kEnv bornA bornB M : Nat)
    (hA : kA ≤ kEnv) (hB : kB ≤ kEnv) (_hM : kEnv ≤ M) :
    weight bornA (kgThermal kA kEnv) M * bornB =
      weight bornB (kgThermal kB kEnv) M * bornA := by
  have h := thermal_swamp kA kB kEnv hA hB
  simp [weight, h.1, h.2, Nat.mul_left_comm, Nat.mul_comm]

theorem thermal_le_additive (kReg kEnv : Nat) :
    kgThermal kReg kEnv ≤ kgAdditive kReg kEnv := by
  simp [kgThermal, kgAdditive]
  omega

/-- Isolated dump of length `n` has `K ≤ n+1`; a bath with `kEnv ≥ n+1`
swamps it. -/
theorem dump_swamped (n kEnv bornA bornB M : Nat)
    (hn : 1 ≤ n) (hL : n + 1 ≤ kEnv) (hM : kEnv ≤ M) :
    weight bornA (kgThermal shortK kEnv) M * bornB =
      weight bornB (kgThermal (n + 1) kEnv) M * bornA := by
  have hA : shortK ≤ kEnv := by
    simp [shortK]
    omega
  exact thermal_tracks_born shortK (n + 1) kEnv bornA bornB M hA hL hM

/-! ### Two-path merge -/

structure Path where
  born : Nat
  kReg : Nat
  kEnv : Nat

def Path.wIsolated (p : Path) (M : Nat) : Nat :=
  weight p.born (kgIsolated p.kReg) M

def Ziso (ps : List Path) (M : Nat) : Nat :=
  (ps.map (fun p => p.wIsolated M)).sum

theorem Ziso_nil (M : Nat) : Ziso [] M = 0 := rfl

theorem merge_well_defined (ps : List Path) (M : Nat) :
    ∃ n : Nat, Ziso ps M = n :=
  ⟨Ziso ps M, rfl⟩

/-- Equal-Born isolated dump of `n` bits versus a 2-bit constant:
the constant takes at least `2^{n-1}` relative Occam mass. -/
theorem isolated_dump_occam (n born M : Nat)
    (hn : 1 ≤ n) (hS : shortK ≤ M) (hD : n + 1 ≤ M) :
    weight born (n + 1) M * born * 2 ^ (n - 1) ≤
      weight born shortK M * born := by
  have hc : shortK + (n - 1) ≤ n + 1 := by
    simp [shortK]
    omega
  simpa using isolated_bias shortK (n + 1) (n - 1) born born M hc hS hD

end Lab
end K
