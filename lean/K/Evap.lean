/-
1+1 evaporation k-cycle, matching `toy/evaporation.py`.

Discrete Vaidya: one Planck unit of Bondi mass becomes outgoing flux per
tick.  On-shell, Einstein supplies the remaining mass (`m + t = N`).
Holography of the leftover hole: at most `m` independent bits fit in
remaining area `m` (units `4ℓ_P² = 1`).  Three families:

* `page` — radiation is a function of the microstate; leftover bits `= m`;
  `K̂_G` stays `K(s)`.
* `remnant` — all `N` bits stay inside as `m` drops; `I_H = t`.
* `scramble` — independent radiation of length `t`, interior still holds
  `s`; pays `t` extra bits and `I_H = t`.

RK4/continuum error bounds are not proved.  What is proved is the
algebraic core the Python analog uses: the Bondi constraint, the area
bound, constant Page complexity, and dominance of the Page family.
-/

import K.Kraft
import Init.Omega

namespace K
namespace Evap

open Bitstring

/-! ### Families and Cauchy data -/

inductive Family where
  | page
  | remnant
  | scramble
  deriving DecidableEq, Repr

/-- Evaporation Cauchy data at retarded time `t`.  `kS` is a computable
upper bound on `K` of the initial `N`-bit microstate. -/
structure Slice where
  N : Nat
  t : Nat
  m : Nat
  onShell : Bool
  family : Family
  kS : Nat
  crash : Bool := false

/-- Independent bits charged to the remaining hole. -/
def storedInHole (d : Slice) : Nat :=
  match d.family with
  | .page => d.N - d.t
  | .remnant => d.N
  | .scramble => d.N

/-- Bondi constraint `|m + t − N|`.  Vanishes on a Vaidya history. -/
def iEnergy (d : Slice) : Nat :=
  (d.m + d.t) - d.N + (d.N - (d.m + d.t))

/-- Holographic leftover: bits in the hole minus remaining area. -/
def iHolo (d : Slice) : Nat :=
  storedInHole d - d.m

/-- `K(data | Einstein)`.  On-shell, Einstein supplies `m`. -/
def kData (d : Slice) : Nat :=
  match d.family with
  | .page => d.kS
  | .remnant => d.kS
  | .scramble => d.kS + d.t

/-- `K̂_G = K(data | Einstein) + β I_E² + β I_H² + crash penalty`. -/
def kgHat (d : Slice) (beta : Nat) : Nat :=
  kData d + beta * (iEnergy d) ^ 2 + beta * (iHolo d) ^ 2
    + if d.crash then 40 else 0

def page (N t kS : Nat) : Slice where
  N := N
  t := t
  m := N - t
  onShell := true
  family := .page
  kS := kS

def remnant (N t kS : Nat) : Slice where
  N := N
  t := t
  m := N - t
  onShell := true
  family := .remnant
  kS := kS

def scramble (N t kS : Nat) : Slice where
  N := N
  t := t
  m := N - t
  onShell := true
  family := .scramble
  kS := kS

/-! ### Bondi constraint -/

theorem iEnergy_eq_zero_iff (d : Slice) :
    iEnergy d = 0 ↔ d.m + d.t = d.N := by
  simp [iEnergy]
  omega

theorem iEnergy_onShell (N t kS : Nat) (ht : t ≤ N) :
    iEnergy (page N t kS) = 0 ∧
      iEnergy (remnant N t kS) = 0 ∧
        iEnergy (scramble N t kS) = 0 := by
  simp [iEnergy, page, remnant, scramble]
  omega

theorem offShell_energy (d : Slice) (h : d.m + d.t ≠ d.N) :
    iEnergy d ≠ 0 :=
  fun hz => h ((iEnergy_eq_zero_iff d).mp hz)

/-! ### Holography of the leftover hole -/

theorem stored_page (N t kS : Nat) :
    storedInHole (page N t kS) = N - t := rfl

theorem stored_remnant (N t kS : Nat) :
    storedInHole (remnant N t kS) = N := rfl

theorem stored_scramble (N t kS : Nat) :
    storedInHole (scramble N t kS) = N := rfl

theorem iHolo_page (N t kS : Nat) (_ht : t ≤ N) :
    iHolo (page N t kS) = 0 := by
  simp [iHolo, storedInHole, page]

theorem iHolo_remnant (N t kS : Nat) (ht : t ≤ N) :
    iHolo (remnant N t kS) = t := by
  simp [iHolo, storedInHole, remnant]
  omega

theorem iHolo_scramble (N t kS : Nat) (ht : t ≤ N) :
    iHolo (scramble N t kS) = t := by
  simp [iHolo, storedInHole, scramble]
  omega

/-! ### `K̂_G` of the three families -/

theorem kgHat_page (N t kS beta : Nat) (ht : t ≤ N) :
    kgHat (page N t kS) beta = kS := by
  have hE := (iEnergy_onShell N t kS ht).1
  have hH := iHolo_page N t kS ht
  rw [kgHat, hE, hH]
  simp [kData, page]

/-- Dynamical holography: Page `K̂_G` of hole+radiation does not grow. -/
theorem kgHat_page_const (N t₁ t₂ kS beta : Nat)
    (h₁ : t₁ ≤ N) (h₂ : t₂ ≤ N) :
    kgHat (page N t₁ kS) beta = kgHat (page N t₂ kS) beta := by
  rw [kgHat_page N t₁ kS beta h₁, kgHat_page N t₂ kS beta h₂]

theorem kgHat_remnant (N t kS beta : Nat) (ht : t ≤ N) :
    kgHat (remnant N t kS) beta = kS + beta * t ^ 2 := by
  have hE := (iEnergy_onShell N t kS ht).2.1
  have hH := iHolo_remnant N t kS ht
  rw [kgHat, hE, hH]
  simp [kData, remnant]

theorem kgHat_scramble (N t kS beta : Nat) (ht : t ≤ N) :
    kgHat (scramble N t kS) beta = kS + t + beta * t ^ 2 := by
  have hE := (iEnergy_onShell N t kS ht).2.2
  have hH := iHolo_scramble N t kS ht
  rw [kgHat, hE, hH]
  simp [kData, scramble]

theorem remnant_pays (N t kS beta : Nat) (ht : t ≤ N) :
    kgHat (page N t kS) beta + beta * t ^ 2 =
      kgHat (remnant N t kS) beta := by
  rw [kgHat_page N t kS beta ht, kgHat_remnant N t kS beta ht]

theorem scramble_pays (N t kS beta : Nat) (ht : t ≤ N) :
    kgHat (page N t kS) beta + t + beta * t ^ 2 =
      kgHat (scramble N t kS) beta := by
  rw [kgHat_page N t kS beta ht, kgHat_scramble N t kS beta ht]

/-! ### Discrete Vaidya Γ -/

/-- One tick of constant 1+1 luminosity. -/
def step (d : Slice) : Slice :=
  { d with t := d.t + 1, m := if d.onShell then d.N - (d.t + 1) else d.m }

theorem step_page (N t kS : Nat) (_ht : t + 1 ≤ N) :
    step (page N t kS) = page N (t + 1) kS := by
  simp [step, page]

theorem step_page_onShell (N t kS : Nat) (ht : t + 1 ≤ N) :
    iEnergy (step (page N t kS)) = 0 ∧
      iHolo (step (page N t kS)) = 0 := by
  rw [step_page N t kS ht]
  exact ⟨(iEnergy_onShell N (t + 1) kS ht).1, iHolo_page N (t + 1) kS ht⟩

/-! ### Holographic bound on microstates and radiation -/

/-- At most `2^A` microstates of a hole of area `A`. -/
theorem hole_microstates (ps : List Bitstring) (A : Nat)
    (hnd : ps.Nodup) (hlen : ∀ p ∈ ps, p.length = A) :
    ps.length ≤ 2 ^ A :=
  holographic_bound ps A hnd hlen

/-- Radiation as a prefix-free family occupies at most the tree of depth `A`. -/
theorem radiation_kraft (ps : List Bitstring) (A : Nat)
    (h : PrefixFree ps) :
    kraftSum ps A ≤ 2 ^ A :=
  kraft_le ps A h

/-! ### Page dominance of the k-weight -/

def weight (born kg M : Nat) : Nat :=
  born * 2 ^ (M - kg)

/-- On-shell Page dominates an on-shell remnant of equal Born mass by
`2^{β t²}`. -/
theorem page_dominates_remnant
    (N t kS beta born M : Nat)
    (ht : t ≤ N) (_hβ : 0 < beta)
    (hkE : kS ≤ M)
    (hkR : kS + beta * t ^ 2 ≤ M) :
    weight born (kgHat (remnant N t kS) beta) M
        * 2 ^ (beta * t ^ 2) ≤
      weight born (kgHat (page N t kS) beta) M := by
  have hP := kgHat_page N t kS beta ht
  have hR := kgHat_remnant N t kS beta ht
  rw [hP, hR]
  simp [weight]
  have hpow : 2 ^ (M - (kS + beta * t ^ 2) + beta * t ^ 2) ≤ 2 ^ (M - kS) := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    omega
  calc
    born * 2 ^ (M - (kS + beta * t ^ 2)) * 2 ^ (beta * t ^ 2)
        = born * 2 ^ (M - (kS + beta * t ^ 2) + beta * t ^ 2) := by
          simp [Nat.pow_add, Nat.mul_assoc]
    _ ≤ born * 2 ^ (M - kS) :=
          Nat.mul_le_mul_left _ hpow

/-- On-shell Page dominates scramble by at least the remnant factor. -/
theorem page_dominates_scramble
    (N t kS beta born M : Nat)
    (ht : t ≤ N) (_hβ : 0 < beta)
    (hkE : kS ≤ M)
    (hkR : kS + t + beta * t ^ 2 ≤ M) :
    weight born (kgHat (scramble N t kS) beta) M
        * 2 ^ (beta * t ^ 2) ≤
      weight born (kgHat (page N t kS) beta) M := by
  have hP := kgHat_page N t kS beta ht
  have hS := kgHat_scramble N t kS beta ht
  rw [hP, hS]
  simp [weight]
  have hle : M - (kS + t + beta * t ^ 2) + beta * t ^ 2 ≤ M - kS := by omega
  have hpow : 2 ^ (M - (kS + t + beta * t ^ 2) + beta * t ^ 2) ≤ 2 ^ (M - kS) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  calc
    born * 2 ^ (M - (kS + t + beta * t ^ 2)) * 2 ^ (beta * t ^ 2)
        = born * 2 ^ (M - (kS + t + beta * t ^ 2) + beta * t ^ 2) := by
          simp [Nat.pow_add, Nat.mul_assoc]
    _ ≤ born * 2 ^ (M - kS) :=
          Nat.mul_le_mul_left _ hpow

/-! ### Merge: a countable sum over the integer skeleton -/

structure Universe where
  data : Slice
  born : Nat
  beta : Nat

def Universe.kg (u : Universe) : Nat :=
  kgHat u.data u.beta

def Universe.w (u : Universe) (M : Nat) : Nat :=
  weight u.born u.kg M

def Z (us : List Universe) (M : Nat) : Nat :=
  (us.map (fun u => u.w M)).sum

theorem Z_nil (M : Nat) : Z [] M = 0 := rfl

theorem merge_well_defined (us : List Universe) (M : Nat) :
    ∃ n : Nat, Z us M = n :=
  ⟨Z us M, rfl⟩

/-- The merge is indexed by finite slices, not by a continuum of metrics. -/
theorem cycle_index (us : List Universe) :
    (us.map Universe.data).length = us.length := by
  simp

/-- Schwarzschild analog: a constant microstate is the 2-bit vacuum program. -/
def schwarzschildK : Nat := 2

theorem schwarzschild_page (N t beta : Nat) (ht : t ≤ N) :
    kgHat (page N t schwarzschildK) beta = 2 :=
  kgHat_page N t schwarzschildK beta ht

end Evap
end K
