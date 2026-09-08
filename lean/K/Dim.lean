/-
3+1 dimensionality analog, matching `toy/dimension.py`.

A gravity plugin is a spacetime dimension `D`, Einstein–Hilbert and/or
Gauss–Bonnet, and compactification moduli.  Local graviton polarizations
are `D(D−3)/2`.  The `p`-th Lovelock density is zero for `D < 2p`,
topological at `D = 2p`, dynamical for `D > 2p`.  Plugins that do not
compress Cauchy data (zero local gravitons, or no dynamical term) pay
`I_dead`.  4d Einstein–Hilbert with no junk is the 2-bit vacuum.

Choquet–Bruhat well-posedness for `D ≥ 3` is an input, like the
GR-machine elsewhere.  What is proved is the compressor count the
Python analog uses.
-/

import K.Complexity
import Init.Omega

namespace K
namespace Dim

inductive LovelockStatus where
  | zero
  | topological
  | dynamical
  deriving DecidableEq, Repr

/-- Local graviton polarizations of GR in `D` spacetime dimensions.
`Nat` subtraction makes this `0` for `D ≤ 3`. -/
def dof (D : Nat) : Nat :=
  D * (D - 3) / 2

theorem dof_2 : dof 2 = 0 := by simp [dof]
theorem dof_3 : dof 3 = 0 := by simp [dof]
theorem dof_4 : dof 4 = 2 := by simp [dof]
theorem dof_5 : dof 5 = 5 := by simp [dof]
theorem dof_6 : dof 6 = 9 := by simp [dof]

/-- Status of the `p`-th Lovelock density in `D` dimensions. -/
def lovelockStatus (p D : Nat) : LovelockStatus :=
  if D < 2 * p then .zero
  else if D = 2 * p then .topological
  else .dynamical

theorem einstein_topological_2 : lovelockStatus 1 2 = .topological := by
  simp [lovelockStatus]

theorem einstein_dynamical_4 : lovelockStatus 1 4 = .dynamical := by
  simp [lovelockStatus]

theorem einstein_dynamical_3 : lovelockStatus 1 3 = .dynamical := by
  simp [lovelockStatus]

theorem gaussBonnet_zero_3 : lovelockStatus 2 3 = .zero := by
  simp [lovelockStatus]

theorem gaussBonnet_topological_4 : lovelockStatus 2 4 = .topological := by
  simp [lovelockStatus]

theorem gaussBonnet_dynamical_5 : lovelockStatus 2 5 = .dynamical := by
  simp [lovelockStatus]

/-! ### Plugins -/

structure Plugin where
  D : Nat
  hasEH : Bool
  hasGB : Bool
  moduli : Nat

def einstein4 : Plugin :=
  { D := 4, hasEH := true, hasGB := false, moduli := 0 }

def einstein3 : Plugin :=
  { D := 3, hasEH := true, hasGB := false, moduli := 0 }

def einstein5 : Plugin :=
  { D := 5, hasEH := true, hasGB := false, moduli := 0 }

def einstein5mod (m : Nat) : Plugin :=
  { D := 5, hasEH := true, hasGB := false, moduli := m }

def einstein4gb : Plugin :=
  { D := 4, hasEH := true, hasGB := true, moduli := 0 }

def nDyn (p : Plugin) : Nat :=
  (if p.hasEH = true ∧ lovelockStatus 1 p.D = .dynamical then 1 else 0)
    + (if p.hasGB = true ∧ lovelockStatus 2 p.D = .dynamical then 1 else 0)

def IsCompressor (p : Plugin) : Prop :=
  0 < dof p.D ∧ 0 < nDyn p

def iDead (p : Plugin) : Nat :=
  if 0 < dof p.D ∧ 0 < nDyn p then 0 else 1

/-- `|D − 4|`. -/
def dimPenalty (D : Nat) : Nat :=
  (D - 4) + (4 - D)

/-- 4d Einstein–Hilbert with no junk is the 2-bit vacuum. -/
def kData (p : Plugin) : Nat :=
  if p.D = 4 ∧ p.hasEH = true ∧ p.hasGB = false ∧ p.moduli = 0 then 2
  else
    2 + dimPenalty p.D + p.moduli
      + (if p.hasGB = true then 1 else 0)
      + (if p.hasEH = true then 0 else 2)

def kgHat (p : Plugin) (beta : Nat) : Nat :=
  kData p + beta * iDead p

def weight (born kg M : Nat) : Nat :=
  born * 2 ^ (M - kg)

/-! ### Vacuum, dead 2+1, extra-dimensional cost -/

theorem kData_einstein4 : kData einstein4 = 2 := by
  simp [kData, einstein4]

theorem nDyn_einstein4 : nDyn einstein4 = 1 := by
  simp [nDyn, einstein4, einstein_dynamical_4]

theorem iDead_einstein4 : iDead einstein4 = 0 := by
  have : 0 < dof einstein4.D ∧ 0 < nDyn einstein4 :=
    ⟨by simp [einstein4, dof_4], by simp [nDyn_einstein4]⟩
  simp [iDead, this]

theorem kgHat_einstein4 (beta : Nat) : kgHat einstein4 beta = 2 := by
  simp [kgHat, kData_einstein4, iDead_einstein4]

theorem einstein4_compressor : IsCompressor einstein4 :=
  ⟨by simp [einstein4, dof_4], by simp [nDyn_einstein4]⟩

theorem iDead_einstein3 : iDead einstein3 = 1 := by
  simp [iDead, einstein3, dof_3]

theorem kData_einstein3 : kData einstein3 = 3 := by
  simp [kData, einstein3, dimPenalty]

theorem kgHat_einstein3 (beta : Nat) :
    kgHat einstein3 beta = 3 + beta := by
  simp [kgHat, kData_einstein3, iDead_einstein3]

theorem kData_einstein4gb : kData einstein4gb = 3 := by
  simp [kData, einstein4gb, dimPenalty]

/-- Topological Gauss–Bonnet in 4d does not add a dynamical term. -/
theorem nDyn_einstein4gb : nDyn einstein4gb = 1 := by
  simp [nDyn, einstein4gb, einstein_dynamical_4, gaussBonnet_topological_4]

theorem iDead_einstein4gb : iDead einstein4gb = 0 := by
  have : 0 < dof einstein4gb.D ∧ 0 < nDyn einstein4gb :=
    ⟨by simp [einstein4gb, dof_4], by simp [nDyn_einstein4gb]⟩
  simp [iDead, this]

theorem kData_einstein5 : kData einstein5 = 3 := by
  simp [kData, einstein5, dimPenalty]

theorem kData_einstein5mod (m : Nat) :
    kData (einstein5mod m) = 3 + m := by
  simp [kData, einstein5mod, dimPenalty]

theorem nDyn_einstein5 : nDyn einstein5 = 1 := by
  simp [nDyn, einstein5, lovelockStatus]

theorem iDead_einstein5 : iDead einstein5 = 0 := by
  have : 0 < dof einstein5.D ∧ 0 < nDyn einstein5 :=
    ⟨by simp [einstein5, dof_5], by simp [nDyn_einstein5]⟩
  simp [iDead, this]

/-! ### Dominance of 4d Einstein–Hilbert -/

/-- 2+1 Einstein is dead as a compressor: it pays `β` plus a dimension bit. -/
theorem einstein4_dominates_3d
    (beta born M : Nat)
    (_hβ : 0 < beta) (hS : 2 ≤ M) (hD : 3 + beta ≤ M) :
    weight born (kgHat einstein3 beta) M * born * 2 ^ (1 + beta) ≤
      weight born (kgHat einstein4 beta) M * born := by
  have hP := kgHat_einstein4 beta
  have hR := kgHat_einstein3 beta
  rw [hP, hR]
  have hc : 2 + (1 + beta) ≤ 3 + beta := by omega
  exact weight_ratio hc hS hD

theorem nDyn_einstein5mod (m : Nat) : nDyn (einstein5mod m) = 1 := by
  simp [nDyn, einstein5mod, lovelockStatus]

theorem iDead_einstein5mod (m : Nat) : iDead (einstein5mod m) = 0 := by
  have : 0 < dof (einstein5mod m).D ∧ 0 < nDyn (einstein5mod m) :=
    ⟨by simp [einstein5mod, dof_5], by simp [nDyn_einstein5mod]⟩
  simp [iDead, this]

theorem kgHat_einstein5mod (m : Nat) :
    kgHat (einstein5mod m) 0 = 3 + m := by
  simp [kgHat, kData_einstein5mod, iDead_einstein5mod]

/-- A 5d Einstein plugin with a modulus pays `|5−4| + m` extra bits. -/
theorem einstein4_dominates_5d_mod
    (m born M : Nat)
    (_hm : 0 < m) (hS : 2 ≤ M) (hD : 3 + m ≤ M) :
    weight born (kgHat (einstein5mod m) 0) M * born * 2 ^ (1 + m) ≤
      weight born (kgHat einstein4 0) M * born := by
  have hP : kgHat einstein4 0 = 2 := kgHat_einstein4 0
  have hR : kgHat (einstein5mod m) 0 = 3 + m := kgHat_einstein5mod m
  rw [hP, hR]
  have hc : 2 + (1 + m) ≤ 3 + m := by omega
  exact weight_ratio hc hS hD

/-- Writing topological Gauss–Bonnet in 4d costs one extra bit. -/
theorem einstein4_dominates_gb
    (born M : Nat) (hS : 2 ≤ M) (hD : 3 ≤ M) :
    weight born (kgHat einstein4gb 0) M * born * 2 ≤
      weight born (kgHat einstein4 0) M * born := by
  have hP : kgHat einstein4 0 = 2 := kgHat_einstein4 0
  have hR : kgHat einstein4gb 0 = 3 := by
    simp [kgHat, kData_einstein4gb, iDead_einstein4gb]
  rw [hP, hR]
  exact weight_ratio (by omega : 2 + 1 ≤ 3) hS hD

/-! ### Merge -/

structure Universe where
  plugin : Plugin
  born : Nat
  beta : Nat

def Universe.kg (u : Universe) : Nat :=
  kgHat u.plugin u.beta

def Universe.w (u : Universe) (M : Nat) : Nat :=
  weight u.born u.kg M

def Z (us : List Universe) (M : Nat) : Nat :=
  (us.map (fun u => u.w M)).sum

theorem Z_nil (M : Nat) : Z [] M = 0 := rfl

theorem merge_well_defined (us : List Universe) (M : Nat) :
    ∃ n : Nat, Z us M = n :=
  ⟨Z us M, rfl⟩

theorem cycle_index (us : List Universe) :
    (us.map Universe.plugin).length = us.length := by
  simp

end Dim
end K
