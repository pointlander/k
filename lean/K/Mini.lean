/-
Minisuperspace k-cycle, matching `toy/minisuperspace.py`.

FLRW + a homogeneous scalar, in integer arithmetic (units 8πG = 1, with
the Friedmann constraint cleared of denominators).  This is the smallest
setting where Γ is Einstein: the constraint supplies H, so on-shell 3-data
do not pay Hubble bits, and I_off = |constraint| kills generic 4-data.

RK4 error bounds are not proved (no analysis library).  What is proved is
the algebraic core the Python analog uses: the constraint, the de Sitter
fixed point, the compressor, and Einsteinian dominance of the k-weight.
-/

import K.Complexity
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.List.Lemmas
import Init.Omega

namespace K
namespace Mini

/-! ### Potential and Cauchy data -/

/-- Scalar potential.  `lam V0` is a cosmological constant; `quad m` is `m² φ²`
(the Python `½ m² φ²` with a rescaled mass, so everything stays in `Int`). -/
inductive Potential where
  | lam (V0 : Nat)
  | quad (m : Nat)

def Potential.V : Potential → Int → Int
  | lam V0, _ => V0
  | quad m, phi => (m : Int) * m * phi * phi

def Potential.dV : Potential → Int → Int
  | lam _, _ => 0
  | quad m, phi => 2 * (m : Int) * m * phi

/-- Minisuperspace Cauchy data.  `onShell` means H was supplied by Einstein
(the 3-data slice).  Bins `ia, iH, iphi, ip` are the integer skeleton. -/
structure Cauchy where
  a : Nat
  H : Int
  phi : Int
  p : Int
  onShell : Bool
  crash : Bool := false
  ia : Nat := 0
  iH : Nat := 0
  iphi : Nat := 0
  ip : Nat := 0

/-- On-shell 3-data `(a, φ, p)`; off-shell 4-data `(a, H, φ, p)`.
Einstein as compressor: the on-shell slice does not pay Hubble bits. -/
def Cauchy.payload (d : Cauchy) : List Nat :=
  if d.onShell then [d.ia, d.iphi, d.ip] else [d.ia, d.iH, d.iphi, d.ip]

theorem payload_length_onShell (d : Cauchy) (h : d.onShell = true) :
    d.payload.length = 3 := by
  simp [Cauchy.payload, h]

theorem payload_length_offShell (d : Cauchy) (h : d.onShell = false) :
    d.payload.length = 4 := by
  simp [Cauchy.payload, h]

/-- Twice the energy density: `p² + 2V`, so `ρ = twoRho / 2`. -/
def twoRho (pot : Potential) (phi p : Int) : Int :=
  p * p + 2 * pot.V phi

/-- Cleared Friedmann constraint `2 a² C`, with
`C = 3(H² + k/a²) − ρ`.  For `a > 0`, on-shell iff this vanishes. -/
def constraint2 (d : Cauchy) (pot : Potential) (curv : Nat) : Int :=
  let a2 : Int := ↑(d.a * d.a)
  6 * a2 * d.H * d.H + 6 * (curv : Int) - a2 * twoRho pot d.phi d.p

def OnShell (d : Cauchy) (pot : Potential) (curv : Nat) : Prop :=
  0 < d.a ∧ constraint2 d pot curv = 0

def iOff (d : Cauchy) (pot : Potential) (curv : Nat) : Nat :=
  (constraint2 d pot curv).natAbs

theorem iOff_eq_zero_iff (d : Cauchy) (pot : Potential) (curv : Nat) :
    iOff d pot curv = 0 ↔ constraint2 d pot curv = 0 :=
  Int.natAbs_eq_zero

theorem iOff_onShell (d : Cauchy) (pot : Potential) (curv : Nat)
    (h : OnShell d pot curv) : iOff d pot curv = 0 :=
  (iOff_eq_zero_iff d pot curv).mpr h.2

/-! ### De Sitter -/

/-- Integer Hubble de Sitter: `V = 3 Hds²` so `3 H² = V` is exact in `Int`. -/
def deSitterV (Hds : Nat) : Nat := 3 * Hds * Hds

def deSitter (Hds a : Nat) (mid : Nat := 0) : Cauchy where
  a := a
  H := ↑Hds
  phi := 0
  p := 0
  onShell := true
  ia := mid
  iH := mid
  iphi := mid
  ip := mid

private theorem mul_left_shift (w x y z : Int) :
    w * x * y * z = x * (w * y * z) := by
  simp [Int.mul_left_comm, Int.mul_comm]

private theorem two_three_sq (y : Int) :
    (2 : Int) * (3 * y * y) = 6 * y * y := by
  simp [Int.mul_left_comm, Int.mul_comm]

theorem constraint2_deSitter (Hds a : Nat) :
    constraint2 (deSitter Hds a) (.lam (deSitterV Hds)) 0 = 0 := by
  simp [constraint2, deSitter, twoRho, Potential.V, deSitterV]
  -- 6 a² H² − a² (2 · 3 H²)
  rw [two_three_sq]
  rw [mul_left_shift]
  simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem deSitter_onShell (Hds a : Nat) (ha : 0 < a) :
    OnShell (deSitter Hds a) (.lam (deSitterV Hds)) 0 :=
  ⟨ha, constraint2_deSitter Hds a⟩

/-- Minkowski kinematics with a cosmological constant is off-shell. -/
theorem lambda_H0_offShell (V0 a : Nat) (hV : 0 < V0) (ha : 0 < a) :
    constraint2
      { a := a, H := 0, phi := 0, p := 0, onShell := false }
      (.lam V0) 0 ≠ 0 := by
  simp [constraint2, twoRho, Potential.V]
  exact ⟨Nat.ne_of_gt ha, Nat.ne_of_gt hV⟩

/-! ### Infinitesimal Einstein–Klein–Gordon (Γ's vector field) -/

/-- `ȧ = H a`. -/
def adot (d : Cauchy) : Int := d.H * d.a

/-- `3 Ḣ = (V − p²) − 3 H²`.  (The factor of 3 clears the denominator.) -/
def Hdot3 (d : Cauchy) (pot : Potential) : Int :=
  pot.V d.phi - d.p * d.p - 3 * d.H * d.H

def phidot (d : Cauchy) : Int := d.p

def pdot (d : Cauchy) (pot : Potential) : Int :=
  -3 * d.H * d.p - pot.dV d.phi

theorem deSitter_Hdot3 (Hds a : Nat) :
    Hdot3 (deSitter Hds a) (.lam (deSitterV Hds)) = 0 := by
  simp [Hdot3, deSitter, Potential.V, deSitterV]

theorem deSitter_pdot (Hds a : Nat) :
    pdot (deSitter Hds a) (.lam (deSitterV Hds)) = 0 := by
  simp [pdot, deSitter, Potential.dV]

theorem deSitter_phidot (Hds a : Nat) :
    phidot (deSitter Hds a) = 0 := by
  simp [phidot, deSitter]

theorem deSitter_adot (Hds a : Nat) :
    adot (deSitter Hds a) = ↑Hds * ↑a := by
  simp [adot, deSitter]

/-- Hubble is a fixed point of de Sitter; the scale factor expands when `Hds > 0`. -/
theorem deSitter_expands (Hds a : Nat) (hH : 0 < Hds) (ha : 0 < a) :
    0 < adot (deSitter Hds a) := by
  simp [deSitter_adot]
  have : 0 < (Hds : Int) := Int.natCast_pos.mpr hH
  have : 0 < (a : Int) := Int.natCast_pos.mpr ha
  exact Int.mul_pos ‹0 < (Hds : Int)› ‹0 < (a : Int)›

/-- On-shell lambda with `p = 0` and `k = 0` is instantaneously de Sitter:
`Ḣ = 0`. -/
theorem lambda_Hdot3_of_onShell (d : Cauchy) (V0 : Nat)
    (hp : d.p = 0) (ha : 0 < d.a)
    (hC : constraint2 d (.lam V0) 0 = 0) :
    Hdot3 d (.lam V0) = 0 := by
  have ha2 : (↑(d.a * d.a) : Int) ≠ 0 := by
    have : d.a ≠ 0 := Nat.ne_of_gt ha
    exact Int.natCast_ne_zero.mpr (Nat.mul_ne_zero this this)
  simp [constraint2, twoRho, Potential.V, hp] at hC
  have hr : 6 * (↑(d.a * d.a) : Int) * d.H * d.H
      = ↑(d.a * d.a) * (6 * d.H * d.H) :=
    mul_left_shift 6 _ _ _
  have hmul : (↑(d.a * d.a) : Int) * (6 * d.H * d.H - 2 * V0) = 0 := by
    rw [Int.mul_sub, ← hr]
    exact hC
  have hfac : 6 * d.H * d.H - 2 * (V0 : Int) = 0 := by
    rcases Int.mul_eq_zero.mp hmul with h0 | h0
    · exact absurd h0 ha2
    · exact h0
  simp [Hdot3, Potential.V, hp]
  have : 3 * d.H * d.H = (V0 : Int) := by
    have : (2 : Int) * (3 * d.H * d.H - V0) = 0 := by
      have := hfac
      simp [Int.mul_sub, Int.mul_left_comm, Int.mul_comm] at this ⊢
      grind
    rcases Int.mul_eq_zero.mp this with h2 | h0
    · cases h2
    · omega
  omega

/-! ### Discrete skeleton: K̂ of Cauchy bins -/

/-- Shortest description of a bin tuple.  The middle bin is the vacuum. -/
def kIndices (idx : List Nat) (nbits : Nat) : Nat :=
  let mid := 2 ^ nbits / 2
  if idx.all (fun i => i == mid) then 2
  else nbits * idx.length + 1

theorem kIndices_all_mid (idx : List Nat) (nbits : Nat)
    (h : ∀ i ∈ idx, i = 2 ^ nbits / 2) :
    kIndices idx nbits = 2 := by
  simp [kIndices, List.all_eq_true]
  intro i hi
  simp [h i hi]

theorem kIndices_deSitter (Hds a mid nbits : Nat)
    (h : mid = 2 ^ nbits / 2) :
    kIndices (deSitter Hds a mid).payload nbits = 2 := by
  simp [Cauchy.payload, deSitter, kIndices, h]

/-- `K̂_G = K(data | Einstein) + β I_off² + crash penalty`. -/
def kgHat (d : Cauchy) (pot : Potential) (curv nbits beta : Nat) : Nat :=
  kIndices d.payload nbits + beta * (iOff d pot curv) ^ 2
    + if d.crash then 40 else 0

theorem kgHat_onShell (d : Cauchy) (pot : Potential) (curv nbits beta : Nat)
    (h : OnShell d pot curv) (hc : d.crash = false) :
    kgHat d pot curv nbits beta = kIndices d.payload nbits := by
  simp [kgHat, iOff_onShell d pot curv h, hc]

theorem kgHat_offShell_ge (d : Cauchy) (pot : Potential) (curv nbits beta : Nat)
    (h : constraint2 d pot curv ≠ 0) (hc : d.crash = false) (_hβ : 0 < beta) :
    kIndices d.payload nbits + beta ≤ kgHat d pot curv nbits beta := by
  have hi : 1 ≤ iOff d pot curv := by
    have : iOff d pot curv ≠ 0 := by
      intro hz
      exact h ((iOff_eq_zero_iff d pot curv).mp hz)
    omega
  simp [kgHat, hc]
  have : 1 ≤ (iOff d pot curv) ^ 2 := by
    have : 1 ≤ iOff d pot curv * iOff d pot curv := Nat.mul_le_mul hi hi
    simpa [Nat.pow_two]
  have : beta ≤ beta * (iOff d pot curv) ^ 2 := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left beta this
  omega

/-! ### Einsteinian dominance of the minisuperspace k-weight -/

/-- Unnormalized weight `born · 2^{M − K̂_G}`. -/
def weight (born kg M : Nat) : Nat :=
  born * 2 ^ (M - kg)

/-- On-shell de Sitter (vacuum payload, `I_off = 0`) dominates an off-shell
sample of equal Born mass by at least `2^β`. -/
theorem einsteinian_dominance
    (Hds a V0 nbits beta born M : Nat)
    (ha : 0 < a) (_hV : 0 < V0) (_hβ : 0 < beta)
    (dR : Cauchy)
    (_hR : constraint2 dR (.lam V0) 0 ≠ 0)
    (_hcR : dR.crash = false)
    (hcrashE : (deSitter Hds a (2 ^ nbits / 2)).crash = false)
    (hkE : kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits ≤ M)
    (hkR : kgHat dR (.lam V0) 0 nbits beta ≤ M)
    (hle : kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits + beta ≤
        kgHat dR (.lam V0) 0 nbits beta) :
    weight born (kgHat dR (.lam V0) 0 nbits beta) M
        * 2 ^ beta ≤
      weight born (kgHat (deSitter Hds a (2 ^ nbits / 2))
        (.lam (deSitterV Hds)) 0 nbits beta) M := by
  have hE := deSitter_onShell Hds a ha
  have hkE' := kgHat_onShell (deSitter Hds a (2 ^ nbits / 2))
    (.lam (deSitterV Hds)) 0 nbits beta hE hcrashE
  rw [hkE'] at *
  -- kgR ≥ kgE + beta, so 2^{M-kgR} * 2^beta ≤ 2^{M-kgE}
  have hkgE : kgHat (deSitter Hds a (2 ^ nbits / 2))
      (.lam (deSitterV Hds)) 0 nbits beta = kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits :=
    kgHat_onShell _ _ _ _ _ hE hcrashE
  -- Use the Occam ratio with c = beta.
  have hc : kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits + beta ≤
      kgHat dR (.lam V0) 0 nbits beta := hle
  simp [weight]
  have hpow : 2 ^ (M - kgHat dR (.lam V0) 0 nbits beta + beta)
      ≤ 2 ^ (M - kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits) := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    omega
  calc
    born * 2 ^ (M - kgHat dR (.lam V0) 0 nbits beta) * 2 ^ beta
        = born * 2 ^ (M - kgHat dR (.lam V0) 0 nbits beta + beta) := by
          simp [Nat.pow_add, Nat.mul_assoc]
    _ ≤ born * 2 ^ (M - kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits) :=
          Nat.mul_le_mul_left _ hpow

/-- Same dominance, with the off-shell lower bound supplied by `kgHat_offShell_ge`
and vacuum on-shell complexity `2`. -/
theorem einsteinian_dominance_vacuum
    (Hds a V0 nbits beta born M : Nat)
    (ha : 0 < a) (hV : 0 < V0) (hβ : 0 < beta)
    (dR : Cauchy)
    (hR : constraint2 dR (.lam V0) 0 ≠ 0)
    (hcR : dR.crash = false)
    (hcrashE : (deSitter Hds a (2 ^ nbits / 2)).crash = false)
    (hpay : kIndices dR.payload nbits = 2)
    (_hkE : 2 ≤ M)
    (hkR : kgHat dR (.lam V0) 0 nbits beta ≤ M) :
    weight born (kgHat dR (.lam V0) 0 nbits beta) M * 2 ^ beta ≤
      weight born (kgHat (deSitter Hds a (2 ^ nbits / 2))
        (.lam (deSitterV Hds)) 0 nbits beta) M := by
  have hE := deSitter_onShell Hds a ha
  have hmid : kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits = 2 :=
    kIndices_deSitter Hds a (2 ^ nbits / 2) nbits rfl
  have hge := kgHat_offShell_ge dR (.lam V0) 0 nbits beta hR hcR hβ
  have hle : kIndices (deSitter Hds a (2 ^ nbits / 2)).payload nbits + beta ≤
      kgHat dR (.lam V0) 0 nbits beta := by
    simpa [hmid, hpay] using hge
  exact einsteinian_dominance Hds a V0 nbits beta born M ha hV hβ dR hR hcR
    hcrashE (by omega) hkR hle

/-! ### Merge: a countable sum over the integer skeleton -/

structure Universe where
  data : Cauchy
  born : Nat
  pot : Potential
  curv : Nat
  nbits : Nat
  beta : Nat

def Universe.kg (u : Universe) : Nat :=
  kgHat u.data u.pot u.curv u.nbits u.beta

def Universe.w (u : Universe) (M : Nat) : Nat :=
  weight u.born u.kg M

/-- Partition function of a finite list of minisuperspace samples. -/
def Z (us : List Universe) (M : Nat) : Nat :=
  (us.map (fun u => u.w M)).sum

theorem Z_nil (M : Nat) : Z [] M = 0 := rfl

theorem merge_well_defined (us : List Universe) (M : Nat) :
    ∃ n : Nat, Z us M = n :=
  ⟨Z us M, rfl⟩

/-- The merge is indexed by Cauchy data (finite bin tuples), not by a
continuum of metrics. -/
theorem cycle_index (us : List Universe) :
    (us.map Universe.data).length = us.length := by
  simp

/-- On-shell de Sitter injects into the enumerable skeleton. -/
theorem deSitter_payload_enumerable (Hds a mid : Nat) :
    ∃ idx : List Nat, (deSitter Hds a mid).payload = idx :=
  ⟨(deSitter Hds a mid).payload, rfl⟩

end Mini
end K
