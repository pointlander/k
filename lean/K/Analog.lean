/-
Discrete analog of the k-cycle, matching `toy/k_merge.py`.

A bitstring is a classical spin configuration on a cycle.  `E_smooth` is a
discrete curvature.  Constant configurations (the Einstein analog) achieve
the global minimum `E_smooth = 0`.
-/

import K.Bitstring
import Init.Data.List.Lemmas
import Init.Omega

namespace K

open Bitstring List

/-- Number of consecutive bit flips, not wrapping around. -/
def lineFlips : Bitstring → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if a = b then 0 else 1) + lineFlips (b :: rest)

/-- Wrap-around flip of a cycle.  Empty and singleton cycles contribute 0. -/
def wrapFlip : Bitstring → Nat
  | [] => 0
  | [_] => 0
  | x :: xs => if xs.getLast? = some x then 0 else 1

/-- Discrete curvature: bit flips around the cycle.  Analog of `I_off`. -/
def E_smooth (s : Bitstring) : Nat :=
  lineFlips s + wrapFlip s

@[simp] theorem E_smooth_nil : E_smooth [] = 0 := rfl

@[simp] theorem E_smooth_singleton (b : Bool) : E_smooth [b] = 0 := rfl

theorem lineFlips_replicate (b : Bool) : ∀ n, lineFlips (List.replicate n b) = 0
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [List.replicate_succ, List.replicate_succ]
      simp [lineFlips]
      exact lineFlips_replicate b (n + 1)

theorem wrapFlip_replicate (b : Bool) : ∀ n, wrapFlip (List.replicate n b) = 0
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [List.replicate_succ]
      simp [wrapFlip, List.getLast?_replicate]

/-- Constant configurations have zero curvature.  These are the Einstein analog. -/
theorem E_smooth_replicate (b : Bool) (n : Nat) :
    E_smooth (List.replicate n b) = 0 := by
  simp [E_smooth, lineFlips_replicate, wrapFlip_replicate]

/-- Einstein analog: a constant configuration achieves the global minimum of
discrete curvature. -/
theorem einstein_minimizes (b : Bool) (n : Nat) (s : Bitstring) :
    E_smooth (List.replicate n b) ≤ E_smooth s := by
  rw [E_smooth_replicate]
  exact Nat.zero_le _

/-- Analog of gravitational Kolmogorov complexity: a 2-bit description for
constants, otherwise the raw length, plus a curvature penalty. -/
def Khat (beta : Nat) (s : Bitstring) : Nat :=
  (if s.all (fun x => x == s.headD false) then 2 else s.length + 1)
    + beta * E_smooth s

theorem all_replicate (b : Bool) : ∀ n,
    (List.replicate n b).all (fun x => x == b) = true
  | 0 => rfl
  | n + 1 => by
      simp [List.replicate, all_replicate b n]

theorem Khat_replicate (beta : Nat) (b : Bool) (n : Nat) :
    Khat beta (List.replicate n b) = 2 := by
  unfold Khat
  rw [E_smooth_replicate]
  cases n with
  | zero => simp
  | succ n =>
      simp [List.headD, List.replicate, all_replicate b n]

/-- Zero-curvature (Einstein) samples have analog complexity 2.  A sample
that is not constant, of length at least 2, has complexity at least 3. -/
theorem analog_dominance (beta : Nat) (b : Bool) {sR : Bitstring}
    (hR : sR.all (fun x => x == sR.headD false) = false)
    (hn : 2 ≤ sR.length) :
    Khat beta (List.replicate sR.length b) + 1 ≤ Khat beta sR := by
  rw [Khat_replicate]
  have helse :
      (if sR.all (fun x => x == sR.headD false) then 2 else sR.length + 1) = sR.length + 1 := by
    cases h : sR.all (fun x => x == sR.headD false)
    · rfl
    · rw [h] at hR
      contradiction
  unfold Khat
  rw [helse]
  have h3 : 3 ≤ sR.length + 1 := by omega
  exact Nat.le_trans h3 (Nat.le_add_right _ _)

end K
