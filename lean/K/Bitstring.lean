/-
The integer skeleton of k: finite binary strings `{0,1}*`.
-/

import Init.Data.List.Lemmas
import Init.Data.List.Sublist
import Init.Data.List.Pairwise
import Init.Data.Nat.Lemmas
import Init.Omega

namespace K

/-- Finite binary strings: Cauchy data, programs, QFT skeleton labels. -/
abbrev Bitstring := List Bool

namespace Bitstring

/-- A list of strings is prefix-free when no member is a prefix of a different member. -/
def PrefixFree (ps : List Bitstring) : Prop :=
  ps.Nodup ∧ ∀ p ∈ ps, ∀ q ∈ ps, p <+: q → p = q

@[simp] theorem prefix_refl (p : Bitstring) : p <+: p := List.prefix_rfl

theorem prefix_trans {p q r : Bitstring} (hpq : p <+: q) (hqr : q <+: r) : p <+: r :=
  hpq.trans hqr

/-- The empty string is a prefix of every string. -/
theorem nil_prefix (p : Bitstring) : ([] : Bitstring) <+: p := List.nil_prefix

/-- In a prefix-free list, the empty program crowds out every other program. -/
theorem prefixFree_nil_mem {ps : List Bitstring} (h : PrefixFree ps)
    (hmem : [] ∈ ps) : ∀ q ∈ ps, q = [] := by
  intro q hq
  exact (h.2 [] hmem q hq (nil_prefix q)).symm

theorem eq_singleton_of_all_eq_nil {ps : List Bitstring}
    (hnodup : ps.Nodup) (hmem : [] ∈ ps)
    (hall : ∀ q ∈ ps, q = []) : ps = [[]] := by
  match ps with
  | [] =>
    cases hmem
  | p :: t =>
    have hp : p = [] := hall p (List.mem_cons_self)
    match t with
    | [] =>
      subst hp
      rfl
    | q :: u =>
      have hq : q = [] := hall q (List.mem_cons_of_mem _ List.mem_cons_self)
      subst hp
      subst hq
      have hmem' : ([] : Bitstring) ∈ [] :: u := List.mem_cons_self
      have hnd := (List.nodup_cons.mp hnodup).1
      exact (hnd hmem').elim

theorem prefixFree_of_nil_mem {ps : List Bitstring} (h : PrefixFree ps)
    (hmem : [] ∈ ps) : ps = [[]] :=
  eq_singleton_of_all_eq_nil h.1 hmem (prefixFree_nil_mem h hmem)

/-- Number of length-`N` extensions of `p` (leaves of the binary tree under `p`). -/
def leafCount (p : Bitstring) (N : Nat) : Nat :=
  if p.length ≤ N then 2 ^ (N - p.length) else 0

theorem leafCount_of_length_le {p : Bitstring} {N : Nat}
    (h : p.length ≤ N) : leafCount p N = 2 ^ (N - p.length) := by
  simp [leafCount, h]

theorem leafCount_of_length_gt {p : Bitstring} {N : Nat}
    (h : N < p.length) : leafCount p N = 0 := by
  simp [leafCount, Nat.not_le.mpr h]

theorem leafCount_cons (b : Bool) (t : Bitstring) (N : Nat) :
    leafCount (b :: t) (N + 1) = leafCount t N := by
  unfold leafCount
  simp only [List.length_cons]
  split <;> split <;> first | omega | (congr 1; omega) | rfl

theorem leafCount_nil (N : Nat) : leafCount [] N = 2 ^ N := by
  simp [leafCount]

end Bitstring
end K
