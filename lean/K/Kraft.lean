/-
Kraft / holography for prefix-free programs.

A nodup family of programs of a fixed length `A` injects into `{0,1}^A`,
which has `2^A` elements.  That is the holographic bound of k.
-/

import K.Bitstring
import Init.Data.List.Lemmas
import Init.Data.List.Pairwise
import Init.Data.List.Perm
import Init.Data.List.Nat.Range
import Init.Omega

namespace K

open Bitstring List

/-- Binary value of a bitstring, most-significant bit first. -/
def natOfBits : Bitstring → Nat
  | [] => 0
  | false :: t => natOfBits t
  | true :: t => 2 ^ t.length + natOfBits t

theorem natOfBits_lt : ∀ s : Bitstring, natOfBits s < 2 ^ s.length
  | [] => by simp [natOfBits]
  | false :: t => by
      have := natOfBits_lt t
      simp [natOfBits, Nat.pow_succ]
      omega
  | true :: t => by
      have := natOfBits_lt t
      simp [natOfBits, Nat.pow_succ]
      omega

theorem natOfBits_injective_of_length_eq :
    ∀ {p q : Bitstring}, p.length = q.length → natOfBits p = natOfBits q → p = q := by
  intro p
  induction p with
  | nil =>
    intro q hlen hval
    cases q with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons b t ih =>
    intro q hlen hval
    cases q with
    | nil => simp at hlen
    | cons c u =>
      have htlen : t.length = u.length := by simp at hlen; exact hlen
      cases b <;> cases c
      · have : natOfBits t = natOfBits u := by simp [natOfBits] at hval; exact hval
        simp [ih htlen this]
      · have ht := natOfBits_lt t
        simp [natOfBits] at hval
        rw [htlen] at ht
        have hge : 2 ^ u.length ≤ natOfBits t := by
          rw [hval]
          exact Nat.le_add_right _ _
        exact (Nat.not_le.mpr ht hge).elim
      · have hu := natOfBits_lt u
        simp [natOfBits] at hval
        have hge : 2 ^ t.length ≤ natOfBits u := by
          have : natOfBits u = 2 ^ t.length + natOfBits t := hval.symm
          rw [this]
          exact Nat.le_add_right _ _
        rw [htlen] at hge
        exact (Nat.not_le.mpr hu hge).elim
      · have : natOfBits t = natOfBits u := by
          simp [natOfBits] at hval
          rw [htlen] at hval
          omega
        simp [ih htlen this]

theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β}
    (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map]
    rw [List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)⟩
    intro hfa
    obtain ⟨b, hb, hfeq⟩ := List.mem_map.mp hfa
    have : a = b := hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hfeq.symm
    subst this
    exact hnd.1 hb

/-- Holographic bound for fixed-length codes: at most `2^A` programs of length `A`.
In k this is the leading term of `K_G(s|_R) ≤ A/4ℓ_P²`. -/
theorem holographic_bound (ps : List Bitstring) (A : Nat)
    (hnd : ps.Nodup) (hlen : ∀ p ∈ ps, p.length = A) :
    ps.length ≤ 2 ^ A := by
  let f : Bitstring → Nat := natOfBits
  have hbound : ∀ p ∈ ps, f p < 2 ^ A := by
    intro p hp
    have := natOfBits_lt p
    simpa [f, hlen p hp] using this
  have hinj : ∀ a ∈ ps, ∀ b ∈ ps, f a = f b → a = b := by
    intro a ha b hb hf
    have : a.length = b.length := by simp [hlen a ha, hlen b hb]
    exact natOfBits_injective_of_length_eq this (by simpa [f] using hf)
  have hmap : (ps.map f).Nodup := nodup_map_of_inj hnd hinj
  have hsub : ps.map f ⊆ List.range (2 ^ A) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    exact List.mem_range.mpr (hbound p hp)
  have := List.Nodup.length_le_of_subset hmap hsub
  simpa [List.length_range, List.length_map] using this

/-- Integer Kraft sum: `∑_p 2^{N - |p|}`. -/
def kraftSum (ps : List Bitstring) (N : Nat) : Nat :=
  (ps.map (fun p => leafCount p N)).sum

@[simp] theorem kraftSum_nil (N : Nat) : kraftSum [] N = 0 := rfl

theorem kraftSum_cons (p : Bitstring) (ps : List Bitstring) (N : Nat) :
    kraftSum (p :: ps) N = leafCount p N + kraftSum ps N := by
  simp [kraftSum]

theorem leafCount_le (p : Bitstring) (N : Nat) : leafCount p N ≤ 2 ^ N := by
  unfold leafCount
  split
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le _ _)
  · exact Nat.zero_le _

/-- Each program occupies at most the whole tree, so the Kraft sum is at most
`|ps| · 2^N`.  Combined with `holographic_bound` this keeps the merge finite. -/
theorem kraftSum_le_mul (ps : List Bitstring) (N : Nat) :
    kraftSum ps N ≤ ps.length * 2 ^ N := by
  induction ps with
  | nil => simp [kraftSum]
  | cons p rest ih =>
    rw [kraftSum_cons, List.length_cons]
    have hleaf := leafCount_le p N
    have : leafCount p N + kraftSum rest N ≤ 2 ^ N + rest.length * 2 ^ N :=
      Nat.add_le_add hleaf ih
    have hmul : 2 ^ N + rest.length * 2 ^ N = (rest.length + 1) * 2 ^ N := by
      simp [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

end K
