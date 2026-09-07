/-
Kolmogorov complexity relative to a prefix-free machine, and the Occam factor
`2^{-K}` of the k-weight.
-/

import K.Bitstring
import K.Kraft
import Init.Data.List.Lemmas
import Init.Omega

namespace K

open Bitstring

/-- A (possibly partial) interpreter: programs to bitstrings. -/
structure Machine where
  eval : Bitstring → Option Bitstring

/-- `p` is a halting program of `U`. -/
def Machine.halts (U : Machine) (p : Bitstring) : Prop :=
  (U.eval p).isSome

/-- `U` is prefix-free: no halting program is a prefix of another. -/
def PrefixFreeMachine (U : Machine) : Prop :=
  ∀ p q, U.halts p → U.halts q → p <+: q → p = q

/-- Program `p` prints sample `s`. -/
def Prints (U : Machine) (p s : Bitstring) : Prop :=
  U.eval p = some s

theorem Prints.halts {U : Machine} {p s : Bitstring} (h : Prints U p s) : U.halts p := by
  simp [Machine.halts, Prints] at h ⊢
  simp [h]

/-- There is a program of length `n` that prints `s`. -/
def HasProgram (U : Machine) (s : Bitstring) (n : Nat) : Prop :=
  ∃ p, p.length = n ∧ Prints U p s

/-- Prefix Kolmogorov complexity of `s` is `n`. -/
def IsK (U : Machine) (s : Bitstring) (n : Nat) : Prop :=
  HasProgram U s n ∧ ∀ m < n, ¬ HasProgram U s m

theorem IsK.unique {U : Machine} {s : Bitstring} {n m : Nat}
    (hn : IsK U s n) (hm : IsK U s m) : n = m := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · exact (hm.2 n h hn.1).elim
  · exact h
  · exact (hn.2 m h hm.1).elim

/-- A shortest program for `s` is a witness to `IsK`. -/
def Shortest (U : Machine) (s : Bitstring) (p : Bitstring) : Prop :=
  Prints U p s ∧ IsK U s p.length

/-- Halting programs of a prefix-free machine form a prefix-free family. -/
theorem prefixFree_of_halting (U : Machine) (hU : PrefixFreeMachine U)
    (ps : List Bitstring) (hnodup : ps.Nodup)
    (hhalt : ∀ p ∈ ps, U.halts p) :
    PrefixFree ps :=
  ⟨hnodup, fun p hp q hq hpq => hU p q (hhalt p hp) (hhalt q hq) hpq⟩

/-- Shortest programs halt, so any nodup list of them is prefix-free. -/
theorem prefixFree_shortest (U : Machine) (hU : PrefixFreeMachine U)
    (ps ss : List Bitstring)
    (hzip : ps.length = ss.length)
    (hshort : ∀ i : Fin ps.length, Shortest U (ss[i]'(by omega)) ps[i])
    (hnodup : ps.Nodup) :
    PrefixFree ps := by
  apply prefixFree_of_halting U hU ps hnodup
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  exact (hshort ⟨i, hi⟩).1.halts

/-- Solomonoff / Kraft, integer form: the Occam mass of any finite list of
programs is bounded.  Combined with `holographic_bound` this is a
semimeasure on samples. -/
theorem solomonoff_semimeasure
    (ps : List Bitstring) (N : Nat) :
    kraftSum ps N ≤ ps.length * 2 ^ N :=
  kraftSum_le_mul ps N

/-- Einsteinian dominance, Occam factor only.

If an Einsteinian sample has complexity `kE` and a random sample has complexity
`kR ≥ kE + c`, the random sample is suppressed by `2^c`. This is the paper's
Proposition (Einsteinian dominance), stripped to the Kolmogorov factor. -/
theorem einsteinian_dominance_occams
    {kE kR c bornR : Nat}
    (hc : kE + c ≤ kR) :
    bornR * 2 ^ kE * 2 ^ c ≤ bornR * 2 ^ kR := by
  have hpow : 2 ^ (kE + c) ≤ 2 ^ kR := Nat.pow_le_pow_right (by decide : 0 < 2) hc
  simp [Nat.pow_add] at hpow
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left bornR hpow

/-- The k-weight ratio in integer arithmetic.

Unnormalized weight `w(s) = born(s) · 2^{M - K(s)}` at cutoff `M`.
If `K(s_R) ≥ K(s_E) + c` then
`w(s_R) · born(s_E) · 2^c ≤ w(s_E) · born(s_R)`. -/
theorem weight_ratio
    {kE kR c bornE bornR M : Nat}
    (hc : kE + c ≤ kR)
    (hkE : kE ≤ M)
    (hkR : kR ≤ M) :
    (bornR * 2 ^ (M - kR)) * bornE * 2 ^ c ≤
      (bornE * 2 ^ (M - kE)) * bornR := by
  have hle : M - kR + c ≤ M - kE := by omega
  have hpow : 2 ^ (M - kR + c) ≤ 2 ^ (M - kE) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  calc
    bornR * 2 ^ (M - kR) * bornE * 2 ^ c
        = bornR * bornE * (2 ^ (M - kR) * 2 ^ c) := by
          simp [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm]
    _ = bornR * bornE * 2 ^ (M - kR + c) := by
          simp [Nat.pow_add]
    _ ≤ bornR * bornE * 2 ^ (M - kE) :=
          Nat.mul_le_mul_left _ hpow
    _ = bornE * 2 ^ (M - kE) * bornR := by
          simp [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm]

end K
