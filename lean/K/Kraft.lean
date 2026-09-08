/-
Kraft / holography for prefix-free programs.

Integer Kraft: a prefix-free family occupies at most the full binary tree
of depth `N`, i.e. `∑ 2^{N-|p|} ≤ 2^N`, or `∑ 2^{-|p|} ≤ 1`.
Equal-length codes recover the holographic bound `|P| ≤ 2^A`.
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

/-! ### Variable-length Kraft: split into 0-tails and 1-tails -/

/-- Tails of programs in `ps` that start with bit `b`. -/
def tailsWith (b : Bool) (ps : List Bitstring) : List Bitstring :=
  ps.filterMap fun p =>
    match p with
    | c :: t => if c = b then some t else none
    | [] => none

theorem mem_tailsWith {b : Bool} {ps : List Bitstring} {t : Bitstring} :
    t ∈ tailsWith b ps ↔ (b :: t) ∈ ps := by
  unfold tailsWith
  constructor
  · intro h
    obtain ⟨p, hp, hp'⟩ := List.mem_filterMap.mp h
    cases p with
    | nil => simp at hp'
    | cons c u =>
      by_cases hc : c = b
      · subst hc
        simp at hp'
        subst hp'
        exact hp
      · simp [hc] at hp'
  · intro h
    exact List.mem_filterMap.mpr ⟨b :: t, h, by simp⟩

theorem tailsWith_cons_nil (b : Bool) (ps : List Bitstring) :
    tailsWith b ([] :: ps) = tailsWith b ps := by
  simp [tailsWith]

theorem tailsWith_cons_eq (b : Bool) (t : Bitstring) (ps : List Bitstring) :
    tailsWith b ((b :: t) :: ps) = t :: tailsWith b ps := by
  simp [tailsWith]

theorem tailsWith_cons_ne (b c : Bool) (t : Bitstring) (ps : List Bitstring)
    (h : c ≠ b) :
    tailsWith b ((c :: t) :: ps) = tailsWith b ps := by
  simp [tailsWith, h]

theorem prefixFree_tail {p : Bitstring} {ps : List Bitstring}
    (h : PrefixFree (p :: ps)) : PrefixFree ps :=
  ⟨(List.nodup_cons.mp h.1).2, fun x hx y hy hp =>
    h.2 x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hp⟩

theorem nodup_tailsWith {b : Bool} {ps : List Bitstring} (h : ps.Nodup) :
    (tailsWith b ps).Nodup := by
  induction ps with
  | nil => simp [tailsWith]
  | cons p rest ih =>
    rw [List.nodup_cons] at h
    have ih' := ih h.2
    match p with
    | [] =>
      simpa [tailsWith_cons_nil] using ih'
    | c :: t =>
      by_cases hc : c = b
      · subst hc
        rw [tailsWith_cons_eq, List.nodup_cons]
        refine ⟨?_, ih'⟩
        intro ht
        exact h.1 (mem_tailsWith.mp ht)
      · simpa [tailsWith_cons_ne b c t rest hc] using ih'

theorem prefixFree_tailsWith {b : Bool} {ps : List Bitstring}
    (h : PrefixFree ps) : PrefixFree (tailsWith b ps) := by
  refine ⟨nodup_tailsWith h.1, ?_⟩
  intro t ht u hu hpref
  have ht' : (b :: t) ∈ ps := mem_tailsWith.mp ht
  have hu' : (b :: u) ∈ ps := mem_tailsWith.mp hu
  have hcons : (b :: t) <+: (b :: u) :=
    List.cons_prefix_cons.mpr ⟨rfl, hpref⟩
  have heq := h.2 (b :: t) ht' (b :: u) hu' hcons
  injection heq

theorem kraftSum_zero_of_long (ps : List Bitstring) (N : Nat)
    (h : ∀ p ∈ ps, N < p.length) : kraftSum ps N = 0 := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    have hp : N < p.length := h p (by simp)
    have hrest : ∀ q ∈ rest, N < q.length := fun q hq => h q (by simp [hq])
    simp [kraftSum_cons, leafCount_of_length_gt hp, ih hrest]

theorem kraftSum_split (ps : List Bitstring) (N : Nat) (hnil : [] ∉ ps) :
    kraftSum ps (N + 1) =
      kraftSum (tailsWith false ps) N + kraftSum (tailsWith true ps) N := by
  induction ps with
  | nil => simp [kraftSum, tailsWith]
  | cons p rest ih =>
    have hrest : [] ∉ rest := fun hr => hnil (List.mem_cons_of_mem _ hr)
    have ih' := ih hrest
    match p with
    | [] => exact (hnil (by simp)).elim
    | b :: t =>
      have hleaf : leafCount (b :: t) (N + 1) = leafCount t N := leafCount_cons b t N
      cases b
      · rw [kraftSum_cons, hleaf, ih']
        rw [tailsWith_cons_eq false t rest]
        rw [tailsWith_cons_ne true false t rest Bool.false_ne_true]
        simp [kraftSum_cons]
        omega
      · rw [kraftSum_cons, hleaf, ih']
        rw [tailsWith_cons_eq true t rest]
        rw [tailsWith_cons_ne false true t rest Bool.false_ne_true.symm]
        simp [kraftSum_cons]
        omega

/-- Kraft's inequality, integer form: a prefix-free set of programs occupies
at most the full binary tree of depth `N`. Equivalently `∑ 2^{-|p|} ≤ 1`. -/
theorem kraft_le (ps : List Bitstring) (N : Nat) (h : PrefixFree ps) :
    kraftSum ps N ≤ 2 ^ N := by
  induction N generalizing ps with
  | zero =>
    by_cases hnil : [] ∈ ps
    · have hps := prefixFree_of_nil_mem h hnil
      subst hps
      simp [kraftSum, leafCount]
    · have hlong : ∀ p ∈ ps, 0 < p.length := by
        intro p hp
        match p with
        | [] => exact (hnil hp).elim
        | _ :: _ => simp
      have := kraftSum_zero_of_long ps 0 hlong
      omega
  | succ N ih =>
    by_cases hnil : [] ∈ ps
    · have hps := prefixFree_of_nil_mem h hnil
      subst hps
      simp [kraftSum, leafCount]
    · have i0 := ih (tailsWith false ps) (prefixFree_tailsWith h)
      have i1 := ih (tailsWith true ps) (prefixFree_tailsWith h)
      rw [kraftSum_split ps N hnil]
      have : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
      omega

/-- Fixed-length codes occupy one leaf each, so the Kraft sum is the count. -/
theorem kraftSum_eq_length_of_fixed (ps : List Bitstring) (A : Nat)
    (hlen : ∀ p ∈ ps, p.length = A) :
    kraftSum ps A = ps.length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    have hp : p.length = A := hlen p (by simp)
    have hlen' : ∀ q ∈ rest, q.length = A := fun q hq => hlen q (by simp [hq])
    have hleaf : leafCount p A = 1 := by
      rw [leafCount_of_length_le (Nat.le_of_eq hp), hp, Nat.sub_self, Nat.pow_zero]
    rw [kraftSum_cons, List.length_cons, hleaf, ih hlen', Nat.add_comm]

/-- Equal-length prefix-free codes: Kraft specialises to holography. -/
theorem holographic_bound_of_prefixFree (ps : List Bitstring) (A : Nat)
    (h : PrefixFree ps) (hlen : ∀ p ∈ ps, p.length = A) :
    ps.length ≤ 2 ^ A := by
  have hk := kraft_le ps A h
  have hones := kraftSum_eq_length_of_fixed ps A hlen
  omega

end K
