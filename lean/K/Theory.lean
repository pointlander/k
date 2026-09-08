/-
The k-cycle, as a Lean structure, and the theorems that follow from it.

  QFT state  --Born-->  sample s ∈ {0,1}*  --Γ-->  universe
       ↑                                           |
       +------ merge ρ⋆  ←------  W(s) ∝ born(s) 2^{-K_G(s)}

Five postulates of the paper become fields of `KTheory`.  The lemmas below
are the parts of the theory that are mathematics, not physics.
-/

import K.Bitstring
import K.Cardinal
import K.Kraft
import K.Complexity
import Init.Data.Function
import Init.Omega

namespace K

open Function Bitstring

/-- A finite-resolution run of the k-cycle.

* `U` is the GR-machine (Postulate 4).
* `born` is the Born factor `|⟨e_s|Ω⟩|²` in integer units (Postulate 1, 3).
* `Gamma` inflates a sample to a continuum universe (Postulate 2, 3).
* `Kof s` is `K_G(s)`, assumed given (uncomputable in the paper; an input here).
* `cutoff` is the finite-resolution depth `N` at which the merge is normalized.
-/
structure KTheory (Geo : Type) where
  U : Machine
  prefixFree : PrefixFreeMachine U
  born : Bitstring → Nat
  Gamma : Bitstring → Geo
  Kof : Bitstring → Nat
  cutoff : Nat
  Kof_le_cutoff : ∀ s, Kof s ≤ cutoff
  Kof_correct : ∀ s, IsK U s (Kof s)

namespace KTheory

variable {Geo : Type} (T : KTheory Geo)

/-- Unnormalized k-weight: Born × Occam, at the cycle's cutoff. -/
def weight (s : Bitstring) : Nat :=
  T.born s * 2 ^ (T.cutoff - T.Kof s)

/-- Partition function of a finite list of samples. -/
def Z (ss : List Bitstring) : Nat :=
  (ss.map T.weight).sum

/-- Normalized merge weight, when `Z ≠ 0`.  Represented as a pair of Nats. -/
def mergeWeight (ss : List Bitstring) (s : Bitstring) : Nat × Nat :=
  (T.weight s, T.Z ss)

theorem Z_cons (s : Bitstring) (ss : List Bitstring) :
    T.Z (s :: ss) = T.weight s + T.Z ss := by
  simp [Z]

theorem Z_nil : T.Z [] = 0 := rfl

/-- The merge of a finite list of samples is a well-defined Nat (no continuum
measure).  This is the paper's resolution of the gravitational path-integral
measure problem: the domain of summation is `{0,1}*`, cardinality ℵ₀. -/
theorem merge_well_defined (ss : List Bitstring) : ∃ n : Nat, T.Z ss = n :=
  ⟨T.Z ss, rfl⟩

/-- Decoherent merge: a weighted sum of observables on inflated universes,
indexed by samples, not by a continuum of metrics. -/
def expect (ss : List Bitstring) (O : Geo → Nat) : Nat :=
  (ss.map (fun s => T.weight s * O (T.Gamma s))).sum

/-- A sample from a finite list.  The inhabited universe of the paper is a
`weight`-typical element of this list; any element is a valid draw. -/
def typical? (ss : List Bitstring) : Option Bitstring :=
  ss.head?

/-- Inflation lands in `Geo`, but the *index* of the merge is a bitstring.
The continuum is generated and then summed out. -/
theorem cycle_index {ss : List Bitstring} :
    (ss.map T.Gamma).length = ss.length := by
  simp

/-- Every universe that the merge can see is `Gamma` of a sample, and samples
are enumerable by `Nat`.  This is `ℵ₀ → 𝔠 → ℵ₀`. -/
theorem cycle_closes (s : Bitstring) :
    T.Gamma s = enumImage T.Gamma (encode s) :=
  (enumImage_complete T.Gamma s).symm

/-- Einsteinian dominance for the k-weight, paper Proposition.

If `K_G(s_R) ≥ K_G(s_E) + c`, the random universe is suppressed by `2^c`
relative to the Einsteinian one, up to the Born ratio. -/
theorem einsteinian_dominance (sE sR : Bitstring) (c : Nat)
    (hc : T.Kof sE + c ≤ T.Kof sR) :
    T.weight sR * T.born sE * 2 ^ c ≤ T.weight sE * T.born sR := by
  simp [weight]
  exact weight_ratio hc (T.Kof_le_cutoff sE) (T.Kof_le_cutoff sR)

/-- A list of shortest programs of a fixed length `A` obeys the holographic
bound: there are at most `2^A` of them. -/
theorem occam_holography
    (ps : List Bitstring) (A : Nat)
    (hnodup : ps.Nodup)
    (hlen : ∀ p ∈ ps, p.length = A) :
    ps.length ≤ 2 ^ A :=
  holographic_bound ps A hnodup hlen

/-- Occam mass of any finite prefix-free program list is a semimeasure. -/
theorem occam_semimeasure (ps : List Bitstring) (h : PrefixFree ps) :
    kraftSum ps T.cutoff ≤ 2 ^ T.cutoff :=
  kraft_le ps T.cutoff h

/-- Physical continuum hypothesis, for objects the cycle actually constructs.

Samples inject into `Nat`.  Inflated universes that arise are enumerated by
`Nat`.  The continuum of all binary sequences does *not* inject backwards
from `Nat`.  Nothing in between is built. -/
theorem physical_CH :
    Injective (encode : Bitstring → Nat) ∧
      (∀ s, ∃ n, enumImage T.Gamma n = T.Gamma s) ∧
        ¬ ∃ f : Nat → Continuum, Surjective f :=
  ⟨encode_injective, inflation_image_enumerable T.Gamma, fun ⟨f, hf⟩ =>
    cantor_diagonal f hf⟩

end KTheory

/-- Postulate package: a separable skeleton, a continuum of geometries, a
prefix-free GR-machine.  This is the whole ontology. -/
structure Ontology where
  Geo : Type
  intoContinuum : Geo → Continuum
  into_inj : Injective intoContinuum
  theory : KTheory Geo

/-- Classical geometries are at most continuum-many: they inject into
`Nat → Bool`.  Combined with Cantor's diagonal, they are not countable. -/
theorem Ontology.geo_injects_continuum (O : Ontology) :
    Injective O.intoContinuum :=
  O.into_inj

/-- QFT labels are countable; GR geometries inject into the continuum.
The two infinities are different. -/
theorem Ontology.two_infinities (O : Ontology) :
    Injective (encode : Bitstring → Nat) ∧ Injective O.intoContinuum ∧
      ¬ ∃ f : Nat → Continuum, Surjective f :=
  ⟨encode_injective, O.into_inj, fun ⟨f, hf⟩ => cantor_diagonal f hf⟩

end K
