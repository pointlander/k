/-
Cantor's two infinities, as used by k.

* Finite binary strings `{0,1}*` are in bijection with `Nat` (ℵ₀).
* Infinite binary sequences `Nat → Bool` are a model of the continuum `𝔠 = 2^{ℵ₀}`.
* There is no surjection `Nat → (Nat → Bool)` (Cantor's diagonal).
-/

import K.Bitstring
import Init.Data.Function

namespace K

open Function

/-! ### Strings are countable: bijection with `Nat` -/

/-- Gödel-style encoding of a finite bitstring as a natural number. -/
def encode : Bitstring → Nat
  | [] => 0
  | false :: xs => 2 * encode xs + 1
  | true :: xs => 2 * encode xs + 2

@[simp] theorem encode_nil : encode [] = 0 := rfl

theorem encode_eq_zero {s : Bitstring} : encode s = 0 ↔ s = [] := by
  constructor
  · intro h
    cases s with
    | nil => rfl
    | cons b xs =>
      cases b <;> simp [encode] at h
  · intro h
    simp [h]

theorem encode_pos_of_cons {b : Bool} {xs : Bitstring} : 0 < encode (b :: xs) := by
  cases b <;> simp [encode] <;> omega

/-- Inverse of `encode`. Every natural number is a unique program. -/
def decode : Nat → Bitstring
  | 0 => []
  | n + 1 =>
    if (n + 1) % 2 = 1 then
      false :: decode (n / 2)
    else
      true :: decode (n / 2)

theorem encode_decode (n : Nat) : encode (decode n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [decode]
    | succ m =>
      simp only [decode]
      split
      · simp [encode]
        have ih' : encode (decode (m / 2)) = m / 2 := ih (m / 2) (by omega)
        have : m + 1 = 2 * (m / 2) + 1 := by
          have hmod := Nat.mod_add_div (m + 1) 2
          omega
        omega
      · simp [encode]
        have ih' : encode (decode (m / 2)) = m / 2 := ih (m / 2) (by omega)
        have : m + 1 = 2 * (m / 2) + 2 := by
          have hmod := Nat.mod_add_div (m + 1) 2
          omega
        omega

/-- Finite strings inject into `Nat`. This is the ℵ₀ of QFT: programs, modes, samples. -/
theorem encode_injective : Injective encode := by
  intro a
  induction a with
  | nil =>
    intro b h
    exact (encode_eq_zero.mp h.symm).symm
  | cons b xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have : encode (b :: xs) = 0 := h
      exact (Nat.ne_of_gt encode_pos_of_cons this).elim
    | cons c zs =>
      cases b <;> cases c <;> simp [encode] at h
      · have : encode xs = encode zs := by omega
        simp [ih this]
      · omega
      · omega
      · have : encode xs = encode zs := by omega
        simp [ih this]

theorem decode_encode (s : Bitstring) : decode (encode s) = s :=
  encode_injective (by rw [encode_decode])

theorem decode_injective : Injective decode := by
  intro n m h
  have := congrArg encode h
  simpa [encode_decode] using this

theorem encode_surjective : Surjective encode := by
  intro n
  exact ⟨decode n, encode_decode n⟩

theorem decode_surjective : Surjective decode := by
  intro s
  exact ⟨encode s, decode_encode s⟩

/-- `Nat` injects into finite strings (unary). -/
theorem unary_injective : Injective (fun n : Nat => List.replicate n true) := by
  intro n m h
  simpa using congrArg List.length h

/-! ### The continuum is uncountable -/

/-- Infinite binary sequences: a concrete model of Cantor's continuum `𝔠 = 2^{ℵ₀}`. -/
abbrev Continuum := Nat → Bool

/-- Point-mass sequences: `Nat` injects into the continuum. -/
def dirac (n m : Nat) : Bool := decide (n = m)

theorem dirac_injective : Injective dirac := by
  intro n m h
  have : dirac n n = dirac m n := congrFun h n
  simp [dirac] at this
  exact this.symm

/-- Characteristic functions: the continuum *is* the (decidable) power set of the integers.
This is Cantor's identification `𝔠 = 2^{ℵ₀}`. -/
theorem continuum_eq_powerset : Continuum = (Nat → Bool) := rfl

/-- Cantor's 1891 diagonal argument: no surjection from the integers onto the reals. -/
theorem cantor_diagonal (f : Nat → Continuum) : ¬ Surjective f := by
  intro hf
  let d : Continuum := fun n => !(f n n)
  obtain ⟨k, hk⟩ := hf d
  have : d k = f k k := by rw [hk]
  simp [d] at this

/-- The two infinities of k are different sizes. -/
theorem two_infinities :
    Injective (encode : Bitstring → Nat) ∧ ¬ ∃ f : Nat → Continuum, Surjective f :=
  ⟨encode_injective, fun ⟨f, hf⟩ => cantor_diagonal f hf⟩

/-- Sampling cannot emit an uncountable object: every sample is a finite string,
and finite strings biject with `ℕ`. -/
theorem samples_countable : Injective encode ∧ Surjective encode :=
  ⟨encode_injective, encode_surjective⟩

/-- Inflation of samples: the image of `Gamma` is parametrized by `Nat`,
so it is at most countable, whatever continuum structure `Geo` carries. -/
def enumImage {Geo : Type} (Gamma : Bitstring → Geo) (n : Nat) : Geo :=
  Gamma (decode n)

theorem enumImage_complete {Geo : Type} (Gamma : Bitstring → Geo) (s : Bitstring) :
    enumImage Gamma (encode s) = Gamma s := by
  simp [enumImage, decode_encode]

/-- Every inflated universe that actually arises is hit by the `Nat`-enumeration. -/
theorem inflation_image_enumerable {Geo : Type} (Gamma : Bitstring → Geo) :
    ∀ s : Bitstring, ∃ n : Nat, enumImage Gamma n = Gamma s := by
  intro s
  exact ⟨encode s, enumImage_complete Gamma s⟩

end K
