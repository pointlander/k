/-
Finite language for field-theory plugins, matching `toy/plugin.py`.

A group word is a 2-bit tagged prefix-free code:
`U(1) | SU(n) | SO(n) | G × H`, with nats unary (`1ⁿ0`).
A raw landscape of `n` copies costs `Θ(n)`; a generator that prints
`n` copies costs `O(log n)`.  `SU(5)` is a shorter word than
`SU(3)×SU(2)×U(1)`.  A named vacuum list of size `n` is longer than
the SM word once `n` exceeds that word's length.

Phenomenology (`I_wrong`) remains an input, like Choquet–Bruhat in `K.Dim`.
What is proved is the grammar, the length comparisons, and Kraft on
the encodings.
-/

import K.Kraft
import K.Complexity
import Init.Data.Nat.Log2
import Init.Omega

namespace K
namespace Plugin

open Bitstring List

/-! ### Unary nats and the group grammar -/

def unary (n : Nat) : Bitstring :=
  List.replicate n true ++ [false]

theorem unary_length (n : Nat) : (unary n).length = n + 1 := by
  simp [unary]

inductive Group where
  | u1
  | su (n : Nat)
  | so (n : Nat)
  | prod (g h : Group)
  deriving DecidableEq, Repr

def encode : Group → Bitstring
  | .u1 => [false, false]
  | .su n => [false, true] ++ unary n
  | .so n => [true, false] ++ unary n
  | .prod g h => [true, true] ++ encode g ++ encode h

def sm : Group :=
  .prod (.su 3) (.prod (.su 2) .u1)

def su5 : Group := .su 5

def so10 : Group := .so 10

theorem encode_u1_len : (encode .u1).length = 2 := rfl

theorem encode_su_len (n : Nat) : (encode (.su n)).length = n + 3 := by
  simp [encode, unary_length]

theorem encode_so_len (n : Nat) : (encode (.so n)).length = n + 3 := by
  simp [encode, unary_length]

theorem encode_prod_len (g h : Group) :
    (encode (.prod g h)).length = 2 + (encode g).length + (encode h).length := by
  simp [encode]
  omega

theorem encode_su5_len : (encode su5).length = 8 := by
  simp [su5, encode_su_len]

theorem encode_so10_len : (encode so10).length = 13 := by
  simp [so10, encode_so_len]

theorem encode_sm_len : (encode sm).length = 17 := by
  simp [sm, encode, unary_length]

/-- `SU(5)` is a shorter group word than the Standard Model product. -/
theorem su5_shorter_sm : (encode su5).length < (encode sm).length := by
  simp [encode_su5_len, encode_sm_len]

/-! ### Landscapes: raw lists vs generators -/

/-- Wrapped raw list: `01 ++ unary n ++ gⁿ`. -/
def rawLen (n : Nat) (g : Group) : Nat :=
  2 + (n + 1) + n * (encode g).length

/-- Generated list: `10 ++ g ++` self-delimiting `n` of length `2(⌊log₂ n⌋+1)`. -/
def log2len (n : Nat) : Nat :=
  2 * (n.log2 + 1)

def genLen (n : Nat) (g : Group) : Nat :=
  2 + (encode g).length + log2len n

theorem rawLen_u1 (n : Nat) : rawLen n .u1 = 3 + 3 * n := by
  simp [rawLen, encode_u1_len]
  omega

theorem rawLen_ge (n : Nat) (g : Group) : n ≤ rawLen n g := by
  simp [rawLen]
  have : 0 < 2 + (n + 1) := by omega
  have : n ≤ n * (encode g).length + (2 + (n + 1)) := by
    have : 0 ≤ (encode g).length := Nat.zero_le _
    omega
  omega

/-- The SM word is shorter than `n` raw `U(1)` vacua once `n ≥ 5`. -/
theorem sm_beats_raw_u1 (n : Nat) (h : 5 ≤ n) :
    (encode sm).length < rawLen n .u1 := by
  simp [encode_sm_len, rawLen_u1]
  omega

theorem raw16_u1 : rawLen 16 .u1 = 51 := by
  simp [rawLen_u1]

theorem gen16_u1 : genLen 16 .u1 = 14 := by
  simp [genLen, encode_u1_len, log2len]
  -- 16.log2 = 4
  have : (16 : Nat).log2 = 4 := by native_decide
  simp [this]

theorem gen16_lt_raw16 : genLen 16 .u1 < rawLen 16 .u1 := by
  simp [gen16_u1, raw16_u1]

/-! ### Kraft on named group encodings -/

def named : List Group :=
  [.u1, .su 2, .su 3, su5, so10, sm]

def namedEnc : List Bitstring :=
  named.map encode

theorem namedEnc_length : namedEnc.length = 6 := rfl

/-- Distinct named groups have distinct encodings (computed). -/
theorem namedEnc_nodup : namedEnc.Nodup := by
  native_decide

/-- Named encodings are prefix-free (computed against `List.IsPrefix`). -/
theorem named_prefixFree : PrefixFree namedEnc := by
  refine ⟨namedEnc_nodup, ?_⟩
  decide

theorem named_holography :
    namedEnc.length ≤ 2 ^ 17 := by
  have : namedEnc.length = 6 := namedEnc_length
  have : 6 ≤ 2 ^ 17 := by native_decide
  omega

/-- Finite named catalog occupies at most the tree of depth 17
(`|SM| = 17` is the longest word). -/
theorem named_kraft : kraftSum namedEnc 17 ≤ 2 ^ 17 :=
  kraft_le namedEnc 17 named_prefixFree

/-! ### Matter-plugin lengths, matching the Python analog -/

/-- `4d` Einstein–Hilbert gravity word (from `K.Dim`), 2 bits. -/
def gravity4 : Nat := 2

/-- Full theory length: gravity + group + unary `nRep, nGen, degV` + breaking. -/
def theoryLen (g : Group) (nRep nGen degV breakCost : Nat) : Nat :=
  gravity4 + (encode g).length + (nRep + 1) + (nGen + 1) + (degV + 1) + breakCost

def smTheory : Nat := theoryLen sm 5 3 4 0

def su5Theory : Nat := theoryLen su5 2 3 4 2

theorem smTheory_len : smTheory = 34 := by
  simp [smTheory, theoryLen, gravity4, encode_sm_len]

theorem su5Theory_len : su5Theory = 24 := by
  simp [su5Theory, theoryLen, gravity4, encode_su5_len]

/-- Conditioned on an SM-like sample, `SU(5)` plus a 2-bit breaking program
is a shorter plugin than the SM product. -/
theorem su5_beats_sm : su5Theory < smTheory := by
  simp [su5Theory_len, smTheory_len]

theorem sm_beats_raw16 : smTheory < rawLen 16 sm := by
  simp [smTheory_len, rawLen, encode_sm_len]

def weight (born kg M : Nat) : Nat :=
  born * 2 ^ (M - kg)

/-- Occam: the shorter GUT word dominates the SM word at equal Born. -/
theorem su5_dominates_sm (born M : Nat) (hS : 24 ≤ M) (hD : 34 ≤ M) :
    weight born smTheory M * born * 2 ^ 10 ≤
      weight born su5Theory M * born := by
  have hc : su5Theory + 10 ≤ smTheory := by
    simp [su5Theory_len, smTheory_len]
  exact weight_ratio hc (by simp [su5Theory_len]; exact hS)
    (by simp [smTheory_len]; exact hD)

end Plugin
end K
