/-
k: a theory of everything from two infinities, formalized.

This library proves the mathematical core of `paper/k.tex`:

* Cantor's split: `{0,1}*` bijects with `ℕ` (ℵ₀); `ℕ → Bool` is uncountable (`𝔠`).
* Kraft's inequality: `2^{-K}` is a semimeasure on prefix-free programs.
* Einsteinian dominance of the Occam factor.
* The k-cycle: samples are countable, inflation is enumerated by `ℕ`,
  the merge is a well-defined countable sum, and the cycle returns to ℵ₀.
* A discrete analog: zero-curvature (Einstein) configurations uniquely
  minimize `E_smooth` and dominate the analog weight.

Physics postulates (the GR Cauchy problem, the existence of a GR-machine,
the identification of `I_EH` with `K_G` on saddles) remain inputs.  What is
proved is everything that follows once those inputs are granted.
-/

import K.Bitstring
import K.Cardinal
import K.Kraft
import K.Complexity
import K.Theory
import K.Analog
