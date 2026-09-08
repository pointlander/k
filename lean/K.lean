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
* Minisuperspace: Friedmann constraint, de Sitter fixed point, Einstein as
  compressor, and k-weight dominance of on-shell 3-data.
* Evaporation: Bondi constraint, leftover holography, constant Page `K̂_G`,
  and dominance of the Page family over remnants and scrambles.
* Laboratory Born correction: isolated short-vs-dump disagrees with Born;
  thermal records and equal-K clicks track Born; additive environments
  do not swamp.
* Dimensionality: local graviton polarizations `D(D−3)/2`, Lovelock
  zero/topological/dynamical, and 4d Einstein–Hilbert as the 2-bit vacuum
  compressor over 2+1 (dead) and 5d plus moduli.
* Field-theory plugins: a prefix-free group grammar, Higgs in-word
  (SM fund vs `SU(5)` adj+fund), `SU(5)` still the minimizer after
  charging `24+5`, raw `N`-landscapes longer than the SM word.

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
import K.Mini
import K.Evap
import K.Lab
import K.Dim
import K.Plugin
