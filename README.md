# k

A theory of everything from two infinities.

Quantum field theory has the infinity of the integers (\(\aleph_0\)): a separable Hilbert space, a countable orthonormal basis, occupation numbers, programs. General relativity has the infinity of the reals (\(\mathfrak{c} = 2^{\aleph_0}\), Cantor): a smooth Lorentzian 4-manifold, uncountably many points, a continuum of metrics. Universes are sampled from the quantum state of the universe. Each sample is inflated to a continuum spacetime by Einstein's equation. Each universe is weighted by gravitational Kolmogorov complexity of the sample. The universes are merged against those weights.

The paper is [`paper/k.tex`](paper/k.tex). A discrete analog of the sample–weight–merge cycle is [`toy/k_merge.py`](toy/k_merge.py).

```
QFT state |Ω⟩  --Born-->  sample s ∈ {0,1}*  --Γ (Einstein)-->  universe U
        ↑                                                          |
        |                                                          |
        +------ merge ρ⋆ ←-------------- weight W(s) ∝ |ψ|² 2^{-K_G(s)}
```

## Paper

```sh
cd paper && make
```

## Toy

```sh
python3 toy/k_merge.py
python3 toy/k_merge.py -n 6 --state w --beta 3
python3 toy/k_merge.py -n 8 --state random --top 12
```

The analog enumerates \(2^n\) universes, scores each by gzip length plus a discrete-curvature (GR-like) penalty, and merges them. It is the shape of the cycle, not gravity.

A minisuperspace cycle, where \(\Gamma\) is an Einstein solver for FLRW plus a homogeneous scalar, is [`toy/minisuperspace.py`](toy/minisuperspace.py):

```sh
python3 toy/minisuperspace.py --self-check
python3 toy/minisuperspace.py --bits 3 --state hh
python3 toy/minisuperspace.py --compare --potential quadratic --bits 3 --no-offshell
```

On-shell 3-data (Friedmann solves for \(H\)) is exponentially preferred over generic 4-data. That is Einstein as a compressor.

`--state hh` and `--state tunneling` are minisuperspace WKB amplitudes, \(|\Psi|^2\propto\exp(\pm 24\pi^2 I_0)\) with \(I_0=1/V\) at the turning point (\(8\pi G=1\)). Hartle–Hawking piles on small \(V\) (little inflation); Vilenkin piles on large \(V\) (more e-folds). `--compare` prints both. `--state gaussian` is the old kinematic envelope.

A 1+1 evaporation cycle, where \(\Gamma\) is discrete Vaidya mass loss, is [`toy/evaporation.py`](toy/evaporation.py):

```sh
python3 toy/evaporation.py --self-check
python3 toy/evaporation.py --bits 6
python3 toy/evaporation.py --compare --bits 6 --no-offshell
python3 toy/evaporation.py --history --bits 6
```

On-shell Page radiation (a reversible function of the microstate) keeps \(\widehat{K}_G = K(s)\) along the history. Remnants that store the bits inside as the area drops, and scrambles that emit independent radiation, pay \(\beta t^2\) and are exponentially downweighted. That is the holographic bound as a process.

A few-qubit Born-correction analog (prediction 2) is [`toy/interferometer.py`](toy/interferometer.py):

```sh
python3 toy/interferometer.py --self-check
python3 toy/interferometer.py --bits 6
python3 toy/interferometer.py --kind clicks
python3 toy/interferometer.py --crossover --bits 6
python3 toy/interferometer.py --full --bits 6
```

Isolated short-vs-dump disagrees with Born by \(2^{\Delta K}\). Two short clicks, and a thermal bath with \(L \ge K(\mathrm{dump})\), track Born. Additive \(K(\mathrm{env})+K(\mathrm{reg})\) does not swamp: a large fridge is not enough. That is laboratory QFT recovered as a limit of the merge.

A 3+1 dimensionality analog, scoring gravity plugins by graviton polarizations \(D(D-3)/2\), Lovelock status, and compactification bits, is [`toy/dimension.py`](toy/dimension.py):

```sh
python3 toy/dimension.py --self-check
python3 toy/dimension.py
python3 toy/dimension.py --compare
```

4d Einstein–Hilbert is the unique maximizer. 2+1 is dead (zero local gravitons). Extra dimensions and curvature junk pay bits. Compressors take essentially all the merge mass. That is Dzhunushaliev's complexity-driven dimensional reduction as a merge.

## Lean

The mathematical core is formalized in Lean 4 (no mathlib) under [`lean/`](lean/):

```sh
cd lean && lake build
```

Proved: Cantor's split (`{0,1}*` bijects with `ℕ`; `ℕ → Bool` is uncountable), Kraft's inequality (`∑ 2^{N-|p|} ≤ 2^N` for prefix-free programs, recovering the holographic bound `|P| ≤ 2^A` at equal length), Einsteinian dominance of the Occam factor, that the merge is a countable sum, that constant (Einstein) configurations minimize discrete curvature, the minisuperspace cycle (Friedmann constraint, de Sitter fixed point, on-shell 3-data as compressor), 1+1 evaporation (Bondi constraint, leftover holography, constant Page \(\widehat{K}_G\), Page dominance over remnants and scrambles), the laboratory Born correction (isolated short-vs-dump disagrees with Born; thermal records and equal-K clicks track Born; additive environments do not swamp), and 3+1 dimensionality (`D(D-3)/2` polarizations, Lovelock zero/topological/dynamical, 4d Einstein–Hilbert as the 2-bit vacuum compressor). Physics postulates (the GR Cauchy problem, the existence of a GR-machine) remain inputs. `cd lean && lake build` checks `K.Mini` against `toy/minisuperspace.py`, `K.Evap` against `toy/evaporation.py`, `K.Lab` against `toy/interferometer.py`, and `K.Dim` against `toy/dimension.py`.
