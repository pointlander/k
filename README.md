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
