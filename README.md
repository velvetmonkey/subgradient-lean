# subgradient-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](SubgradientLean)
[![Zenodo](https://img.shields.io/badge/Zenodo-10.5281%2Fzenodo.20475946-blue)](https://zenodo.org/records/20475946)

**subgradient-lean: Formal Proofs of Subgradient Method Convergence in Lean 4**

Lean 4 formal proofs of the subgradient method for non-smooth convex optimisation: a per-step distance bound, a telescoping sum bound, and an O(1/√K) convergence rate for the running minimum.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

The headline theorem is `subgradient_convergence` in `SubgradientLean/Convergence.lean`. With step size `R / (G√K)`, it proves that some index `i < K` has objective gap at most `RG / √K`.

The core calculation bounds the squared distance after one subgradient step using the defining global subgradient inequality and the uniform norm bound `G`. Summing those bounds telescopes the distance terms. An averaging argument then rules out the possibility that every one of the first `K` gaps exceeds the target rate.

The conclusion is existential: it controls the best iterate seen, not necessarily the final iterate. The theorem does not assert per-step objective descent. It also bundles positivity, the exact constant step size, the initial-distance identity, a global minimizer, valid subgradients, and their norm bound as hypotheses of the run.

## Background and motivation

Gradient descent needs a gradient — but many important convex objectives (ℓ₁ penalties, hinge loss, max-of-linear functions) are non-smooth and have no gradient at the points that matter most. The subgradient method replaces ∇f(x) with *any* subgradient g ∈ ∂f(x) and still converges, which is why it is the baseline algorithm for non-smooth convex optimisation. This library machine-checks its O(1/√K) guarantee.

## Setting

A non-smooth convex objective f over a real inner product space, with a subgradient g ∈ ∂f(x) captured by the predicate `IsSubgradientAt f g x` (∀ y, f(y) ≥ f(x) + ⟨g, y − x⟩). The iteration is x_{k+1} = x_k − α·g_k with a **constant step size α = R/(G√K)**, where R bounds ‖x₀ − x*‖ and G bounds the subgradient norms.

## Main result

```
∃ i < K,  f(x_i) − f* ≤ R·G / √K
```

i.e. the best iterate seen in the first K steps is within RG/√K of optimal — the classical **O(1/√K)** rate.

## Key design note

The subgradient method has **no per-step descent guarantee**: a subgradient step can *increase* the objective, so f(x_{k+1}) ≤ f(x_k) simply does not hold in general. This is a fundamental difference from gradient descent. What the analysis controls is the *distance to the optimum* per step, and convergence is proved for the **running minimum** `min_{i<K} f(x_i)` — via a telescoping sum of the per-step distance bounds followed by an averaging / pigeonhole argument — not for the last iterate. The library is stated to reflect this honestly: `subgradient_convergence` produces *some* good iterate i < K, not a monotone decrease.

## Project structure

```
SubgradientLean/
├── Defs.lean             — IsSubgradientAt, IsSubgradientAt.inner_sub_ge, SubgradientRun
├── SubgradientBound.lean — norm_sq_sub_smul_sub, subgradient_step_bound
└── Convergence.lean      — subgradient_sum_bound, subgradient_convergence
SubgradientLean.lean      — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `IsSubgradientAt` | g ∈ ∂f(x): ∀ y, f(y) ≥ f(x) + ⟨g, y − x⟩ |
| 2 | `IsSubgradientAt.inner_sub_ge` | ⟨g, x − y⟩ ≥ f(x) − f(y) |
| 3 | `SubgradientRun` | bundled run: f, x*, iterates, subgradients, step α = R/(G√K), hypotheses |
| 4 | `norm_sq_sub_smul_sub` | ‖(x − αg) − z‖² = ‖x − z‖² − 2α⟨g, x − z⟩ + α²‖g‖² |
| 5 | `subgradient_step_bound` | ‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² − 2α(f(x_k) − f*) + α²G² |
| 6 | `subgradient_sum_bound` | 2α·Σ_{i<K}(f(x_i) − f*) ≤ R² + Kα²G² (telescoping) |
| 7 | `subgradient_convergence` | ∃ i < K, f(x_i) − f* ≤ RG/√K — O(1/√K) |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

**subgradient-lean: Formal Proofs of Subgradient Method Convergence in Lean 4**
Ben Cassie (2026). Companion paper: [paper.md](paper.md).

DOI: https://doi.org/10.5281/zenodo.20475946

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence (O(1/k) rate)
- [sgd-lean](https://github.com/velvetmonkey/sgd-lean) — Lean 4 bounded-noise SGD convergence (O(1/√K) rate)
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences (O(1/√K) rate)
- [proximal-gd-lean](https://github.com/velvetmonkey/proximal-gd-lean) — Lean 4 proximal gradient descent for composite objectives (O(1/k) rate)

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
