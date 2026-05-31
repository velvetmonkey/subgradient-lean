# subgradient-lean: Formal Proofs of Subgradient Method Convergence in Lean 4

Ben Cassie  
2026

## Abstract

`subgradient-lean` is a Lean 4 / Mathlib library formalising the classical convergence theorem for the subgradient method on convex, possibly non-smooth objectives. The library defines the subgradient predicate `IsSubgradientAt`, packages a full trajectory in `SubgradientRun`, proves the exact squared-distance identity for a subgradient step, derives the per-step distance bound, telescopes the resulting inequalities, and proves the `O(1/sqrt K)` running-minimum guarantee. The development contains zero `sorry`, zero `admit`, and uses standard Lean/Mathlib axioms only. It provides a checked baseline theorem for non-smooth convex optimisation and a reusable component for formal work on learning theory and AI safety.

## 1. Introduction

Gradient descent assumes differentiability. Many important convex objectives are not differentiable: hinge losses, absolute-value penalties, maximums of affine functions, and composite regularisers all have corners. The subgradient method is the basic first-order method for this setting. At each iterate it chooses any subgradient `g` and updates

```text
x_{k+1} = x_k - alpha g_k.
```

The method is simple, but its convergence proof differs sharply from smooth gradient descent. A subgradient step need not decrease the objective. The last iterate need not be the best iterate. The guarantee is usually for the running minimum, obtained from a distance-to-optimum inequality and an averaging argument.

The formal setting is a real inner product space `E` and a convex function `f : E -> R`. A vector `g` is a subgradient at `x` when

```text
forall y, f(y) >= f(x) + <g, y - x>.
```

The library uses a constant step size

```text
alpha = R / (G sqrt K),
```

where `R` bounds the initial distance to an optimum and `G` bounds the subgradient norms. It proves

```text
exists i < K, f(x_i) - f* <= R G / sqrt K.
```

This is the standard non-smooth convex `O(1/sqrt K)` rate.

## 2. Library Overview

The project is organised into three implementation modules plus a root import file:

- `SubgradientLean/Defs.lean` defines `IsSubgradientAt`, proves `IsSubgradientAt.inner_sub_ge`, and defines `SubgradientRun`.
- `SubgradientLean/SubgradientBound.lean` proves the exact squared-norm identity and the per-step subgradient distance bound.
- `SubgradientLean/Convergence.lean` proves the summed bound and the final `O(1/sqrt K)` convergence theorem.
- `SubgradientLean.lean` is the root module importing the library.

The project depends on Lean `v4.28.0` and Mathlib `v4.28.0`.

`SubgradientRun` bundles the objective, optimum, iterate sequence, subgradient sequence, step size, bounded-subgradient hypothesis, and update rule. This makes the convergence theorem self-contained: applying it means constructing a run satisfying the stated assumptions.

## 3. Theorem Inventory

The source contains seven headline definitions and results, organised into three layers.

### Layer 1 - Subgradient Mechanics

1. `IsSubgradientAt` — The subgradient predicate:

```text
forall y, f(y) >= f(x) + <g, y - x>.
```

2. `IsSubgradientAt.inner_sub_ge` — The predicate rearranged into the form used by the proof:

```text
<g, x - y> >= f(x) - f(y).
```

3. `SubgradientRun` — A trajectory structure bundling iterates, subgradients, the optimum, the constant step size, and the hypotheses required for convergence.

### Layer 2 - Per-Step Bound

4. `norm_sq_sub_smul_sub` — The exact identity

```text
||(x - alpha g) - z||^2 =
  ||x - z||^2 - 2 alpha <g, x - z> + alpha^2 ||g||^2.
```

5. `subgradient_step_bound` — The per-step distance inequality:

```text
||x_{k+1} - x*||^2 <= ||x_k - x*||^2
  - 2 alpha (f(x_k) - f*) + alpha^2 G^2.
```

The theorem uses the subgradient inequality and the uniform norm bound `||g_k|| <= G`.

### Layer 3 - Convergence

6. `subgradient_sum_bound` — Summing the per-step inequalities yields

```text
2 alpha * sum_{i<K} (f(x_i) - f*) <= R^2 + K alpha^2 G^2.
```

7. `subgradient_convergence` — With `alpha = R / (G sqrt K)`, there exists an iterate satisfying

```text
exists i < K, f(x_i) - f* <= R G / sqrt K.
```

This is the running-minimum `O(1/sqrt K)` theorem.

## 4. Key Technical Highlights

### No Per-Step Descent

Unlike smooth gradient descent, the subgradient method has no general per-step objective decrease. A valid subgradient can point in a direction that temporarily increases `f`. This is not a proof artifact; it is a real feature of non-smooth convex optimisation.

The theorem therefore does not claim that `f(x_k)` is monotone or that the last iterate is optimal at the stated rate. It proves the existence of a good iterate among the first `K` steps.

### The Norm Identity

The exact squared-norm identity is the algebraic heart of the proof. It exposes the inner product `<g_k, x_k - x*>`, which the subgradient inequality converts into a function gap. The remaining `alpha^2 ||g_k||^2` term is controlled by the uniform bound `G`.

This is the same basic geometry as gradient descent, but without smoothness there is no gradient-norm decrease term to exploit.

### Telescoping and Pigeonhole

The per-step inequalities telescope because they compare successive squared distances to the optimum. After summing, all intermediate distances cancel. The resulting sum bound controls the average function gap. If every iterate had gap larger than the claimed bound, the sum would exceed the theorem. Therefore some iterate must be good.

### Optimal Non-Smooth Rate

The `O(1/sqrt K)` rate is the correct scale for general non-smooth convex optimisation. Without smoothness, the faster `O(1/k)` and accelerated `O(1/k^2)` rates are not available in general. This places `subgradient-lean` next to `sgd-lean` and `mirror-descent-lean`, which also prove `O(1/sqrt K)` guarantees under different sources of difficulty.

## 5. Relation to Sibling Libraries

`gradient-descent-lean` has DOI `10.5281/zenodo.20472996` and proves smooth deterministic convergence with per-step descent and `O(1/k)` rates. `subgradient-lean` removes differentiability and accepts the slower running-minimum guarantee.

`sgd-lean` studies noisy smooth objectives. It shares the same rate scale but for a different reason: stochastic or bounded noise rather than non-smoothness.

`mirror-descent-lean` generalises the subgradient method from Euclidean distance to Bregman geometry. The proof shape remains a distance/divergence inequality followed by telescoping.

`proximal-gd-lean` handles non-smooth composite objectives when the non-smooth part has exploitable proximal structure. It can recover an `O(1/k)` rate in settings where plain subgradient descent is slower.

## 6. AI Safety Significance

Non-smooth objectives appear in robust optimisation, constrained penalties, max-loss formulations, and verification-inspired training objectives. A safety argument that assumes differentiability may not apply to these cases. The subgradient method is a minimal formal model of optimisation under non-smooth convex structure.

The library also highlights a caution: non-smooth optimisation does not necessarily improve monotonically. Safety claims based on monotone objective decrease must check that the algorithm really has such a property. For the subgradient method, the checked guarantee is weaker and correctly stated for the running minimum.

## 7. Conclusion

`subgradient-lean` formalises the standard convergence proof for the subgradient method in Lean 4. It defines subgradients, bundles trajectories, proves the per-step distance bound, telescopes the result, and derives the `O(1/sqrt K)` running-minimum theorem. The library is a compact non-smooth optimisation component for Lean's growing collection of verified learning and dynamics results.

## References

Shor, N. Z. (1985). *Minimization Methods for Non-Differentiable Functions*. Springer.

Polyak, B. T. (1967). *A general method for solving extremal problems*. Soviet Mathematics Doklady, 8, 593-597.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

