/-
Copyright (c) 2025. All rights reserved.
Subgradient method definitions for convex optimization.
-/
import Mathlib

noncomputable section

open Real Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Subgradient definition -/

/-- `g` is a subgradient of `f` at point `x`:
    `f(y) ≥ f(x) + ⟨g, y − x⟩` for every `y`. -/
def IsSubgradientAt (f : E → ℝ) (g x : E) : Prop :=
  ∀ y : E, f y ≥ f x + @inner ℝ _ _ g (y - x)

/-
Key consequence: `⟨g, x − y⟩ ≥ f(x) − f(y)`.
-/
lemma IsSubgradientAt.inner_sub_ge {f : E → ℝ} {g x : E}
    (hg : IsSubgradientAt f g x) (y : E) :
    @inner ℝ _ _ g (x - y) ≥ f x - f y := by
  contrapose! hg with h;
  unfold IsSubgradientAt;
  simp +decide [ inner_sub_right ] at h ⊢;
  exact ⟨ y, by linarith ⟩

/-! ## Subgradient method iteration -/

/-- Bundled data for a subgradient method run with **constant** step size `α`.

  * `x k` is the k-th iterate, `g k` is the chosen subgradient at `x k`.
  * `xStar` is a minimiser of `f`, `G` bounds all subgradient norms,
    `R = ‖x 0 − xStar‖` is the initial distance. -/
structure SubgradientRun (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- Objective function -/
  f : E → ℝ
  /-- A minimiser of `f` -/
  xStar : E
  /-- Uniform bound on subgradient norms -/
  G : ℝ
  /-- Initial distance to optimum -/
  R : ℝ
  /-- Number of iterations (positive) -/
  K : ℕ
  /-- Iterates -/
  x : ℕ → E
  /-- Subgradients chosen at each iterate -/
  g : ℕ → E
  /-- Constant step size -/
  α : ℝ
  /-- `G > 0` -/
  hG_pos : 0 < G
  /-- `R > 0` -/
  hR_pos : 0 < R
  /-- `K ≥ 1` -/
  hK_pos : 0 < K
  /-- Step size is `R / (G √K)` -/
  hα_def : α = R / (G * √↑K)
  /-- `R` equals the initial distance -/
  hR_def : R = ‖x 0 - xStar‖
  /-- Update rule: `x_{k+1} = x_k − α · g_k` -/
  h_update : ∀ k, x (k + 1) = x k - α • g k
  /-- Each `g k` is a subgradient of `f` at `x k` -/
  h_subgrad : ∀ k, IsSubgradientAt f (g k) (x k)
  /-- Subgradient norms uniformly bounded by `G` -/
  h_norm_bound : ∀ k, ‖g k‖ ≤ G
  /-- `xStar` is a global minimiser -/
  h_minimizer : ∀ y, f xStar ≤ f y

end