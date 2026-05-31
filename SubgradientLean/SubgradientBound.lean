/-
Copyright (c) 2025. All rights reserved.
Per-step distance bound for the subgradient method.
-/
import SubgradientLean.Defs

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Per-step distance bound

If `x' = x − α · g` where `g` is a subgradient of `f` at `x` with `‖g‖ ≤ G`,
then for any point `z`:

  `‖x' − z‖² ≤ ‖x − z‖² − 2α(f(x) − f(z)) + α² G²`

This is the fundamental inequality underlying subgradient convergence.
Note: there is **no** descent guarantee for `f` — only a distance bound.
-/

/-- **Per-step distance identity** (general version for any step size `α`).

  `‖(x − α g) − z‖² = ‖x − z‖² − 2α⟨g, x − z⟩ + α²‖g‖²` -/
theorem norm_sq_sub_smul_sub {x z g : E} {α : ℝ} :
    ‖(x - α • g) - z‖ ^ 2 =
      ‖x - z‖ ^ 2 - 2 * α * @inner ℝ _ _ g (x - z) + α ^ 2 * ‖g‖ ^ 2 := by
  rw [show x - α • g - z = (x - z) - α • g by abel1, @norm_sub_sq ℝ]
  simp +decide [inner_smul_right, norm_smul, mul_pow]
  rw [real_inner_comm]; ring

/-- **Per-step bound for the subgradient method**.

  `‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² − 2α(f(x_k) − f(x*)) + α² G²` -/
theorem subgradient_step_bound
    {f : E → ℝ} {x z g : E} {α G : ℝ}
    (hg : IsSubgradientAt f g x)
    (h_bound : ‖g‖ ≤ G)
    (hα : 0 ≤ α) :
    ‖(x - α • g) - z‖ ^ 2 ≤
      ‖x - z‖ ^ 2 - 2 * α * (f x - f z) + α ^ 2 * G ^ 2 := by
  rw [norm_sq_sub_smul_sub]
  gcongr
  exact IsSubgradientAt.inner_sub_ge hg z

end
