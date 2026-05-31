/-
Copyright (c) 2025. All rights reserved.
O(1/√K) convergence of the subgradient method.
-/
import SubgradientLean.SubgradientBound

noncomputable section

open Real Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Telescoping sum -/

/-
After `K` steps of the subgradient method with constant step `α`,
    `0 ≤ R² − 2α ∑_{i<K} (f(xᵢ) − f*) + K α² G²`.
    Equivalently, `2α ∑ (f(xᵢ) − f*) ≤ R² + K α² G²`.
-/
theorem subgradient_sum_bound
    {f : E → ℝ} {x : ℕ → E} {g : ℕ → E} {xStar : E}
    {α G R : ℝ} {K : ℕ}
    (hα : 0 ≤ α) (_hG : 0 ≤ G)
    (hR : R = ‖x 0 - xStar‖)
    (h_update : ∀ k, x (k + 1) = x k - α • g k)
    (h_subgrad : ∀ k, IsSubgradientAt f (g k) (x k))
    (h_bound : ∀ k, ‖g k‖ ≤ G) :
    2 * α * ∑ i ∈ range K, (f (x i) - f xStar) ≤ R ^ 2 + ↑K * α ^ 2 * G ^ 2 := by
  -- Apply induction on K to prove the inequality.
  have h_ind : ∀ k ≤ K, ‖x k - xStar‖ ^ 2 ≤ R ^ 2 - 2 * α * (∑ i ∈ Finset.range k, (f (x i) - f xStar)) + k * α ^ 2 * G ^ 2 := by
    intro k;
    induction' k with k ih;
    · aesop;
    · intro hk
      have h_step : ‖x (k + 1) - xStar‖ ^ 2 ≤ ‖x k - xStar‖ ^ 2 - 2 * α * (f (x k) - f xStar) + α ^ 2 * G ^ 2 := by
        grind +suggestions;
      rw [ Finset.sum_range_succ ] ; push_cast ; linarith [ ih ( Nat.le_of_succ_le hk ) ] ;
  linarith [ h_ind K le_rfl, sq_nonneg ( ‖x K - xStar‖ ) ]

/-! ## O(1/√K) convergence -/

/-
**Subgradient method convergence**.
    With step size `α = R/(G√K)`, the best iterate in `{x₀,…,x_{K-1}}`
    satisfies `f(xᵢ) − f* ≤ R G / √K`.

    This is the classical O(1/√K) rate for the subgradient method.
    The bound holds for the **running minimum**, not the last iterate.
-/
theorem subgradient_convergence (run : SubgradientRun E) :
    ∃ i, i < run.K ∧
      run.f (run.x i) - run.f run.xStar ≤ run.R * run.G / √↑run.K := by
  by_contra! h_contra;
  have := @subgradient_sum_bound E _ _ run.f run.x run.g run.xStar ( run.R / ( run.G * Real.sqrt run.K ) ) run.G run.R run.K ?_ ?_ ?_ ?_ ?_;
  any_goals linarith [ run.hG_pos, run.hR_pos, run.hK_pos, run.hα_def, run.hR_def, run.h_update, run.h_subgrad, run.h_norm_bound, run.h_minimizer ];
  · have := this run.h_norm_bound;
    refine' absurd this ( not_le_of_gt _ );
    refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_left ( Finset.sum_lt_sum_of_nonempty ( by norm_num; linarith [ run.hK_pos ] ) fun i hi => h_contra i ( Finset.mem_range.mp hi ) ) ( mul_pos zero_lt_two ( div_pos run.hR_pos ( mul_pos run.hG_pos ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr run.hK_pos ) ) ) ) ) );
    by_cases hK : run.K = 0 <;> simp_all +decide [mul_assoc, mul_comm, mul_left_comm];
    · exact absurd hK run.hK_pos.ne';
    · ring_nf; norm_num [ hK, run.hG_pos.ne', run.hR_pos.ne' ];
      linarith;
  · exact div_nonneg run.hR_pos.le ( mul_nonneg run.hG_pos.le ( Real.sqrt_nonneg _ ) );
  · exact fun k => by rw [ ← run.hα_def, run.h_update ] ;
  · exact run.h_subgrad

end