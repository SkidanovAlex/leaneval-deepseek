import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-!
# Pointwise bounds for the angular weight `Γ(θ)`

`Γ(θ) = (sin θ cos²θ)^{α/3}`.  For `θ ∈ [0,π/2]` the base `u = sin θ cos²θ` lies in
`[0,1]` and the exponent `α/3` is nonnegative, so `Γ` takes values in `[0,1]`.
-/

/-- On the angular interval `Iθ = [0,π/2]`, the base `sin θ cos²θ` lies in `[0,1]`. -/
theorem sin_mul_cos_sq_mem_Icc (θ : ℝ) (hθ : θ ∈ Iθ) :
    0 ≤ Real.sin θ * Real.cos θ ^ 2 ∧ Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  refine ⟨mul_nonneg hs0 (by positivity), ?_⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ^ 2 ≤ 1 := by
    have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    simpa using h
  have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
  simpa using mul_le_mul hs1 hc1 hc0 (by norm_num : (0 : ℝ) ≤ 1)

theorem Gam_bounds (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ ∧ Work.Spaces.Gam α θ ≤ 1 := by
  have ht0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 :=
    (sin_mul_cos_sq_mem_Icc θ hθ).1
  have ht1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 :=
    (sin_mul_cos_sq_mem_Icc θ hθ).2
  have hα3 : 0 ≤ α / 3 := by linarith
  exact ⟨by rw [Gam]; exact Real.rpow_nonneg ht0 _,
    by rw [Gam]; exact Real.rpow_le_one ht0 ht1 hα3⟩

end Work.Spaces
