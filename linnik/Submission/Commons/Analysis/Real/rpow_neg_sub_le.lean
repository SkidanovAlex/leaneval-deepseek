import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Commons.Analysis.Real

theorem rpow_neg_sub_le {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ)^(-σ) - ((n:ℝ)+1)^(-σ) ≤ σ * (n:ℝ)^(-σ-1) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-σ)) (Set.Ici (n:ℝ)) := by
    refine (continuous_id.continuousOn).rpow_const (fun x hx => ?_)
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hnpos hx))
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ (-σ)) (interior (Set.Ici (n:ℝ))) := by
    rw [interior_Ici]
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hnpos hx.le
    exact (Real.differentiableAt_rpow_const_of_ne (-σ) (ne_of_gt hxpos)).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (n:ℝ)),
      -σ * (n:ℝ)^(-σ-1) ≤ deriv (fun x : ℝ => x ^ (-σ)) x := by
    intro x hx
    rw [interior_Ici] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hnpos hx.le
    have hz : -σ - 1 ≤ 0 := by linarith
    have hle : x ^ (-σ - 1) ≤ (n:ℝ) ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hnpos hx.le hz
    rw [Real.deriv_rpow_const]
    nlinarith [mul_le_mul_of_nonneg_left hle hσ.le]
  have key := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici (n : ℝ)) hcont hdiff
    (C := -σ * (n:ℝ)^(-σ-1)) hderiv (n:ℝ) (Set.mem_Ici.mpr le_rfl)
    ((n:ℝ)+1) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have key' : -σ * (n:ℝ)^(-σ-1) ≤ ((n:ℝ)+1)^(-σ) - (n:ℝ)^(-σ) := by
    simpa using key
  linarith

end Commons.Analysis.Real