import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

theorem angIbpPrimBoundary (p : ℝ) (g : ℝ → ℝ) :
    (Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ
        - p * Real.cot (2 * θ) * (g θ) ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun θ => g θ * deriv g θ * (Real.sin (2 * θ)) ^ p
        - p * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (p - 1) * (g θ) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ
        - p * Real.cot (2 * θ) * (g θ) ^ 2)) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      Filter.Tendsto (fun θ => g θ * deriv g θ * (Real.sin (2 * θ)) ^ p
        - p * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (p - 1) * (g θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- A neighbourhood of `0` inside the right half-line on which `sin (2 * θ) > 0`.
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
    have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Filter.mem_inf_of_left (Iio_mem_nhds hpi2)
    have h3 := Filter.inter_mem h1 h2
    have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioi 0 ∩ Set.Iio (Real.pi / 2) := by
      ext x; simp [Set.Ioo, Set.Ioi, Set.Iio]
    rwa [hIoo]
  -- A neighbourhood of `π / 2` inside the left half-line on which `sin (2 * θ) > 0`.
  have hmem1 : Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      self_mem_nhdsWithin
    have h2 : Set.Ioi (Real.pi / 2 - 1) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      Filter.mem_inf_of_left (Ioi_mem_nhds (by linarith))
    have h3 := Filter.inter_mem h2 h1
    have hIoo : Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2)
        = Set.Ioi (Real.pi / 2 - 1) ∩ Set.Iio (Real.pi / 2) := by
      ext x; simp [Set.Ioo, Set.Ioi, Set.Iio]
    rwa [hIoo]
  -- The two integrands agree wherever `sin (2 * θ) > 0`, by `sin^p * cot = cos * sin^{p-1}`.
  have key : ∀ θ : ℝ, 0 < 2 * θ → 2 * θ < Real.pi →
      (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ - p * Real.cot (2 * θ) * (g θ) ^ 2)
      = g θ * deriv g θ * (Real.sin (2 * θ)) ^ p
        - p * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (p - 1) * (g θ) ^ 2 := by
    intro θ h1 h2
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    have hrpow : Real.sin (2 * θ) ^ p * Real.cot (2 * θ)
        = Real.cos (2 * θ) * Real.sin (2 * θ) ^ (p - 1) := by
      rw [Real.cot_eq_cos_div_sin, Real.rpow_sub_one (ne_of_gt hsin) p]
      ring
    have hexp : (Real.sin (2 * θ)) ^ p * (g θ * deriv g θ - p * Real.cot (2 * θ) * (g θ) ^ 2)
        = Real.sin (2 * θ) ^ p * (g θ * deriv g θ)
          - p * (Real.sin (2 * θ) ^ p * Real.cot (2 * θ)) * (g θ) ^ 2 := by
      ring
    rw [hexp, hrpow]
    ring
  constructor
  · intro h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [hmem0] with θ hθ
    exact key θ (by linarith [hθ.1]) (by linarith [hθ.2])
  · intro h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [hmem1] with θ hθ
    exact key θ (by linarith [hθ.1, Real.pi_gt_three]) (by linarith [hθ.2])

end Work.FTS.EllipticEst.Prop
