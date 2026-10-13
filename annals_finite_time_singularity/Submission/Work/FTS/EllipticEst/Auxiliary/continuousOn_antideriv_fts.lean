import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.exists_bound_div_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Real
open Filter

namespace Work.FTS.EllipticEst.Auxiliary

theorem continuousOn_antideriv_fts (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h1 : f (π / 2) = 0) :
    ContinuousOn (fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * f θ
      + (1 / 2) * Real.tan θ * (f θ) ^ 2) (Set.Icc 0 (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := Real.pi_div_two_pos
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpi
  have hderiv : ContinuousOn (derivWithin f (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
    hs.continuousOn_derivWithin hU (by norm_num)
  have hf : ContinuousOn f (Set.Icc 0 (π / 2)) := hs.continuousOn
  have hA : ContinuousOn (fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * f θ)
      (Set.Icc 0 (π / 2)) := hderiv.neg.mul hf
  obtain ⟨C, _hC0, hCb⟩ :=
    Work.FTS.EllipticEst.exists_bound_div_cos f hs h1
  have htan_id : ∀ θ : ℝ,
      Real.tan θ * (f θ) ^ 2 = Real.sin θ * (f θ / Real.cos θ) * f θ := by
    intro θ
    rw [Real.tan_eq_sin_div_cos]
    ring
  have hmem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_of_lt hpi, le_refl _⟩
  have hB : ContinuousOn (fun θ => (1 / 2) * Real.tan θ * (f θ) ^ 2)
      (Set.Icc 0 (π / 2)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with hxeq | hxlt
    · -- endpoint `x = π/2`: the factor `tan θ * f θ²` is squeezed by `f θ → 0`
      rw [hxeq, ContinuousWithinAt]
      rw [show (1 / 2) * Real.tan (π / 2) * (f (π / 2)) ^ 2 = 0 by simp [h1]]
      have hbound : Tendsto (fun θ => (1 / 2) * C * |f θ|)
          (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
        have hft : Tendsto f (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
          have h := (hf.continuousWithinAt hmem).tendsto
          rwa [h1] at h
        simpa using hft.abs.const_mul ((1 / 2) * C)
      refine squeeze_zero_norm' (a := fun θ => (1 / 2) * C * |f θ|) ?_ hbound
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        rw [Real.norm_eq_abs]
        have hb : |Real.tan θ * (f θ) ^ 2| ≤ C * |f θ| := by
          rw [htan_id θ, abs_mul, abs_mul]
          calc |Real.sin θ| * |f θ / Real.cos θ| * |f θ|
              ≤ 1 * C * |f θ| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul (Real.abs_sin_le_one θ) (hCb θ hθ)
                    (abs_nonneg _) (by norm_num))
                  (abs_nonneg _)
            _ = C * |f θ| := by ring
        calc |(1 / 2) * Real.tan θ * (f θ) ^ 2|
            = (1 / 2) * |Real.tan θ * (f θ) ^ 2| := by
              rw [show (1 / 2) * Real.tan θ * (f θ) ^ 2
                    = (1 / 2) * (Real.tan θ * (f θ) ^ 2) by ring,
                abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ ≤ (1 / 2) * (C * |f θ|) := mul_le_mul_of_nonneg_left hb (by norm_num)
          _ = (1 / 2) * C * |f θ| := by ring
    · -- interior point: `tan` is continuous there
      have hcos : Real.cos x ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, hpi], hxlt⟩)
      have htan : ContinuousWithinAt Real.tan (Set.Icc 0 (π / 2)) x :=
        (Real.continuousAt_tan.mpr hcos).continuousWithinAt
      have hfx : ContinuousWithinAt f (Set.Icc 0 (π / 2)) x := hf x hx
      exact ((continuousWithinAt_const (b := (1 / 2))).mul htan).mul (hfx.pow 2)
  exact hA.add hB

end Work.FTS.EllipticEst.Auxiliary
