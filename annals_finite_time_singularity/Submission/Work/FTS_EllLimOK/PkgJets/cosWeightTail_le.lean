import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailA
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The `cos`-weight tail estimate

For `T ∈ (0, π/2)` we bound the product

`(∫ s in T..π/2, cos(s)² sin(2s)^η) * (∫ s in 0..T, sin(2s)^{-η} / cos(s)^4)`

uniformly in `T`, where `η = Work.Spaces.eta = 99/100`.

Both factors degenerate near the endpoint `s = π/2` (the first tends to `0`, the second blows
up) and the two degeneracies cancel: with `δ = π/2 - T`,

* `∫ s in T..π/2, cos(s)² sin(2s)^η ≤ 2^η δ^{3+η}`   (`cosTailA`),
* `∫ s in 0..T, sin(2s)^{-η}/cos(s)^4 ≤ C₂ δ^{-(3+η)}`   (`cosTailB`),
* and `δ^{3+η} · δ^{-(3+η)} = 1` for `δ > 0`.

So the product is bounded by the constant `2^η · C₂`.
-/

/-- Assembly: the two one-sided estimates `hA`, `hB` for the two factors give the uniform
bound on their product.  Stated with the literal `99/100` (definitionally equal to
`Work.Spaces.eta`) so that it is exactly the shape of the two component lemmas. -/
private theorem cosWeightTail_le_aux (C₂ : ℝ) (hC₂pos : 0 < C₂)
    (hA : ∀ T : ℝ, T ∈ Set.Ioo 0 (Real.pi / 2) →
      (∫ s in T..(Real.pi / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ))
        ≤ (2 : ℝ) ^ (99 / 100 : ℝ) * (Real.pi / 2 - T) ^ (3 + 99 / 100 : ℝ))
    (hB : ∀ T : ℝ, T ∈ Set.Ioo 0 (Real.pi / 2) →
      (∫ s in (0 : ℝ)..T, (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) / (Real.cos s) ^ (4 : ℕ))
        ≤ C₂ * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, T ∈ Set.Ioo 0 (π / 2) →
      (∫ s in T..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * (∫ s in (0 : ℝ)..T,
            (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4) ≤ C := by
  refine ⟨(2 : ℝ) ^ Work.Spaces.eta * C₂,
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC₂pos, ?_⟩
  intro T hT
  have hδ : 0 < π / 2 - T := sub_pos.mpr hT.2
  have hI2nn : 0 ≤ ∫ s in (0 : ℝ)..T,
      (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4 := by
    apply intervalIntegral.integral_nonneg (le_of_lt hT.1)
    intro s hs
    have hsin : 0 ≤ Real.sin (2 * s) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hs.1], by linarith [hs.2, hT.2]⟩
    exact div_nonneg (Real.rpow_nonneg hsin _) (by positivity)
  have h1 := hA T hT
  have h2 := hB T hT
  have hkey : (π / 2 - T) ^ (3 + Work.Spaces.eta)
      * (π / 2 - T) ^ (-(3 + Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hδ]
    simp
  calc (∫ s in T..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * (∫ s in (0 : ℝ)..T,
            (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4)
      ≤ ((2 : ℝ) ^ Work.Spaces.eta * (π / 2 - T) ^ (3 + Work.Spaces.eta))
        * (∫ s in (0 : ℝ)..T,
            (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4) :=
        mul_le_mul_of_nonneg_right h1 hI2nn
    _ ≤ ((2 : ℝ) ^ Work.Spaces.eta * (π / 2 - T) ^ (3 + Work.Spaces.eta))
        * (C₂ * (π / 2 - T) ^ (-(3 + Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left h2
          (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hδ _)).le
    _ = (2 : ℝ) ^ Work.Spaces.eta * C₂ := by
        rw [show ((2 : ℝ) ^ Work.Spaces.eta * (π / 2 - T) ^ (3 + Work.Spaces.eta))
              * (C₂ * (π / 2 - T) ^ (-(3 + Work.Spaces.eta)))
            = (2 : ℝ) ^ Work.Spaces.eta * C₂
              * ((π / 2 - T) ^ (3 + Work.Spaces.eta)
                  * (π / 2 - T) ^ (-(3 + Work.Spaces.eta)))
            from by ring, hkey, mul_one]

theorem cosWeightTail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, T ∈ Set.Ioo 0 (π / 2) →
      (∫ s in T..(π / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * (∫ s in (0 : ℝ)..T,
            (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) / (Real.cos s) ^ 4) ≤ C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := cosTailB
  exact cosWeightTail_le_aux C₂ hC₂pos cosTailA hC₂

end Work.FTS_EllLimOK.PkgJets
