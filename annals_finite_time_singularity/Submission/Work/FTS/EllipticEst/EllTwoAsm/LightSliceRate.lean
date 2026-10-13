import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllTwoAsm.SliceRateLightAsm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllTwoAsm

open Filter

/-- If `f → c` at an endpoint where `f → 0` as well, then `c = 0`; this is the uniqueness of
limits for the one-sided filters `𝓝[Ioi 0] 0` and `𝓝[Iio (π/2)] (π/2)`. -/
theorem lightSliceRate_const_eq_zero_left {f : ℝ → ℝ} {c : ℝ}
    (h₁ : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c))
    (h₂ : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) : c = 0 :=
  tendsto_nhds_unique h₁ h₂

/-- The right-endpoint analogue of `lightSliceRate_const_eq_zero_left`. -/
theorem lightSliceRate_const_eq_zero_right {f : ℝ → ℝ} {c : ℝ}
    (h₁ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c))
    (h₂ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    c = 0 :=
  tendsto_nhds_unique h₁ h₂

theorem LightSliceRate : ∀ (a : ℝ), 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ),
      ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f θ) ^ 2 ≤ C * θ ^ (1 - a) *
            ∫ θ' in Set.Ioo (0 : ℝ) θ, (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a)
      ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f θ) ^ 2 ≤ C * (Real.pi / 2 - θ) ^ (1 - a) *
            ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a) := by
  intro a ha ha1
  obtain ⟨C, hCpos, hmain⟩ := SliceRateLightAsm a ha ha1
  refine ⟨C, hCpos, ?_⟩
  intro f hf hL hR hint
  obtain ⟨⟨cL, hcL, hbL⟩, ⟨cR, hcR, hbR⟩⟩ := hmain f hf hint
  have hcL0 : cL = 0 := lightSliceRate_const_eq_zero_left hcL hL
  have hcR0 : cR = 0 := lightSliceRate_const_eq_zero_right hcR hR
  refine ⟨?_, ?_⟩
  · intro θ hθ
    have h := hbL θ hθ
    rw [hcL0] at h
    simpa using h
  · intro θ hθ
    have h := hbR θ hθ
    rw [hcR0] at h
    simpa using h

end Work.FTS.EllipticEst.EllTwoAsm
