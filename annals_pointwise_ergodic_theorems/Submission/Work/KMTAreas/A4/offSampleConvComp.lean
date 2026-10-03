/-
# The sampling estimate for the off-diagonal Ionescu--Wainger decomposition (component form)

`offSampleConvComp` combines the two elementary estimates of this directory:

* `offSample`: the `ℓ¹(ℤ)`-norm of the samples of a Schwartz function `f` is bounded by
  `C (‖f‖₁ + ‖f'‖₁)`;
* `offConvMoment`: `‖h - h ⋆ v‖₁ ≤ (∫ |y| ‖v y‖) ‖h'‖₁` for a normalised kernel `∫ v = 1`.

Applied to `f = h - h ⋆ v` the first estimate needs `‖(h - h ⋆ v)'‖₁`, which is the same moment
estimate applied to `h'` once one knows that the derivative commutes with the convolution,
`(h ⋆ v)' = h' ⋆ v` (`Work.KMTAreas.A4.derivCSEq`).  Hence the constant `1` works:

`∑_j ‖(h - h ⋆ v) j‖ ≤ (‖h - h ⋆ v‖₁ + ‖(h - h ⋆ v)'‖₁) ≤ (∫ |y| ‖v y‖) (‖h'‖₁ + ‖h''‖₁)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offSample
import Submission.Work.KMTAreas.A4.offConvMoment
import Submission.Work.KMTAreas.A4.derivCSEq

open MeasureTheory
open scoped BigOperators

namespace Work.KMTAreas.A4

theorem offSampleConvComp : ∃ C : ℝ, 0 < C ∧ ∀ (h v : SchwartzMap ℝ ℂ), (∫ y : ℝ, v y = 1) → ∑' j : ℤ, ‖(h - Work.KMTAreas.A4.cS h v) (j : ℝ)‖ ≤ C * (∫ y : ℝ, |y| * ‖v y‖) * ((∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖) + ∫ x : ℝ, ‖deriv (deriv (h : ℝ → ℂ)) x‖) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := offSample
  refine ⟨C₁, hC₁pos, ?_⟩
  intro h v hv
  set M : ℝ := ∫ y : ℝ, |y| * ‖v y‖
  set A : ℝ := ∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖
  set B : ℝ := ∫ x : ℝ, ‖deriv (deriv (h : ℝ → ℂ)) x‖
  -- the derivative of the convolution is the convolution of the derivative
  have hdse : SchwartzMap.derivCLM ℝ ℂ (cS h v) = cS (SchwartzMap.derivCLM ℝ ℂ h) v :=
    derivCSEq h v
  -- `(h - h ⋆ v)' = h' - h' ⋆ v`
  have hderiv : deriv (fun x : ℝ => (h - cS h v) x)
      = fun x : ℝ => (SchwartzMap.derivCLM ℝ ℂ h - cS (SchwartzMap.derivCLM ℝ ℂ h) v) x := by
    have hcoe : (fun x : ℝ => (h - cS h v) x) = ⇑h - ⇑(cS h v) := by
      funext y; simp
    have hdcoe : (fun x : ℝ => (SchwartzMap.derivCLM ℝ ℂ h
          - cS (SchwartzMap.derivCLM ℝ ℂ h) v) x)
        = ⇑(SchwartzMap.derivCLM ℝ ℂ h) - ⇑(cS (SchwartzMap.derivCLM ℝ ℂ h) v) := by
      funext y; simp
    rw [hcoe, hdcoe]
    funext x
    rw [deriv_sub h.differentiableAt (cS h v).differentiableAt]
    simp only [Pi.sub_apply]
    rw [← SchwartzMap.derivCLM_apply ℝ h x, ← SchwartzMap.derivCLM_apply ℝ (cS h v) x]
    rw [show ⇑(SchwartzMap.derivCLM ℝ ℂ (cS h v))
        = ⇑(cS (SchwartzMap.derivCLM ℝ ℂ h) v) from
      congrArg (fun w : SchwartzMap ℝ ℂ => (w : ℝ → ℂ)) hdse]
  -- first-order moment estimate for `h - h ⋆ v`
  have hI1 : (∫ x : ℝ, ‖(h - cS h v) x‖) ≤ M * A := by
    have hconv : (fun x : ℝ => ‖(h - cS h v) x‖)
        = fun x : ℝ => ‖h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x‖ := by
      funext x
      simp [cS, SchwartzMap.convolution_apply]
    rw [hconv]
    exact offConvMoment h v hv
  -- first-order moment estimate for the derivative `h' - h' ⋆ v`
  have hI2 : (∫ x : ℝ, ‖deriv (fun x : ℝ => (h - cS h v) x) x‖) ≤ M * B := by
    rw [hderiv]
    have hconv : (fun x : ℝ => ‖(SchwartzMap.derivCLM ℝ ℂ h
          - cS (SchwartzMap.derivCLM ℝ ℂ h) v) x‖)
        = fun x : ℝ => ‖(SchwartzMap.derivCLM ℝ ℂ h) x
            - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (SchwartzMap.derivCLM ℝ ℂ h) v x‖ := by
      funext x
      simp [cS, SchwartzMap.convolution_apply]
    rw [hconv]
    have hh : (∫ x : ℝ, ‖deriv (⇑(SchwartzMap.derivCLM ℝ ℂ h)) x‖) = B := by
      have hfun : ⇑(SchwartzMap.derivCLM ℝ ℂ h) = deriv (h : ℝ → ℂ) :=
        funext (fun x => SchwartzMap.derivCLM_apply ℝ h x)
      rw [hfun]
    rw [← hh]
    exact offConvMoment (SchwartzMap.derivCLM ℝ ℂ h) v hv
  calc ∑' j : ℤ, ‖(h - cS h v) (j : ℝ)‖
      ≤ C₁ * ((∫ x : ℝ, ‖(h - cS h v) x‖)
          + ∫ x : ℝ, ‖deriv (fun x : ℝ => (h - cS h v) x) x‖) := hC₁ _
    _ ≤ C₁ * (M * A + M * B) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₁pos)
        exact add_le_add hI1 hI2
    _ = C₁ * M * (A + B) := by ring

end Work.KMTAreas.A4
