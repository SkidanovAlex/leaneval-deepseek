/-
# The clean contour set of `straightPart`

`Work.Asymptotics.straightPart` is the CKMRV contour integral along the positive imaginary axis
with the two intervals around the coincidence heights `t₀` and `t₀⁻¹` deleted.  This file collects
the set-theoretic bookkeeping for that deleted set, so that the analytic lemmas about
`straightPart` can be stated and proved without unfolding its definition.
-/
import Mathlib
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.Holomorphy

noncomputable section

namespace Work.Asymptotics

open MeasureTheory

/-- The set of contour heights `t` on which `straightPart` integrates: the positive imaginary
axis with the open intervals `(t₀-A₁, t₀+A₁)` and `(t₀⁻¹-A₂, t₀⁻¹+A₂)` deleted.  These are
exactly the intervals on which the contour of `K(τ,·)` may meet the pole `z = τ - 1` (height
`t = Im τ`) or the removable coincidence `z = -1/(τ-1)` (height `1/Im τ`). -/
def straightPartSet (t₀ A₁ A₂ : ℝ) : Set ℝ :=
  Set.Ioi (0 : ℝ) \
    (Set.Ioo (t₀ - A₁) (t₀ + A₁) ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))

lemma measurableSet_straightPartSet (t₀ A₁ A₂ : ℝ) :
    MeasurableSet (straightPartSet t₀ A₁ A₂) := by
  unfold straightPartSet
  measurability

@[simp] lemma mem_straightPartSet {t₀ A₁ A₂ t : ℝ} :
    t ∈ straightPartSet t₀ A₁ A₂ ↔
      0 < t ∧ t ∉ Set.Ioo (t₀ - A₁) (t₀ + A₁) ∧ t ∉ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) := by
  simp only [straightPartSet, Set.mem_diff, Set.mem_Ioi, Set.mem_union, not_or]

lemma straightPartSet_subset_Ioi (t₀ A₁ A₂ : ℝ) :
    straightPartSet t₀ A₁ A₂ ⊆ Set.Ioi (0 : ℝ) := fun t ht => (mem_straightPartSet.mp ht).1

/-- `straightPart` is the contour integral over the clean set. -/
lemma straightPart_eq_integral (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ A₂ : ℝ)
    (τ : UpperHalfPlane) :
    straightPart ℓ d r t₀ A₁ A₂ τ
      = ∫ t in straightPartSet t₀ A₁ A₂,
          contourIntegrand (Work.Kernels.Kfun ℓ d) r (τ : ℂ) t := by
  simp only [straightPart, straightPartSet, contourIntegrand, contourKernel,
    UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos, gaussWeight]

/-- The complex form of the previous identity, on the upper half plane. -/
lemma straightPart_eq_integral_ofComplex (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (r t₀ A₁ A₂ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    straightPart ℓ d r t₀ A₁ A₂ (UpperHalfPlane.ofComplex z)
      = ∫ t in straightPartSet t₀ A₁ A₂,
          contourIntegrand (Work.Kernels.Kfun ℓ d) r z t := by
  rw [straightPart_eq_integral]
  have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
  rw [hcoe]

end Work.Asymptotics
