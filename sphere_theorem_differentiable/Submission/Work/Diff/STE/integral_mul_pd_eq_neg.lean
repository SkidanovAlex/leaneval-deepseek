import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integration by parts on the torus: `∫ f ∂ᵢg = -∫ (∂ᵢf) g`

For `f g : (ι → ℝ) → ℂ` of class `C¹` that are `1`-periodic in the coordinate `i`, the
`i`-th partial derivative may be moved from one factor to the other at the cost of a sign:

`∫_{unitCube} f · ∂ᵢg = - ∫_{unitCube} (∂ᵢf) · g`.

This is the cube-level form of Layer A's "periodic integration by parts".  The proof applies
the Leibniz rule (`pd_mul`) to the product `h = f · g`, notes that `h` is again `C¹` and
`1`-periodic in the `i`-th coordinate, and uses `integral_pd_unitCube_zero`:

`0 = ∫ ∂ᵢh = ∫ (∂ᵢf) · g + ∫ f · ∂ᵢg`,

which is the desired identity after rearranging.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

theorem integral_mul_pd_eq_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (f g : (ι → ℝ) → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : Work.Diff.STE.PeriodicIn i f) (hgp : Work.Diff.STE.PeriodicIn i g) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * Work.Diff.STE.pd i g x
      = - ∫ x in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.pd i f x * g x := by
  -- The product `h = f * g` is again `C¹` and periodic in the `i`-th coordinate.
  have hfg : ContDiff ℝ 1 (fun y : ι → ℝ => f y * g y) := hf.mul hg
  have hperp : PeriodicIn i (fun y : ι → ℝ => f y * g y) := by
    intro x
    show f (x + Pi.single i 1) * g (x + Pi.single i 1) = f x * g x
    rw [hfp x, hgp x]
  -- Leibniz rule: `∂ᵢ(f * g) = (∂ᵢf) * g + f * (∂ᵢg)`.
  have hpoint : ∀ x : ι → ℝ,
      pd i (fun y : ι → ℝ => f y * g y) x = pd i f x * g x + f x * pd i g x := by
    intro x
    rw [pd_mul i (hf.differentiable_one.differentiableAt) (hg.differentiable_one.differentiableAt)]
  -- Both summands are continuous, hence integrable on the unit cube.
  have h1 : Integrable (fun x : ι → ℝ => pd i f x * g x) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous ((continuous_pd hf i).mul hg.continuous)
  have h2 : Integrable (fun x : ι → ℝ => f x * pd i g x) (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous (hf.continuous.mul (continuous_pd hg i))
  -- The partial derivative of the periodic product integrates to zero.
  have hzero := integral_pd_unitCube_zero i hfg hperp
  simp_rw [hpoint] at hzero
  rw [integral_add h1 h2] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

end Work.Diff.STE
