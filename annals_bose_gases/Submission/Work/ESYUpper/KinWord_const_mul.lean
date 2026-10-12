import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ESYUpper.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

namespace Work.ESYUpper

/-- `fderiv` of a constant multiple of a scalar-valued function: the identity
`fderiv (s * f) x = s • fderiv f x` holds **without any differentiability
hypothesis** on `f`.  Indeed Mathlib's `fderiv_const_mul` covers the
differentiable case, while if `f` is not differentiable at `x` and `s ≠ 0` then
`s * f` is not differentiable there either (as `f = s⁻¹ • (s * f)`), so both
sides vanish; if `s = 0` then `s * f` is the zero function. -/
lemma fderiv_const_mul_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (f : E → ℝ) (x : E) :
    fderiv ℝ (fun y => s * f y) x = s • fderiv ℝ f x := by
  by_cases hd : DifferentiableAt ℝ f x
  · exact fderiv_const_mul hd s
  · rw [fderiv_zero_of_not_differentiableAt hd, smul_zero]
    rcases eq_or_ne s 0 with hs | hs
    · subst hs
      have : (fun y => (0 : ℝ) * f y) = Function.const _ (0 : ℝ) := by
        funext y; simp
      rw [this, fderiv_const]; simp
    · refine fderiv_zero_of_not_differentiableAt ?_
      intro hc
      apply hd
      have hff : f = fun y => s⁻¹ * (s * f y) := by
        funext y; rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      rw [hff]
      exact hc.const_mul s⁻¹

theorem KinWord_const_mul (N : ℕ) (ℓ s : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.kinWord N ℓ (fun x => s * Φ x)
      = s ^ 2 * Submission.BoseGases.kinWord N ℓ Φ := by
  unfold Submission.BoseGases.kinWord
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  have hpt : ∀ x : Submission.BoseGases.X N,
      fderiv ℝ (fun x => s * Φ x) x (Submission.BoseGases.kcDir N i k)
        = s * fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k) := by
    intro x
    rw [fderiv_const_mul_gen s Φ x]
    rfl
  simp_rw [hpt]
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        (s * fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          s ^ 2 * (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2 from by
        apply integral_congr_ae; filter_upwards with x; ring]
  rw [MeasureTheory.integral_const_mul]

end Work.ESYUpper
