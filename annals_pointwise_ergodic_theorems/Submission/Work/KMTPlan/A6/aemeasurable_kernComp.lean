import Mathlib
import Submission.Work.A7.ModelApproxCore_aux.kernComp_eq_tsum

namespace Work.KMTPlan.A6

open MeasureTheory

/-- Measurability in `t` of the composed kernel `kernComp K (κ t) (κ' t)`, given that all the
`t`-sections of `κ` and `κ'` are a.e. measurable.  The iterated sum defining `kernComp` is a
countable `tsum` of the a.e. measurable functions
`t ↦ K (a - a') (b - b') * κ t a' * κ' t b'`, so `AEMeasurable.tsum` (twice) applies.

The hypotheses `hK`, `hκ`, `hκ'` (absolute convergence of the kernel and of the two families at
each `t ∈ (1/2, 1]`) are not needed for measurability; they are part of the statement as requested
so that the lemma can be applied in the same context as the summability facts it accompanies. -/
theorem aemeasurable_kernComp (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ) (a b : ℤ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hκ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ t j‖)
    (hκ' : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ' t j‖)
    (hmκ : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ t j) volume)
    (hmκ' : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ' t j) volume) :
    AEMeasurable (fun t : ℝ => Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
  unfold Work.KMTAreas.A7.kernComp
  have h : AEMeasurable (fun t : ℝ =>
      ∑' a' : ℤ, ∑' b' : ℤ, K (a - a') (b - b') * κ t a' * κ' t b') volume := by
    refine AEMeasurable.tsum (fun a' => ?_)
    refine AEMeasurable.tsum (fun b' => ?_)
    exact (aemeasurable_const.mul (hmκ a')).mul (hmκ' b')
  exact h.restrict

end Work.KMTPlan.A6
