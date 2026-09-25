import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_holderNorm_le

namespace Work.NN.Final

open MeasureTheory

/-- **`bmPot` is additive and `ℂ`-homogeneous on continuous compactly supported families.**  With
`Work.CR.Flat.Cauchy.bmPot f z = ∑ k, ∫ x, bmKernel k x * f k (z + x)` (a plain Bochner integral,
`Submission/Work/CR/Flat/Cauchy/bmSetup.lean`), the sum of integrals of an `L¹` kernel against
`f k` and `g k` splits whenever each term is integrable — which is supplied by
`integrable_bmKernel_mul` (`bmPotential_holderNorm_le.lean`) for continuous compactly supported
data.  This is the linearity of the Bochner–Martinelli potential needed to define the
`(0,2)`-solution operator as a `ℝ`-linear map. -/
theorem bmPot_linear {n : ℕ} (hn : 0 < n) (a b : ℂ) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    ∀ z : Fin n → ℂ,
      Work.CR.Flat.Cauchy.bmPot (fun j => fun y => a * f j y + b * g j y) z
        = a * Work.CR.Flat.Cauchy.bmPot f z + b * Work.CR.Flat.Cauchy.bmPot g z := by
  intro z
  -- Integrability of each term of both potentials, the translation of the compactly supported
  -- continuous data being again continuous with compact support.
  have int_f : ∀ j : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x)) := fun j =>
    Work.CR.Flat.Cauchy.integrable_bmKernel_mul hn j
      ((hf j).comp (continuous_const.add continuous_id))
      ((hfs j).comp_homeomorph (Homeomorph.addLeft z))
  have int_g : ∀ j : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x)) := fun j =>
    Work.CR.Flat.Cauchy.integrable_bmKernel_mul hn j
      ((hg j).comp (continuous_const.add continuous_id))
      ((hgs j).comp_homeomorph (Homeomorph.addLeft z))
  simp only [Work.CR.Flat.Cauchy.bmPot]
  trans ∑ j : Fin n, (a * (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
      + b * ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x))
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j x
          * (a * f j (z + x) + b * g j (z + x)))
        = fun x : Fin n → ℂ =>
            a * (Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
              + b * (Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x)) from by
      funext x; ring]
    rw [MeasureTheory.integral_add ((int_f j).const_mul a) ((int_g j).const_mul b),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end Work.NN.Final
