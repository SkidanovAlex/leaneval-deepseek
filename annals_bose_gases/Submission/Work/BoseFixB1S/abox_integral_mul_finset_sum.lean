import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.CentreBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Linearity of the `abox` (set) integral in a finite sum

`∫ x in abox N ℓ, g x * (∑ i ∈ s, c i * f i x) = ∑ i ∈ s, c i * ∫ x in abox N ℓ, g x * f i x`

This is the standard finite-linearity statement for the Bochner integral restricted to the
`N`-particle centred box `abox N ℓ`, in the exact shape needed by the box-word expansion
downstream: the scalar weights `c i` are pulled out of the integral and the integral is
exchanged with the finite sum `∑ i ∈ s`.

The only hypothesis is integrability on `abox N ℓ` of each of the *unweighted* products
`g · f i`; integrability of `g · (c i · f i)` then follows from `Integrable.const_mul`.

The import of `Submission.CentreBox` (rather than a heavier module) is deliberate: it supplies
`Submission.BoseGases.X` and `Submission.BoseGases.abox` and nothing else is needed.
-/

namespace Work.BoseFixB1S

theorem abox_integral_mul_finset_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    (g : Submission.BoseGases.X N → ℝ)
    (c : ι → ℝ) (f : ι → Submission.BoseGases.X N → ℝ)
    (hint : ∀ i ∈ s, MeasureTheory.IntegrableOn (fun x => g x * f i x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, g x * (∑ i ∈ s, c i * f i x))
      = ∑ i ∈ s, c i * ∫ x in Submission.BoseGases.abox N ℓ, g x * f i x := by
  classical
  -- peel the factor `g x` into the finite sum (`Finset.mul_sum`)
  simp_rw [Finset.mul_sum]
  -- exchange the (restricted) Bochner integral with the finite sum
  rw [MeasureTheory.integral_finsetSum]
  · -- each summand: pull the scalar `c i` out of the integral
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (fun x => g x * (c i * f i x)) = fun x => c i * (g x * f i x) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul]
  · -- integrability of the weighted summands
    intro i hi
    convert (hint i hi).const_mul (c i) using 1
    ext x; ring

end Work.BoseFixB1S
