import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Submission.Work.BoseB4.Gauss_integrable
import Submission.Work.BoseB4.Gauss_moment
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.integrable_conj_cohWeight_mul_cohWeight` — integrability of a coherent-weight pair

The coherent weights `cw n z = z̄ⁿ/√(n!)` (`Coherent.cohWeight`) are elements of
`L²(ℂ, dν)`, `dν = e^{-|z|²}d²z/π` (`Coherent.gauss`): their pairwise products
`conj(cw n z) * cw m z` are integrable, with integral `δ_{nm}` (`Gauss_moment`).

The point is that `conj(cw n z) * cw m z` is a *polynomial* in `z` and `z̄`, namely
`zⁿ z̄ᵐ / (√(n!)√(m!))` (because `√(n!)` and `√(m!)` are real and positive), and
polynomials are integrable against the Gaussian measure (`Gauss_integrable`).

This integrability is exactly what lets one commute the integral with the finite sums
in the pointwise expansion of `⟪Phi Ψ z, Phi Ψ' z⟫`, i.e. it is the analytic input
of the Bargmann isometry (resolution of the identity) of FS §8.3.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Work.BoseB4

set_option autoImplicit false

/-- The coherent weight is `cw n z = z̄ⁿ/√(n!)` with a *real* denominator, so its
conjugate is `zⁿ/√(n!)`. -/
lemma conj_cohWeight_eq (n : ℕ) (z : ℂ) :
    starRingEnd ℂ (cohWeight n z) = z ^ n / sq n.factorial := by
  rw [cohWeight, map_div₀, map_pow]
  simp [sq, Complex.conj_ofReal]

/-- `conj(cw n z) * cw m z` in the polynomial form whose integrability is
`Gauss_integrable`: `zⁿ z̄ᵐ (√(n!)√(m!))⁻¹`. -/
lemma conj_cohWeight_mul_eq (n m : ℕ) (z : ℂ) :
    starRingEnd ℂ (cohWeight n z) * cohWeight m z
      = (z ^ n * (starRingEnd ℂ z) ^ m) * (sq n.factorial * sq m.factorial)⁻¹ := by
  rw [conj_cohWeight_eq, cohWeight, div_eq_mul_inv, div_eq_mul_inv]
  simp only [sq]
  ring

/-- **Integrability of a pair of coherent weights against the Gaussian measure.**
`conj(cw n ·) * cw m ·` is a polynomial in `z, z̄` times a constant, hence integrable
(`Gauss_integrable`). -/
theorem integrable_conj_cohWeight_mul_cohWeight (n m : ℕ) :
    MeasureTheory.Integrable
      (fun z : ℂ => (starRingEnd ℂ (Work.BoseB4.cohWeight n z)) * Work.BoseB4.cohWeight m z)
      Work.BoseB4.gauss := by
  have h := (Gauss_integrable n m).mul_const ((sq n.factorial * sq m.factorial)⁻¹)
  refine h.congr ?_
  filter_upwards with z
  exact (conj_cohWeight_mul_eq n m z).symm

end Work.BoseB4
