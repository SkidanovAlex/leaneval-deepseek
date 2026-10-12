import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseFixB1S

/-- Expansion of the integral of a perfect square of a linear combination of two
continuous functions and a constant, in terms of the integrals of the six monomials.
This is the bilinearity of the integral (`f - c·g + d)² = f² - 2c fg + c²g² + 2d f - 2dc g + d²`
over the compact set `P`, whose volume is `volBox P`. -/
theorem integral_sq_sub_mul_add_const {P : Set ℝ³} (hK : IsCompact P) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (c d : ℝ) :
    (∫ x in P, (f x - c * g x + d) ^ 2)
      = (∫ x in P, (f x) ^ 2) - 2 * c * (∫ x in P, f x * g x)
        + c ^ 2 * (∫ x in P, (g x) ^ 2)
        + 2 * d * (∫ x in P, f x) - 2 * d * c * (∫ x in P, g x)
        + d ^ 2 * Work.BoseFixB1P.volBox P := by
  -- expand the integrand pointwise
  have key : (∫ x in P, (f x - c * g x + d) ^ 2)
      = ∫ x in P, ((f x) ^ 2 - (2 * c) * (f x * g x) + (c ^ 2) * (g x) ^ 2
          + (2 * d) * (f x) - (2 * d * c) * (g x) + d ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [key]
  -- integrability of each monomial (continuous on the compact set `P`)
  have hA : IntegrableOn (fun x => (f x) ^ 2) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hB : IntegrableOn (fun x => (2 * c) * (f x * g x)) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hC : IntegrableOn (fun x => (c ^ 2) * (g x) ^ 2) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hD : IntegrableOn (fun x => (2 * d) * (f x)) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hE : IntegrableOn (fun x => (2 * d * c) * (g x)) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hF : IntegrableOn (fun x => d ^ 2) P :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hAB : IntegrableOn (fun x => (f x) ^ 2 - (2 * c) * (f x * g x)) P := hA.sub hB
  have hABC : IntegrableOn
      (fun x => (f x) ^ 2 - (2 * c) * (f x * g x) + (c ^ 2) * (g x) ^ 2) P := hAB.add hC
  have hABCD : IntegrableOn
      (fun x => (f x) ^ 2 - (2 * c) * (f x * g x) + (c ^ 2) * (g x) ^ 2
        + (2 * d) * (f x)) P := hABC.add hD
  have hABCDE : IntegrableOn
      (fun x => (f x) ^ 2 - (2 * c) * (f x * g x) + (c ^ 2) * (g x) ^ 2
        + (2 * d) * (f x) - (2 * d * c) * (g x)) P := hABCD.sub hE
  -- additivity / homogeneity of the integral, peeled from the outside in
  rw [integral_add hABCDE hF]
  rw [integral_sub hABCD hE]
  rw [integral_add hABC hD]
  rw [integral_add hAB hC]
  rw [integral_sub hA hB]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [setIntegral_const, Work.BoseFixB1P.volBox, smul_eq_mul]
  ring

end Work.BoseFixB1S
