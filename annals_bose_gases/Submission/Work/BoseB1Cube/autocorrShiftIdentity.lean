import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

/-- The autocorrelation identity at a shift `z`, in the "one integral moved" form:
`∫ f(x) f(x-z) = ∫ f² - (1/2) ∫ (f(x+z) - f(x))²`.

Proof: expand the square
`∫ (f(x+z) - f(x))² = ∫ f(x+z)² - 2 ∫ f(x+z) f(x) + ∫ f(x)²`,
use the translation-invariance of Lebesgue measure to replace `∫ f(x+z)²` by `∫ f(x)²`,
and finally replace `∫ f(x+z) f(x)` by `∫ f(x) f(x-z)` (the substitution `x ↦ x + z`). -/
theorem autocorrShiftIdentity {f : EuclideanSpace ℝ (Fin 3) → ℝ} {z : EuclideanSpace ℝ (Fin 3)}
    (h2 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => f x ^ 2))
    (h2z : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => f (x + z) ^ 2))
    (hc : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => f (x + z) * f x)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), f x * f (x - z))
      = (∫ x : EuclideanSpace ℝ (Fin 3), f x ^ 2)
        - (1 / 2) * ∫ x : EuclideanSpace ℝ (Fin 3), (f (x + z) - f x) ^ 2 := by
  -- Substitution `x ↦ x + z` (translation invariance of the Lebesgue measure).
  have hshift : (∫ x : EuclideanSpace ℝ (Fin 3), f x * f (x - z))
      = ∫ x : EuclideanSpace ℝ (Fin 3), f (x + z) * f x := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun x : EuclideanSpace ℝ (Fin 3) => f x * f (x - z)) z
    simpa using h.symm
  -- Expansion of the square, together with the translation invariance of `∫ f²`.
  have hexp : (∫ x : EuclideanSpace ℝ (Fin 3), (f (x + z) - f x) ^ 2)
      = 2 * (∫ x : EuclideanSpace ℝ (Fin 3), f x ^ 2)
        - 2 * (∫ x : EuclideanSpace ℝ (Fin 3), f (x + z) * f x) := by
    have h1 : (∫ x : EuclideanSpace ℝ (Fin 3), (f (x + z) - f x) ^ 2)
        = ∫ x : EuclideanSpace ℝ (Fin 3),
            (f (x + z) ^ 2 - 2 * (f (x + z) * f x) + f x ^ 2) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    have h2' : (∫ x : EuclideanSpace ℝ (Fin 3),
            (f (x + z) ^ 2 - 2 * (f (x + z) * f x) + f x ^ 2))
        = (∫ x : EuclideanSpace ℝ (Fin 3), (f (x + z) ^ 2 - 2 * (f (x + z) * f x)))
          + (∫ x : EuclideanSpace ℝ (Fin 3), f x ^ 2) :=
      integral_add (h2z.sub (hc.const_mul 2)) h2
    have h3 : (∫ x : EuclideanSpace ℝ (Fin 3), (f (x + z) ^ 2 - 2 * (f (x + z) * f x)))
        = (∫ x : EuclideanSpace ℝ (Fin 3), f (x + z) ^ 2)
          - (∫ x : EuclideanSpace ℝ (Fin 3), 2 * (f (x + z) * f x)) :=
      integral_sub h2z (hc.const_mul 2)
    have h4 : (∫ x : EuclideanSpace ℝ (Fin 3), 2 * (f (x + z) * f x))
        = 2 * (∫ x : EuclideanSpace ℝ (Fin 3), f (x + z) * f x) :=
      integral_const_mul 2 (fun x : EuclideanSpace ℝ (Fin 3) => f (x + z) * f x)
    have h5 : (∫ x : EuclideanSpace ℝ (Fin 3), f (x + z) ^ 2)
        = ∫ x : EuclideanSpace ℝ (Fin 3), f x ^ 2 :=
      integral_add_right_eq_self (μ := volume)
        (fun x : EuclideanSpace ℝ (Fin 3) => f x ^ 2) z
    rw [h1, h2', h3, h4, h5]
    ring
  rw [hshift, hexp]
  ring

end Work.BoseB1Cube
