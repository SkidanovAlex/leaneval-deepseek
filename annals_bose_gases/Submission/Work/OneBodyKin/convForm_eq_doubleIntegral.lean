import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

open MeasureTheory

/-- **The convolution form of the one-body energy equals the double integral.**

For real functions `k, ψ` on `ℝ³`,

    `∫∫ k(x−y) ψ(x) ψ(y) dx dy = ∫ (k ⋆ ψ)(x) · ψ(x) dx`,

where `k ⋆ ψ` is Mathlib's convolution against Lebesgue measure with the pointwise product
`ContinuousLinearMap.mul ℂ ℂ` as the bilinear operation (both sides are read as complex numbers).
The identity is unconditional in `k` and `ψ`: no integrability hypothesis is needed, because
Mathlib's Bochner integral is linear over constants (`integral_const_mul`) and the complex
casting commutes with the integral (`integral_complex_ofReal`). -/
theorem convForm_eq_doubleIntegral (k ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    ((∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
        k (x - y) * ψ x * ψ y : ℝ) : ℂ)
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          MeasureTheory.convolution (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ))
              (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ))
              (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume x *
            (ψ x : ℂ) := by
  -- Evaluate the convolution at a point: it is the cast of the real inner integral `∫ y, k (x-y) * ψ y`.
  have hconv : ∀ x, MeasureTheory.convolution (fun z => (k z : ℂ)) (fun z => (ψ z : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume x
        = (((∫ y, k (x - y) * ψ y : ℝ)) : ℂ) := by
    intro x
    rw [convolution_mul_swap]
    have h : (fun t => (k (x - t) : ℂ) * (ψ t : ℂ))
           = (fun t => ((k (x - t) * ψ t : ℝ) : ℂ)) := by
      funext t; exact (Complex.ofReal_mul _ _).symm
    rw [h, integral_complex_ofReal]
  -- Pull the constant `ψ x` out of the inner real integral.
  have hinner : ∀ x, (∫ y, k (x - y) * ψ x * ψ y)
        = (∫ y, k (x - y) * ψ y) * ψ x := by
    intro x
    have h : (fun y => k (x - y) * ψ x * ψ y)
           = (fun y => ψ x * (k (x - y) * ψ y)) := by
      funext y; ring
    rw [h, integral_const_mul, mul_comm]
  -- Both sides reduce to `∫ x, (∫ y, k (x-y) * ψ y) * ψ x`, cast to `ℂ`.
  have hL : (∫ x, ∫ y, k (x - y) * ψ x * ψ y)
        = ∫ x, (∫ y, k (x - y) * ψ y) * ψ x :=
    integral_congr_ae (Filter.Eventually.of_forall hinner)
  have hR : (∫ x, MeasureTheory.convolution (fun z => (k z : ℂ)) (fun z => (ψ z : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume x * (ψ x : ℂ))
        = ((∫ x, (∫ y, k (x - y) * ψ y) * ψ x : ℝ) : ℂ) := by
    have h : (fun x => MeasureTheory.convolution (fun z => (k z : ℂ)) (fun z => (ψ z : ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume x * (ψ x : ℂ))
        = (fun x => (((∫ y, k (x - y) * ψ y) * ψ x : ℝ) : ℂ)) := by
      funext x
      rw [hconv x]
      exact (Complex.ofReal_mul _ _).symm
    rw [h, integral_complex_ofReal]
  rw [hL, hR]

end Work.OneBodyKin
