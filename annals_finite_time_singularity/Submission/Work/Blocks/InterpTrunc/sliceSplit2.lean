import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-- The elementary Young-type splitting behind `sliceSplit2`:

`(a + b)² ≤ (1 + L)·a² + (1 + 1/L)·b²` for `L > 0`.

It is the pointwise statement, valid in any field, that the difference of the two sides
equals `(1/L)·(L·a - b)² ≥ 0`. -/
private lemma sq_add_le_young {a b L : ℝ} (hL : 0 < L) :
    (a + b) ^ 2 ≤ (1 + L) * a ^ 2 + (1 + 1 / L) * b ^ 2 := by
  have hkey : (1 + L) * a ^ 2 + (1 + 1 / L) * b ^ 2 - (a + b) ^ 2
      = (1 / L) * (L * a - b) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ (1 / L) * (L * a - b) ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (le_of_lt hL)) (sq_nonneg _)
  linarith

/-- **Splitting a slice `L²`-integral of a sum.**  For two functions continuous on the
angular interval `Iθ` and any `L > 0`,

`∫_θ (A + B)² σ ≤ (1 + L)·∫_θ A² σ + (1 + 1/L)·∫_θ B² σ`,  `σ = sin(2θ)^{-η}`.

The inequality is pointwise (`(a+b)² ≤ (1+L)a² + (1+1/L)b²`, the Young splitting with
weights `√(L a)` and `b/√L`), multiplied by the nonnegative weight `σ` and integrated.
Integrability of the three integrands on `Iθ` is `integrable_slice_sq_mul_thEta`
(`σ` is integrable on the compact interval and a continuous function is bounded there). -/
theorem sliceSplit2 {A B : ℝ → ℝ} (hA : ContinuousOn A Work.Spaces.Iθ)
    (hB : ContinuousOn B Work.Spaces.Iθ) {L : ℝ} (hL : 0 < L) :
    (∫ θ in Work.Spaces.Iθ, (A θ + B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ (1 + L) * (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + (1 + 1 / L) * (∫ θ in Work.Spaces.Iθ, (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hIA : Integrable (fun θ => (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta hA
  have hIB : Integrable (fun θ => (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta hB
  have hIAB : Integrable (fun θ => (A θ + B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta (hA.add hB)
  have hIY : Integrable (fun θ => (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      + (1 + 1 / L) * ((B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (volume.restrict Work.Spaces.Iθ) :=
    (hIA.const_mul (1 + L)).add (hIB.const_mul (1 + 1 / L))
  calc (∫ θ in Work.Spaces.Iθ, (A θ + B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (1 + 1 / L) * ((B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
        refine setIntegral_mono_on hIAB hIY measurableSet_Icc (fun θ hθ => ?_)
        have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have hpt : (A θ + B θ) ^ 2 ≤ (1 + L) * (A θ) ^ 2 + (1 + 1 / L) * (B θ) ^ 2 :=
          sq_add_le_young hL
        calc (A θ + B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ ((1 + L) * (A θ) ^ 2 + (1 + 1 / L) * (B θ) ^ 2)
                * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right hpt hσ
          _ = (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                + (1 + 1 / L) * ((B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
    _ = (1 + L) * (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + (1 + 1 / L) * (∫ θ in Work.Spaces.Iθ, (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        rw [integral_add (hIA.const_mul (1 + L)) (hIB.const_mul (1 + 1 / L)),
          integral_const_mul, integral_const_mul]

end Work.Blocks.InterpTrunc
