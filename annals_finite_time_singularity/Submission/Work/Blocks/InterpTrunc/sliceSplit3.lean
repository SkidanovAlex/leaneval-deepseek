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

/-- The elementary Young-type splitting behind `sliceSplit3`:

`(a + b + c)² ≤ (1 + 1/L)·c² + 2·(1 + L)·(a² + b²)` for `L > 0`.

The difference of the two sides equals `(1/L)·(c - L·(a+b))² + (1+L)·(a-b)² ≥ 0`, so the
statement is a pure field identity plus nonnegativity of squares. -/
private lemma sq3_le_young {a b c L : ℝ} (hL : 0 < L) :
    (a + b + c) ^ 2 ≤ (1 + 1 / L) * c ^ 2 + 2 * (1 + L) * (a ^ 2 + b ^ 2) := by
  have hkey : (1 + 1 / L) * c ^ 2 + 2 * (1 + L) * (a ^ 2 + b ^ 2) - (a + b + c) ^ 2
      = (1 / L) * (c - L * (a + b)) ^ 2 + (1 + L) * (a - b) ^ 2 := by
    field_simp
    ring
  have h1 : 0 ≤ (1 / L) * (c - L * (a + b)) ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (le_of_lt hL)) (sq_nonneg _)
  have h2 : 0 ≤ (1 + L) * (a - b) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- **Splitting a slice `L²`-integral of a sum of three functions.**  For three functions
continuous on the angular interval `Iθ` and any `L > 0`,

`∫_θ (A + B + C)² σ ≤ (1 + 1/L)·∫_θ C² σ + 2·(1+L)·(∫_θ A² σ + ∫_θ B² σ)`,
`σ = sin(2θ)^{-η}`.

The inequality is pointwise (`(c + (a+b))² ≤ (1 + 1/L)c² + (1+L)(a+b)²` together with
`(a+b)² ≤ 2(a²+b²)`), multiplied by the nonnegative weight `σ` and integrated.
Integrability of the integrands on `Iθ` is `integrable_slice_sq_mul_thEta`
(`σ` is integrable on the compact interval and a continuous function is bounded there). -/
theorem sliceSplit3 {A B C : ℝ → ℝ} (hA : ContinuousOn A Work.Spaces.Iθ)
    (hB : ContinuousOn B Work.Spaces.Iθ) (hC : ContinuousOn C Work.Spaces.Iθ) {L : ℝ}
    (hL : 0 < L) :
    (∫ θ in Work.Spaces.Iθ, (A θ + B θ + C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ (1 + 1 / L) * (∫ θ in Work.Spaces.Iθ, (C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (1 + L) * ((∫ θ in Work.Spaces.Iθ, (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (∫ θ in Work.Spaces.Iθ, (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  have hIA : Integrable (fun θ => (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta hA
  have hIB : Integrable (fun θ => (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta hB
  have hIC : Integrable (fun θ => (C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta hC
  have hIABC : Integrable (fun θ => (A θ + B θ + C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta ((hA.add hB).add hC)
  have hC1 : Integrable (fun θ => (1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hIC.const_mul (1 + 1 / L)
  have hAB : Integrable (fun θ => (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (volume.restrict Work.Spaces.Iθ) :=
    hIA.add hIB
  have hAB2 : Integrable (fun θ => 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) (volume.restrict Work.Spaces.Iθ) :=
    hAB.const_mul (2 * (1 + L))
  have hRHS : Integrable (fun θ =>
        (1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
              + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hC1.add hAB2
  have e1 : (∫ θ in Work.Spaces.Iθ, ((1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)))
      = (∫ θ in Work.Spaces.Iθ, (1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        + (∫ θ in Work.Spaces.Iθ, 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
    integral_add hC1 hAB2
  have e2 : (∫ θ in Work.Spaces.Iθ, (1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = (1 + 1 / L) * (∫ θ in Work.Spaces.Iθ, (C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    integral_const_mul (1 + 1 / L) (fun θ => (C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
  have e3 : (∫ θ in Work.Spaces.Iθ, 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = 2 * (1 + L) * (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
    integral_const_mul (2 * (1 + L)) (fun θ => (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
  have e4 : (∫ θ in Work.Spaces.Iθ, ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = (∫ θ in Work.Spaces.Iθ, (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    integral_add hIA hIB
  calc (∫ θ in Work.Spaces.Iθ, (A θ + B θ + C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
              + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
        refine setIntegral_mono_on hIABC hRHS measurableSet_Icc (fun θ hθ => ?_)
        have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have hpt : (A θ + B θ + C θ) ^ 2
            ≤ (1 + 1 / L) * (C θ) ^ 2 + 2 * (1 + L) * ((A θ) ^ 2 + (B θ) ^ 2) :=
          sq3_le_young hL
        calc (A θ + B θ + C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ ((1 + 1 / L) * (C θ) ^ 2 + 2 * (1 + L) * ((A θ) ^ 2 + (B θ) ^ 2))
                * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right hpt hσ
          _ = (1 + 1 / L) * ((C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                + 2 * (1 + L) * ((A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
                    + (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
    _ = (1 + 1 / L) * (∫ θ in Work.Spaces.Iθ, (C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (1 + L) * ((∫ θ in Work.Spaces.Iθ, (A θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (∫ θ in Work.Spaces.Iθ, (B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
        rw [e1, e2, e3, e4]

end Work.Blocks.InterpTrunc
