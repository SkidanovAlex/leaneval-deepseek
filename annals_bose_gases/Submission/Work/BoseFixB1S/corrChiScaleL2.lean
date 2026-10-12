import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.corrChiScaleL2`

The `L²`-bound for the scaled localisation window: for `0 < ℓ` and any continuous
`w : EuclideanSpace ℝ (Fin 3) → ℝ`,

    ∫_ℝ³ χ_ℓ(z)² w(z)²  ≤  (∫_ℝ³ χ²)⁻¹ · ∫_{Λ(ℓ)} w(z)²,

where `χ_ℓ(z) = χ(z/ℓ)` (`Submission.BoseGases.chiScale`) and `Λ(ℓ) = acube ℓ` is the
centred cube `[−ℓ/2,ℓ/2]³`.

Two elementary facts about the cubic bump `χ` of `Submission.CubicChi` give this:

* `χ_ℓ(z)² ≤ chiNormSq⁻¹` **everywhere** (`chiNormSq = ∫χ²`, and
  `χ_ℓ(z)² = (χBase(z/ℓ) / √chiNormSq)²` with `0 ≤ χBase ≤ 1`), and
* `χ_ℓ` **vanishes off the cube**: `χ_ℓ(z) ≠ 0` forces `‖z‖ ≤ ℓ/2`, and
  `‖z‖ ≤ ℓ/2` implies `z ∈ acube ℓ` since `|z m| ≤ ‖z‖`.

Hence the integrand `χ_ℓ²w²` is supported in the compact cube, and on it the
pointwise bound `χ_ℓ²w² ≤ chiNormSq⁻¹ w²` may be integrated.
-/

open MeasureTheory
open scoped Topology

namespace Work.BoseFixB1S

set_option autoImplicit false

/-- `χ_ℓ(z)² ≤ (∫χ²)⁻¹` everywhere (the bump-height bound). -/
private lemma chiScale_sq_le_inv (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    (Submission.BoseGases.chiScale ℓ z) ^ 2 ≤ (Submission.BoseGases.chiNormSq)⁻¹ := by
  have hNpos : 0 < Submission.BoseGases.chiNormSq := Submission.BoseGases.chiNormSq_pos
  rw [Submission.BoseGases.chiScale, Submission.BoseGases.chi, div_pow,
    Real.sq_sqrt (le_of_lt hNpos)]
  have h1 : Submission.BoseGases.chiBase ((ℓ⁻¹) • z) ≤ 1 :=
    Submission.BoseGases.chiBase_le_one _
  have hsq : (Submission.BoseGases.chiBase ((ℓ⁻¹) • z)) ^ 2 ≤ 1 := by
    nlinarith [Submission.BoseGases.chiBase_nonneg ((ℓ⁻¹) • z)]
  rw [div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right hsq
    (inv_nonneg.mpr (le_of_lt hNpos))

/-- `χ_ℓ` vanishes outside the centred cube of side `ℓ`. -/
private lemma chiScale_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiScale ℓ z = 0 := by
  by_contra hne
  exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓ.le
    (Submission.BoseGases.chiScale_support_le hℓ hne))

theorem corrChiScaleL2 {ℓ : ℝ} (hℓ : 0 < ℓ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ *
        (∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2) := by
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiScale ℓ z) ^ 2 ≤ (Submission.BoseGases.chiNormSq)⁻¹ :=
    chiScale_sq_le_inv ℓ
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ Submission.BoseGases.acube ℓ → Submission.BoseGases.chiScale ℓ z = 0 :=
    fun _ hz => chiScale_eq_zero_of_notMem_acube hℓ hz
  -- the integrand vanishes off the cube, so the global integral is the restricted one
  have hstep1 : (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2 := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
      ring
  rw [hstep1]
  -- both integrands are continuous on the compact cube
  have hfi : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).mul (hw.pow 2)).continuousOn
  have hgi : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiNormSq)⁻¹ * (w z) ^ 2)
      (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((hw.pow 2).const_mul (Submission.BoseGases.chiNormSq)⁻¹).continuousOn
  -- and the pointwise bound integrates
  have hmono := MeasureTheory.setIntegral_mono_on hfi hgi
    (Submission.BoseGases.acube_measurable ℓ)
    (fun z _ => mul_le_mul_of_nonneg_right (hpt z) (sq_nonneg (w z)))
  refine hmono.trans (le_of_eq ?_)
  rw [← MeasureTheory.integral_const_mul]

end Work.BoseFixB1S
