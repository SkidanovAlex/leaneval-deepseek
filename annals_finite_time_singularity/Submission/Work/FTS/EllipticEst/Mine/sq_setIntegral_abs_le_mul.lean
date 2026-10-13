import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.Mine

/-- Cauchy–Schwarz with reciprocal weights: if `u, v ≥ 0` and `u * v = 1` a.e. on `s`, then
`(∫_s |g|)^2 ≤ (∫_s g^2 u) * (∫_s v)`.

Indeed, on the a.e. set where `u, v ≥ 0` and `u v = 1`,
`|g| = √(g^2 u) · √v`, so the claim is the inequality of Cauchy–Schwarz for the two functions
`x ↦ √(g x ^ 2 * u x)` and `x ↦ √(v x)`, with the integrals `∫ (√(g²u))² = ∫ g² u` and
`∫ (√v)² = ∫ v`. -/
theorem sq_setIntegral_abs_le_mul {g u v : ℝ → ℝ} {s : Set ℝ}
    (hg : AEMeasurable g (MeasureTheory.volume.restrict s))
    (hu : AEMeasurable u (MeasureTheory.volume.restrict s))
    (hv : AEMeasurable v (MeasureTheory.volume.restrict s))
    (hu0 : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ u x)
    (hv0 : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ v x)
    (huv : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), u x * v x = 1)
    (h1 : MeasureTheory.IntegrableOn (fun x => g x ^ 2 * u x) s)
    (h2 : MeasureTheory.IntegrableOn v s)
    (h3 : MeasureTheory.IntegrableOn (fun x => |g x|) s) :
    (∫ x in s, |g x|) ^ 2 ≤ (∫ x in s, g x ^ 2 * u x) * (∫ x in s, v x) := by
  set A : ℝ → ℝ := fun x => Real.sqrt (g x ^ 2 * u x) with hA
  set B : ℝ → ℝ := fun x => Real.sqrt (v x) with hB
  have hA_meas : AEMeasurable A (volume.restrict s) := by
    rw [hA]; exact ((hg.pow_const 2).mul hu).sqrt
  have hB_meas : AEMeasurable B (volume.restrict s) := by
    rw [hB]; exact hv.sqrt
  have hprod : (fun x => A x * B x) =ᵐ[volume.restrict s] (fun x => |g x|) := by
    filter_upwards [hu0, hv0, huv] with x hux _ huvx
    show A x * B x = |g x|
    rw [hA, hB]
    show Real.sqrt (g x ^ 2 * u x) * Real.sqrt (v x) = |g x|
    rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) hux)]
    have : g x ^ 2 * u x * v x = g x ^ 2 := by rw [mul_assoc, huvx, mul_one]
    rw [this, Real.sqrt_sq_eq_abs]
  have hA2 : (fun x => A x ^ 2) =ᵐ[volume.restrict s] (fun x => g x ^ 2 * u x) := by
    filter_upwards [hu0] with x hux
    show A x ^ 2 = g x ^ 2 * u x
    rw [hA]
    exact Real.sq_sqrt (mul_nonneg (sq_nonneg _) hux)
  have hB2 : (fun x => B x ^ 2) =ᵐ[volume.restrict s] (fun x => v x) := by
    filter_upwards [hv0] with x hvx
    show B x ^ 2 = v x
    rw [hB]
    exact Real.sq_sqrt hvx
  -- the product `A * B` is a.e. `|g|`, hence integrable (this is where `h3` is used)
  have hAB_int : Integrable (fun x => A x * B x) (volume.restrict s) :=
    h3.integrable.congr hprod.symm
  have hA2_int : Integrable (fun x => A x ^ 2) (volume.restrict s) :=
    h1.integrable.congr hA2.symm
  have hB2_int : Integrable (fun x => B x ^ 2) (volume.restrict s) :=
    h2.integrable.congr hB2.symm
  have hA_nonneg : 0 ≤ᵐ[volume.restrict s] A := by
    filter_upwards with x
    rw [hA]; exact Real.sqrt_nonneg _
  have hB_nonneg : 0 ≤ᵐ[volume.restrict s] B := by
    filter_upwards with x
    rw [hB]; exact Real.sqrt_nonneg _
  have hA_memLp : MemLp A (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hA_meas.aestronglyMeasurable).mpr hA2_int
  have hB_memLp : MemLp B (ENNReal.ofReal 2) (volume.restrict s) := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hB_meas.aestronglyMeasurable).mpr hB2_int
  -- Cauchy–Schwarz (Hölder with conjugate exponents `2` and `2`)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    hA_nonneg hB_nonneg hA_memLp hB_memLp
  -- turn the real powers in Hölder back into natural powers
  have hconvA : (∫ x, A x ^ (2:ℝ) ∂(volume.restrict s)) = ∫ x, A x ^ 2 ∂(volume.restrict s) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.rpow_natCast _ 2)
  have hconvB : (∫ x, B x ^ (2:ℝ) ∂(volume.restrict s)) = ∫ x, B x ^ 2 ∂(volume.restrict s) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.rpow_natCast _ 2)
  rw [hconvA, hconvB] at hholder
  have hleft : (∫ x, A x * B x ∂(volume.restrict s)) = ∫ x in s, |g x| :=
    integral_congr_ae hprod
  have hright1 : (∫ x, A x ^ 2 ∂(volume.restrict s)) = ∫ x in s, g x ^ 2 * u x :=
    integral_congr_ae hA2
  have hright2 : (∫ x, B x ^ 2 ∂(volume.restrict s)) = ∫ x in s, v x :=
    integral_congr_ae hB2
  have ha : 0 ≤ ∫ x, A x * B x ∂(volume.restrict s) := by
    rw [hleft]; exact integral_nonneg (fun x => abs_nonneg _)
  have hPA : 0 ≤ ∫ x, A x ^ 2 ∂(volume.restrict s) := by
    rw [hright1]
    exact integral_nonneg_of_ae (by
      filter_upwards [hu0] with x hx; exact mul_nonneg (sq_nonneg _) hx)
  have hPB : 0 ≤ ∫ x, B x ^ 2 ∂(volume.restrict s) := by
    rw [hright2]; exact integral_nonneg_of_ae hv0
  -- squaring the Hölder inequality
  have hsq : ((∫ x, A x ^ 2 ∂(volume.restrict s)) ^ (1/2 : ℝ)
      * (∫ x, B x ^ 2 ∂(volume.restrict s)) ^ (1/2 : ℝ)) ^ 2
      = (∫ x, A x ^ 2 ∂(volume.restrict s)) * (∫ x, B x ^ 2 ∂(volume.restrict s)) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hPA, Real.sq_sqrt hPB]
  calc (∫ x in s, |g x|) ^ 2
      = (∫ x, A x * B x ∂(volume.restrict s)) ^ 2 := by rw [hleft]
    _ ≤ ((∫ x, A x ^ 2 ∂(volume.restrict s)) ^ (1/2 : ℝ)
          * (∫ x, B x ^ 2 ∂(volume.restrict s)) ^ (1/2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ ha hholder 2
    _ = (∫ x, A x ^ 2 ∂(volume.restrict s)) * (∫ x, B x ^ 2 ∂(volume.restrict s)) := hsq
    _ = (∫ x in s, g x ^ 2 * u x) * (∫ x in s, v x) := by rw [hright1, hright2]

end Work.FTS.EllipticEst.Mine
