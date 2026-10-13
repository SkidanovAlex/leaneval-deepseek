import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set

/-- **Cauchy–Schwarz on `(0,x)` with the Hardy weight split.**  For `γ > -1`, `x > 0` and an
`F : ℝ → ℝ` whose weighted square and whose `k`-weighted first factor are integrable on `(0,x]`,

  `(∫_0^x s^k F(s) ds)² ≤ (∫_0^x s^γ ds) · (∫_0^x s^{2k-γ} F(s)² ds)`.

The splitting is `s^k F = s^{γ/2} · s^{k-γ/2} F`, using `(s^{γ/2})² = s^γ` and
`(s^{k-γ/2}F)² = s^{2k-γ}F²` on `s > 0`.

The proof converts the three interval integrals to set integrals over `Ioc 0 x`
(`intervalIntegral.integral_of_le`), supplies the two `MemLp 2 (volume.restrict (Ioc 0 x))`
hypotheses via `MeasureTheory.memLp_two_iff_integrable_sq` (the a.e. strong measurability of `F`
following from the integrability of `s^k F` on `Ioc 0 x`, since `s^k` is nonvanishing there),
applies `Work.Spaces.cs_integral` to `u s = s^{γ/2}` and `v s = s^{k-γ/2} F s`, and identifies the
pointwise products a.e. via `Real.rpow_add` / `Real.rpow_mul`. -/
theorem csWeightedInterval (k : ℕ) (γ x : ℝ) (hx : 0 < x) (hγ : -1 < γ) :
    ∀ F : ℝ → ℝ,
      MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) (Set.Ioc 0 x) →
      MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * F s) (Set.Ioc 0 x) →
      (∫ s in (0 : ℝ)..x, s ^ k * F s) ^ 2
        ≤ (∫ s in (0 : ℝ)..x, s ^ γ) * (∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
  intro F hF2 hF1
  have hx0 : (0 : ℝ) ≤ x := hx.le
  -- Strong measurability of `F` on `(0,x]`, from the integrability of `s^k * F s` there.
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Ioc 0 x)) := by
    have hinv : AEStronglyMeasurable (fun s : ℝ => (s ^ k)⁻¹) (volume.restrict (Ioc 0 x)) := by
      fun_prop
    have h2 : AEStronglyMeasurable (fun s : ℝ => (s ^ k)⁻¹ * (s ^ k * F s))
        (volume.restrict (Ioc 0 x)) := hinv.mul hF1.aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hs.1)), one_mul]
  -- `s^γ` is integrable on `(0,x]` because `γ > -1`.
  have hIγ : IntegrableOn (fun s : ℝ => s ^ γ) (Ioc 0 x) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx0]
    exact intervalIntegral.intervalIntegrable_rpow' hγ
  -- The three a.e. identifications on `(0,x]`.
  have hA2 : (fun s : ℝ => (s ^ (γ / 2)) ^ 2) =ᵐ[volume.restrict (Ioc 0 x)]
      (fun s : ℝ => s ^ γ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
    ring_nf
  have hB2 : (fun s : ℝ => (s ^ ((k : ℝ) - γ / 2) * F s) ^ 2)
      =ᵐ[volume.restrict (Ioc 0 x)]
      (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
    congr 2
    ring
  have hAB : (fun s : ℝ => s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s))
      =ᵐ[volume.restrict (Ioc 0 x)] (fun s : ℝ => s ^ k * F s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← mul_assoc, ← Real.rpow_add hs.1,
      show γ / 2 + ((k : ℝ) - γ / 2) = (k : ℝ) by ring, Real.rpow_natCast]
  -- The two `MemLp` inputs for Cauchy–Schwarz.
  have hA : MemLp (fun s : ℝ => s ^ (γ / 2)) 2 (volume.restrict (Ioc 0 x)) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · fun_prop
    · exact hIγ.congr hA2.symm
  have hB : MemLp (fun s : ℝ => s ^ ((k : ℝ) - γ / 2) * F s) 2
      (volume.restrict (Ioc 0 x)) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · have hrp : AEStronglyMeasurable (fun s : ℝ => s ^ ((k : ℝ) - γ / 2))
          (volume.restrict (Ioc 0 x)) := by fun_prop
      exact hrp.mul hFmeas
    · exact hF2.congr hB2.symm
  have key : (∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s)) ^ 2
      ≤ (∫ s in Ioc 0 x, s ^ γ) * (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by
    have h := Work.Spaces.cs_integral hA hB
    have e1 : (∫ s in Ioc 0 x, (fun s : ℝ => s ^ (γ / 2)) s ^ 2) = ∫ s in Ioc 0 x, s ^ γ :=
      integral_congr_ae hA2
    have e2 : (∫ s in Ioc 0 x, (fun s : ℝ => s ^ ((k : ℝ) - γ / 2) * F s) s ^ 2)
        = ∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2 :=
      integral_congr_ae hB2
    rw [e1, e2] at h
    exact h
  have eAB : (∫ s in (0 : ℝ)..x, s ^ k * F s)
      = ∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s) := by
    rw [intervalIntegral.integral_of_le hx0]
    exact (integral_congr_ae hAB).symm
  have eA : (∫ s in Ioc 0 x, s ^ γ) = ∫ s in (0 : ℝ)..x, s ^ γ := by
    rw [intervalIntegral.integral_of_le hx0]
  have eB : (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2)
      = ∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2 := by
    rw [intervalIntegral.integral_of_le hx0]
  calc (∫ s in (0 : ℝ)..x, s ^ k * F s) ^ 2
      = (∫ s in Ioc 0 x, s ^ (γ / 2) * (s ^ ((k : ℝ) - γ / 2) * F s)) ^ 2 := by rw [eAB]
    _ ≤ (∫ s in Ioc 0 x, s ^ γ) * (∫ s in Ioc 0 x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := key
    _ = (∫ s in (0 : ℝ)..x, s ^ γ)
          * (∫ s in (0 : ℝ)..x, s ^ (2 * (k : ℝ) - γ) * (F s) ^ 2) := by rw [eA, eB]

end Work.FTS.H2.DivQ
