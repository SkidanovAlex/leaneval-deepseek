/-
Work.MRMT.Found — the `L²` bound for the Cauchy transform on a ball, in Bochner-integral
form, with the explicit constant `8 √(M R)`.

`ω ∈ L²(ℂ)` supported in `ball 0 M`; then
`∫_{ball 0 R} ‖C ω‖² ≤ (8 √(M R))² ∫ ‖ω‖²`.

The `ℝ≥0∞`-valued core is the Schur/Tonelli estimate `lintegral_sq_cauchyKernel_le`
(already available in `cauchyTransform_memLp_ball`), which produces the bound
`∫⁻_{ball 0 R} ‖C ω‖ₑ² ≤ ofReal (64 M R) · ∫⁻ ‖ω‖ₑ²`; the rest is the standard
`∫ = (∫⁻ ·).toReal` translation for nonnegative real-valued integrands.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function
open scoped ENNReal Topology

namespace Work.MRMT.Found

/-- **`ℝ≥0∞`-valued Schur/Tonelli bound with explicit constant.** For `ω ∈ L²` supported in
`ball 0 M`, `∫⁻_{ball 0 R} ‖C ω‖ₑ² ≤ ofReal (64 M R) · ∫⁻ ‖ω‖ₑ²`. -/
theorem lintegral_normSq_cauchyTransform_le {ω : ℂ → ℂ} {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hω : MemLp ω 2 (volume : Measure ℂ))
    (hs : Function.support ω ⊆ Metric.ball (0 : ℂ) M) :
    ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ₑ ^ 2
      ≤ ENNReal.ofReal (64 * M * R) * ∫⁻ z, ‖ω z‖ₑ ^ 2 := by
  classical
  have hsm : AEStronglyMeasurable ω (volume : Measure ℂ) := hω.aestronglyMeasurable
  -- `ω` vanishes off `ball 0 M` (pointwise, not just a.e.)
  have hvanish : ∀ ζ : ℂ, ζ ∉ Metric.ball (0 : ℂ) M → ω ζ = 0 := fun ζ hζ =>
    by_contra fun hne => hζ (hs (by simpa [Function.mem_support] using hne))
  -- pointwise (in `z`) bound by the Cauchy-kernel integral
  have hpt : ∀ z : ℂ, ‖Work.MRMT.cauchyTransform ω z‖ₑ ≤ ‖Work.MRMT.cauchyConst‖ₑ *
      ∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
    intro z
    have hzero : ∀ ζ ∉ Metric.ball (0 : ℂ) M, ω ζ / (ζ - z) = 0 := by
      intro ζ hζ
      rw [hvanish ζ hζ, zero_div]
    have h1 : (∫ ζ, ω ζ / (ζ - z)) = ∫ ζ in Metric.ball (0 : ℂ) M, ω ζ / (ζ - z) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    calc ‖Work.MRMT.cauchyTransform ω z‖ₑ
        = ‖Work.MRMT.cauchyConst‖ₑ * ‖∫ ζ, ω ζ / (ζ - z)‖ₑ := by
          rw [Work.MRMT.cauchyTransform, enorm_mul]
      _ = ‖Work.MRMT.cauchyConst‖ₑ * ‖∫ ζ in Metric.ball (0 : ℂ) M, ω ζ / (ζ - z)‖ₑ := by
          rw [h1]
      _ ≤ ‖Work.MRMT.cauchyConst‖ₑ * ∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ / (ζ - z)‖ₑ :=
          mul_le_mul_right (enorm_integral_le_lintegral_enorm (fun ζ => ω ζ / (ζ - z))) _
      _ = ‖Work.MRMT.cauchyConst‖ₑ * ∫⁻ ζ in Metric.ball (0 : ℂ) M,
            ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
          congr 1
          apply setLIntegral_congr_fun measurableSet_ball
          intro ζ _
          exact enorm_div_eq_mul_ofReal_inv (ω ζ) (ζ - z)
  -- the support reduction
  have hsupp : ∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ ^ 2 = ∫⁻ ζ, ‖ω ζ‖ₑ ^ 2 := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun ζ => ?_
    rw [Set.indicator_apply]
    by_cases hζ : ζ ∈ Metric.ball (0 : ℂ) M
    · rw [ite_eq_left hζ]
    · rw [ite_eq_right hζ, hvanish ζ hζ]; simp
  have hschur := lintegral_sq_cauchyKernel_le ω hM hR hsm.aemeasurable
  have hcc : ‖Work.MRMT.cauchyConst‖ₑ = ENNReal.ofReal Real.pi⁻¹ := by
    have hpi : ‖((Real.pi : ℂ))‖ = Real.pi := by norm_num
    rw [Work.MRMT.cauchyConst, enorm_neg,
      enorm_inv (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)), ← ofReal_norm, hpi]
    exact (ENNReal.ofReal_inv_of_pos Real.pi_pos).symm
  have hCBB : ‖Work.MRMT.cauchyConst‖ₑ ^ 2
        * (ENNReal.ofReal (8 * Real.pi * M) * ENNReal.ofReal (8 * Real.pi * R))
      = ENNReal.ofReal (64 * M * R) := by
    rw [hcc, ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ Real.pi⁻¹),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * Real.pi * M),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi⁻¹ ^ 2)]
    congr 1
    rw [show Real.pi⁻¹ ^ 2 * (8 * Real.pi * M * (8 * Real.pi * R)) = 64 * M * R from by
      field_simp
      ring]
  have h1 : ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ₑ ^ 2
      ≤ ‖Work.MRMT.cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R,
          (∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := by
    calc ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ₑ ^ 2
        ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
            (‖Work.MRMT.cauchyConst‖ₑ
              * ∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 :=
          lintegral_mono fun z => ENNReal.pow_le_pow_left (hpt z)
      _ = ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyConst‖ₑ ^ 2
            * (∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := by
          apply setLIntegral_congr_fun measurableSet_ball
          intro z _
          exact mul_sq _ _
      _ = ‖Work.MRMT.cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R,
            (∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 :=
          lintegral_const_mul' _ _ (by rw [hcc]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  calc ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ₑ ^ 2
      ≤ ‖Work.MRMT.cauchyConst‖ₑ ^ 2 * ∫⁻ z in Metric.ball (0 : ℂ) R,
          (∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ * ENNReal.ofReal (‖ζ - z‖⁻¹)) ^ 2 := h1
    _ ≤ ‖Work.MRMT.cauchyConst‖ₑ ^ 2 * (ENNReal.ofReal (8 * Real.pi * M)
          * ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ ζ in Metric.ball (0 : ℂ) M, ‖ω ζ‖ₑ ^ 2) :=
        mul_le_mul_right hschur _
    _ = ‖Work.MRMT.cauchyConst‖ₑ ^ 2 * (ENNReal.ofReal (8 * Real.pi * M)
          * ENNReal.ofReal (8 * Real.pi * R) * ∫⁻ ζ, ‖ω ζ‖ₑ ^ 2) := by rw [hsupp]
    _ = (‖Work.MRMT.cauchyConst‖ₑ ^ 2
          * (ENNReal.ofReal (8 * Real.pi * M) * ENNReal.ofReal (8 * Real.pi * R)))
          * ∫⁻ ζ, ‖ω ζ‖ₑ ^ 2 := by ring
    _ = ENNReal.ofReal (64 * M * R) * ∫⁻ ζ, ‖ω ζ‖ₑ ^ 2 := by rw [hCBB]

theorem fw_integral_normSq_cauchyTransform_le {ω : ℂ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hω : MeasureTheory.MemLp ω 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : Function.support ω ⊆ Metric.ball (0 : ℂ) M) :
    ∫ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ ^ 2
      ≤ (8 * Real.sqrt (M * R)) ^ 2 * ∫ z, ‖ω z‖ ^ 2 := by
  classical
  have hkey := lintegral_normSq_cauchyTransform_le hM.le hR.le hω hs
  have hChL2 : MemLp (Work.MRMT.cauchyTransform ω) 2
      (volume.restrict (Metric.ball (0 : ℂ) R)) :=
    (cauchyTransform_memLp_ball (h := ω) (R := M) (R' := R) hM hR hω hs).1
  have hAESM_ct : AEStronglyMeasurable (fun z => ‖Work.MRMT.cauchyTransform ω z‖ ^ 2)
      (volume.restrict (Metric.ball (0 : ℂ) R)) :=
    (continuous_pow 2).comp_aestronglyMeasurable
      ((continuous_norm).comp_aestronglyMeasurable hChL2.aestronglyMeasurable)
  have hAESM_ω : AEStronglyMeasurable (fun z => ‖ω z‖ ^ 2) (volume : Measure ℂ) :=
    (continuous_pow 2).comp_aestronglyMeasurable
      ((continuous_norm).comp_aestronglyMeasurable hω.aestronglyMeasurable)
  -- rewrite `ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2`
  have hof_ct : ∫⁻ z in Metric.ball (0 : ℂ) R,
        ENNReal.ofReal (‖Work.MRMT.cauchyTransform ω z‖ ^ 2)
      = ∫⁻ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ₑ ^ 2 :=
    lintegral_congr fun z => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hof_ω : ∫⁻ z, ENNReal.ofReal (‖ω z‖ ^ 2) = ∫⁻ z, ‖ω z‖ₑ ^ 2 :=
    lintegral_congr fun z => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hkey' : ∫⁻ z in Metric.ball (0 : ℂ) R,
        ENNReal.ofReal (‖Work.MRMT.cauchyTransform ω z‖ ^ 2)
      ≤ ENNReal.ofReal (64 * M * R) * ∫⁻ z, ENNReal.ofReal (‖ω z‖ ^ 2) := by
    rw [hof_ct, hof_ω]; exact hkey
  -- finiteness of `∫⁻ ‖ω‖ₑ²`
  have hfin : ∫⁻ z, ‖ω z‖ₑ ^ 2 < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) hω.eLpNorm_lt_top
    simpa using h
  have hne : ENNReal.ofReal (64 * M * R) * ∫⁻ z, ENNReal.ofReal (‖ω z‖ ^ 2) ≠ ⊤ := by
    rw [hof_ω]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hmono := ENNReal.toReal_mono hne hkey'
  -- translate the two `ℝ≥0∞`-integrals into Bochner integrals of nonnegative functions
  have hCTint : ∫ z in Metric.ball (0 : ℂ) R, ‖Work.MRMT.cauchyTransform ω z‖ ^ 2
      = (∫⁻ z in Metric.ball (0 : ℂ) R,
          ENNReal.ofReal (‖Work.MRMT.cauchyTransform ω z‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Metric.ball (0 : ℂ) R))
      (Filter.Eventually.of_forall fun z => by positivity) hAESM_ct
  have hωint : ∫ z, ‖ω z‖ ^ 2 = (∫⁻ z, ENNReal.ofReal (‖ω z‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => by positivity) hAESM_ω
  have hconst : (64 : ℝ) * M * R = (8 * Real.sqrt (M * R)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hRHS : (ENNReal.ofReal (64 * M * R) * ∫⁻ z, ENNReal.ofReal (‖ω z‖ ^ 2)).toReal
      = (8 * Real.sqrt (M * R)) ^ 2 * ∫ z, ‖ω z‖ ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 64 * M * R),
      hconst, ← hωint]
  rw [hCTint, ← hRHS]
  exact hmono

end Work.MRMT.Found
