import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory

namespace Work.MRMT.Found

/-! ## Integrability of `‖ω‖` for a compactly supported `L²` field -/

/-- A field `ω ∈ L²(ℂ)` whose support is contained in the closed ball of radius `M` centred at
the origin is integrable.  On that ball the measure is finite, so `L² ⊂ L¹` there; and off the
ball `‖ω‖` vanishes, which lets us transfer the integrability back to `volume`. -/
lemma fw_aux_integrable_norm {ω : ℂ → ℂ} {M : ℝ}
    (hω : MemLp ω 2 (volume : Measure ℂ))
    (hsupp : ∀ z : ℂ, ω z ≠ 0 → ‖z‖ ≤ M) :
    Integrable (fun z : ℂ => ‖ω z‖) volume := by
  have hs : MeasurableSet (Metric.closedBall (0 : ℂ) M) := measurableSet_closedBall
  have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) M)) := by
    rw [isFiniteMeasure_restrict]
    exact (isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne
  have hωμ : MemLp ω 2 (volume.restrict (Metric.closedBall (0 : ℂ) M)) :=
    hω.mono_measure Measure.restrict_le_self
  have hintμ : Integrable (fun z : ℂ => ‖ω z‖)
      (volume.restrict (Metric.closedBall (0 : ℂ) M)) :=
    MemLp.integrable (q := 2) (by norm_num) hωμ.norm
  have hind : Integrable ((Metric.closedBall (0 : ℂ) M).indicator fun z : ℂ => ‖ω z‖) volume :=
    (integrable_indicator_iff hs).mpr hintμ
  have heq : (Metric.closedBall (0 : ℂ) M).indicator (fun z : ℂ => ‖ω z‖) = fun z => ‖ω z‖ := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) M
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have h0 : ω z = 0 := by
        by_contra h
        exact hz (by simpa [Metric.mem_closedBall, dist_zero_right] using hsupp z h)
      simp [h0]
  simpa only [heq] using hind

/-! ## The `L¹` bound by Cauchy–Schwarz -/

/-- **`L¹`–`L²` bound with the area of the support.**  If `ω ∈ L²(ℂ)` is supported in the closed
ball of radius `M` around the origin and `∫ ‖ω‖² ≤ E²`, then
`∫ ‖ω‖ ≤ E * sqrt (area of the ball)`.  This is Cauchy–Schwarz applied on the finite measure
space `volume.restrict (closedBall 0 M)`, with the constant function `1` as the second factor. -/
lemma fw_aux_integral_le {ω : ℂ → ℂ} {M E : ℝ} (hE0 : 0 ≤ E)
    (hω : MemLp ω 2 (volume : Measure ℂ))
    (hsupp : ∀ z : ℂ, ω z ≠ 0 → ‖z‖ ≤ M)
    (hE : ∫ z, ‖ω z‖ ^ 2 ≤ E ^ 2) :
    ∫ z, ‖ω z‖ ≤ E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) M with hs_def
  set μ : Measure ℂ := volume.restrict s with hμ_def
  have hs : MeasurableSet s := measurableSet_closedBall
  have hfin : IsFiniteMeasure μ := by
    rw [hμ_def, isFiniteMeasure_restrict]
    exact (isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne
  have hωμ : MemLp ω 2 μ := hω.mono_measure (by rw [hμ_def]; exact Measure.restrict_le_self)
  have hone : MemLp (fun _ : ℂ => (1 : ℝ)) 2 μ := memLp_const 1
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) hpq
    (f := fun z : ℂ => ‖ω z‖) (g := fun _ : ℂ => (1 : ℝ))
    (ae_of_all _ fun z => norm_nonneg (ω z)) (ae_of_all _ fun _ => zero_le_one)
    (by simpa using hωμ.norm) (by simpa using hone)
  have hzero : ∀ z : ℂ, z ∉ s → ‖ω z‖ = 0 := by
    intro z hz
    have h0 : ω z = 0 := by
      by_contra h
      exact hz (by simpa [hs_def, Metric.mem_closedBall, dist_zero_right] using hsupp z h)
    simp [h0]
  have hzero2 : ∀ z : ℂ, z ∉ s → ‖ω z‖ ^ 2 = 0 := by
    intro z hz; rw [hzero z hz]; norm_num
  have hsetint : ∫ z, ‖ω z‖ ∂μ = ∫ z, ‖ω z‖ ∂volume := by
    rw [hμ_def]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hsetint2 : ∫ z, ‖ω z‖ ^ 2 ∂μ = ∫ z, ‖ω z‖ ^ 2 ∂volume := by
    rw [hμ_def]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero2
  have hB : ∫ z, (1 : ℝ) ∂μ = (volume s).toReal := by
    rw [integral_const, hμ_def, Measure.real_def, Measure.restrict_apply_univ s]
    simp
  have hA : ∫ z, ‖ω z‖ ^ 2 ∂μ ≤ E ^ 2 := by
    rw [hsetint2]; exact hE
  have hA' : (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ E := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (∫ z, ‖ω z‖ ^ 2 ∂μ) ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt hA
      _ = E := Real.sqrt_sq hE0
  have hB' : (∫ z, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) = Real.sqrt ((volume s).toReal) := by
    have h1 : ∫ z, (1 : ℝ) ^ 2 ∂μ = (volume s).toReal := by
      rw [show (1 : ℝ) ^ 2 = 1 by norm_num]
      exact hB
    rw [h1, Real.sqrt_eq_rpow]
  have hholder' : ∫ z, ‖ω z‖ * 1 ∂μ
      ≤ (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [Real.rpow_two] using hholder
  have key : (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ E * Real.sqrt ((volume s).toReal) := by
    calc (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        = (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * Real.sqrt ((volume s).toReal) := by rw [hB']
      _ ≤ E * Real.sqrt ((volume s).toReal) :=
          mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg _)
  calc ∫ z, ‖ω z‖ ∂volume = ∫ z, ‖ω z‖ ∂μ := hsetint.symm
    _ = ∫ z, ‖ω z‖ * 1 ∂μ := by simp
    _ ≤ (∫ z, ‖ω z‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ z, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hholder'
    _ ≤ E * Real.sqrt ((volume s).toReal) := key
    _ = E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) := by rw [hs_def]

/-! ## The decay estimate -/

theorem fw_decay_cauchyTransform_le {ω : ℂ → ℂ} {M E : ℝ} (hM0 : 0 ≤ M) (hE0 : 0 ≤ E)
    (hω : MeasureTheory.MemLp ω 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hsupp : ∀ z : ℂ, ω z ≠ 0 → ‖z‖ ≤ M)
    (hE : ∫ z, ‖ω z‖ ^ 2 ≤ E ^ 2) :
    ∀ z : ℂ, max (2 * M) 1 ≤ ‖z‖ →
      ‖Work.MRMT.cauchyTransform ω z‖ ≤
        (2 * E * Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) M)).toReal)
          / Real.pi) / ‖z‖ := by
  intro z hz
  -- `hM0` is not needed mathematically: for `M < 0` the support condition forces `ω = 0` and the
  -- estimate is trivial.  It is recorded here so that the hypothesis is used explicitly.
  have hM0' : (0 : ℝ) ≤ M := hM0
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hz2 : 2 * M ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hint : Integrable (fun ζ : ℂ => ‖ω ζ‖) volume := fw_aux_integrable_norm hω hsupp
  have hbound : ∫ ζ, ‖ω ζ‖
      ≤ E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) :=
    fw_aux_integral_le hE0 hω hsupp hE
  have hmain := Work.MRMT.Beltrami.decay_cauchyTransform_le ω hint hsupp hz1 hz2
  calc ‖Work.MRMT.cauchyTransform ω z‖ ≤ (2 * (∫ ζ, ‖ω ζ‖)) / Real.pi / ‖z‖ := hmain
    _ ≤ (2 * (E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)))
          / Real.pi / ‖z‖ := by
        have h2 : 2 * (∫ ζ, ‖ω ζ‖)
            ≤ 2 * (E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right h2 Real.pi_pos.le) (norm_nonneg z)
    _ = (2 * E * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)
          / Real.pi) / ‖z‖ := by ring

end Work.MRMT.Found
