import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Metric
open scoped ENNReal Topology

/-- If `ν` lies in `L^{q/(q-1)}` (`1 < q < 2`), vanishes outside a ball of radius `R`,
and the (locally integrable) kernel `w ↦ ‖w - z‖^{-q}` has finite lintegral on balls
around `z`, then `w ↦ ν w / (w - z)` is integrable.  This is the Hölder estimate
`L^{q/(q-1)} · L^q_loc ⊆ L^1_loc` combined with the compact support of `ν`. -/
theorem integrable_cauchyKernel_of_memLp_lintegral {ν : ℂ → ℂ} {R q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hν : MeasureTheory.AEStronglyMeasurable ν (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hint : (∫⁻ w, ‖ν w‖ₑ ^ (q / (q - 1))) < ⊤)
    (hsupp : ∀ w : ℂ, R ≤ ‖w‖ → ν w = 0)
    (hK : ∀ (z : ℂ) (r : ℝ), 0 < r →
      (∫⁻ w in Metric.ball z r, ‖w - z‖ₑ ^ (-q)) < ⊤)
    (z : ℂ) :
    MeasureTheory.Integrable (fun w : ℂ => ν w / (w - z))
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  set S : Set ℂ := Metric.closedBall (0 : ℂ) R with hS
  have hSmeas : MeasurableSet S := by rw [hS]; exact Metric.isClosed_closedBall.measurableSet
  have hq_pos : 0 < q := lt_trans zero_lt_one hq1
  have hqm1 : 0 < q - 1 := by linarith
  have hp_pos : 0 < q / (q - 1) := div_pos hq_pos hqm1
  have hpq : Real.HolderConjugate (q / (q - 1)) q := by
    refine Real.HolderTriple.mk ?_ hp_pos hq_pos
    rw [inv_one]; field_simp; ring
  have haesm : AEStronglyMeasurable (fun w : ℂ => ν w / (w - z)) volume := by
    have hden_inv : AEStronglyMeasurable (fun w : ℂ => (w - z)⁻¹) (volume : Measure ℂ) :=
      (by measurability : Measurable (fun w : ℂ => (w - z)⁻¹)).aestronglyMeasurable
    exact hν.mul hden_inv
  have hvan : (fun w : ℂ => ‖ν w / (w - z)‖ₑ)
      = S.indicator (fun w : ℂ => ‖ν w / (w - z)‖ₑ) := by
    funext w
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw]
      have hw' : R ≤ ‖w‖ := by
        rw [hS] at hw
        rw [Metric.mem_closedBall] at hw
        push Not at hw
        rw [dist_eq_norm, sub_zero] at hw
        exact le_of_lt hw
      have hν0 : ν w = 0 := hsupp w hw'
      simp [hν0]
  have hAfin : (∫⁻ w, ‖ν w‖ₑ ^ (q / (q - 1)) ∂(volume.restrict S)) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral S (fun w => ‖ν w‖ₑ ^ (q / (q - 1)))) hint
  have hr : 0 < |R| + ‖z‖ + 1 := by positivity
  have hsub : S ⊆ Metric.ball z (|R| + ‖z‖ + 1) := by
    intro w hw
    rw [hS] at hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have hw' : ‖w‖ ≤ R := by simpa [dist_eq_norm] using hw
    calc dist w z ≤ dist w 0 + dist 0 z := dist_triangle w 0 z
      _ = ‖w‖ + ‖z‖ := by simp [dist_eq_norm]
      _ ≤ R + ‖z‖ := by linarith
      _ ≤ |R| + ‖z‖ := by linarith [le_abs_self R]
      _ < |R| + ‖z‖ + 1 := by linarith
  have hBfin : (∫⁻ w, ‖(w - z)⁻¹‖ₑ ^ q ∂(volume.restrict S)) < ⊤ := by
    have hle : ∀ w : ℂ, ‖(w - z)⁻¹‖ₑ ^ q ≤ ‖w - z‖ₑ ^ (-q) := by
      intro w
      by_cases hw : w - z = 0
      · rw [hw, inv_zero, enorm_zero, ENNReal.zero_rpow_of_pos hq_pos]
        exact bot_le
      · rw [enorm_inv hw, ENNReal.inv_rpow, ENNReal.rpow_neg]
    have h2 : (∫⁻ w, ‖(w - z)⁻¹‖ₑ ^ q ∂(volume.restrict S))
        ≤ (∫⁻ w, ‖w - z‖ₑ ^ (-q) ∂(volume.restrict S)) := lintegral_mono hle
    have h3 : (∫⁻ w, ‖w - z‖ₑ ^ (-q) ∂(volume.restrict S))
        ≤ (∫⁻ w in Metric.ball z (|R| + ‖z‖ + 1), ‖w - z‖ₑ ^ (-q)) :=
      lintegral_mono_set hsub
    exact lt_of_le_of_lt (le_trans h2 h3) (hK z (|R| + ‖z‖ + 1) hr)
  have hmain : (∫⁻ w, ‖ν w / (w - z)‖ₑ ∂(volume : Measure ℂ)) < ⊤ := by
    rw [hvan, lintegral_indicator hSmeas]
    have hgg : AEMeasurable (fun w : ℂ => ‖(w - z)⁻¹‖ₑ) (volume.restrict S) :=
      (by measurability : Measurable (fun w : ℂ => ‖(w - z)⁻¹‖ₑ)).aemeasurable
    have hHölder : (∫⁻ w, ‖ν w‖ₑ * ‖(w - z)⁻¹‖ₑ ∂(volume.restrict S))
        ≤ (∫⁻ w, ‖ν w‖ₑ ^ (q / (q - 1)) ∂(volume.restrict S)) ^ (1 / (q / (q - 1))) *
          (∫⁻ w, ‖(w - z)⁻¹‖ₑ ^ q ∂(volume.restrict S)) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq (hν.enorm.restrict) hgg
    have h1 : (∫⁻ w, ‖ν w / (w - z)‖ₑ ∂(volume.restrict S))
        ≤ (∫⁻ w, ‖ν w‖ₑ * ‖(w - z)⁻¹‖ₑ ∂(volume.restrict S)) := by
      apply lintegral_mono; intro w
      show ‖ν w / (w - z)‖ₑ ≤ ‖ν w‖ₑ * ‖(w - z)⁻¹‖ₑ
      rw [div_eq_mul_inv, enorm_mul]
    have hA' : (∫⁻ w, ‖ν w‖ₑ ^ (q / (q - 1)) ∂(volume.restrict S)) ^ (1 / (q / (q - 1))) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hp_pos)) hAfin.ne
    have hB' : (∫⁻ w, ‖(w - z)⁻¹‖ₑ ^ q ∂(volume.restrict S)) ^ (1 / q) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hq_pos)) hBfin.ne
    exact lt_of_le_of_lt (le_trans h1 hHölder) (ENNReal.mul_lt_top hA' hB')
  exact ⟨haesm, (MeasureTheory.hasFiniteIntegral_iff_enorm (f := fun w : ℂ => ν w / (w - z))).mpr hmain⟩

end Work.MRMT.Cauchy
