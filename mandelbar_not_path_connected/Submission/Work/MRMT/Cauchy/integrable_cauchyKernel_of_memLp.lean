import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.radial_kernel_integrable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Metric Function Filter
open scoped ENNReal Topology

namespace Work.MRMT.Cauchy

/-- The truncated Cauchy kernel `w ↦ 1/(w - z)`, cut off outside the disc `‖w - z‖ ≤ R`. -/
def cauchyCap (z : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  ((if ‖w - z‖ ≤ R then ‖w - z‖⁻¹ else 0 : ℝ) : ℂ)

theorem cauchyCap_apply (z : ℂ) (R : ℝ) (w : ℂ) :
    cauchyCap z R w = ((if ‖w - z‖ ≤ R then ‖w - z‖⁻¹ else 0 : ℝ) : ℂ) := rfl

theorem norm_cauchyCap_of_mem (z : ℂ) (R : ℝ) {w : ℂ} (h : ‖w - z‖ ≤ R) :
    ‖cauchyCap z R w‖ = ‖w - z‖⁻¹ := by
  rw [cauchyCap, if_pos h]
  have hnorm : ‖(((‖w - z‖)⁻¹ : ℝ) : ℂ)‖ = |(‖w - z‖)⁻¹| := RCLike.norm_ofReal _
  rw [hnorm, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]

theorem norm_cauchyCap_pow (z : ℂ) (R : ℝ) {q : ENNReal} (hqr0 : 0 < q.toReal) (w : ℂ) :
    ‖cauchyCap z R w‖ ^ q.toReal
      = if ‖w - z‖ ≤ R then ‖w - z‖ ^ (-q.toReal) else 0 := by
  by_cases h : ‖w - z‖ ≤ R
  · rw [cauchyCap, if_pos h]
    have hnorm : ‖(((‖w - z‖)⁻¹ : ℝ) : ℂ)‖ = |(‖w - z‖)⁻¹| := RCLike.norm_ofReal _
    rw [hnorm, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    rw [if_pos h]
  · rw [cauchyCap, if_neg h, if_neg h, Complex.ofReal_zero, norm_zero,
        Real.zero_rpow hqr0.ne']

/-- The truncated Cauchy kernel lies in `L^q` for every `q < 2` (dimension 2). -/
theorem memLp_cauchyCap (z : ℂ) (R : ℝ) {q : ENNReal} (hq1 : 1 ≤ q) (hq2 : q < 2) :
    MemLp (cauchyCap z R) q (volume : Measure ℂ) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hqtop : q ≠ ⊤ := ne_top_of_lt hq2
  have hqr : q.toReal < 2 := (ENNReal.toReal_lt_toReal hqtop (by norm_num)).mpr hq2
  have hqr0 : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have haesm : AEStronglyMeasurable (cauchyCap z R) (volume : Measure ℂ) := by
    apply Measurable.aestronglyMeasurable
    unfold cauchyCap
    refine Complex.measurable_ofReal.comp ?_
    have h1 : Measurable (fun w : ℂ => ‖w - z‖) :=
      measurable_norm.comp (measurable_id.sub_const z)
    exact Measurable.ite (measurableSet_le h1 measurable_const) h1.inv measurable_const
  refine (integrable_norm_rpow_iff haesm hq0 hqtop).mp ?_
  have hfun : (fun w : ℂ => ‖cauchyCap z R w‖ ^ q.toReal)
      = fun w : ℂ => if ‖w - z‖ ≤ R then ‖w - z‖ ^ (-q.toReal) else 0 :=
    funext fun w => norm_cauchyCap_pow z R hqr0 w
  rw [hfun]
  exact radial_kernel_integrable z R hqr

theorem integrable_cauchyKernel_of_memLp {ν : ℂ → ℂ} {p : ENNReal} (hp : 2 < p)
    (hν : MeasureTheory.MemLp ν p (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport ν) (z : ℂ) :
    MeasureTheory.Integrable (fun w : ℂ => ν w / (w - z)) (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt (lt_trans (by norm_num) hp)
  haveI : Fact (1 ≤ p) := ⟨hp1⟩
  have hq1 : (1 : ENNReal) ≤ ENNReal.conjExponent p := by
    rw [ENNReal.conjExponent]; simp
  have hq2 : ENNReal.conjExponent p < 2 := by
    rw [ENNReal.conjExponent]
    have h1 : (1 : ENNReal) < p - 1 := by
      rw [lt_tsub_iff_left]
      have : (1 : ENNReal) + 1 = 2 := by norm_num
      rwa [this]
    have h2 : (p - 1)⁻¹ < 1 := ENNReal.inv_lt_one.mpr h1
    have h3 := ENNReal.add_lt_add_left (a := (1 : ENNReal)) (by norm_num) h2
    have : (1 : ENNReal) + 1 = 2 := by norm_num
    rwa [this] at h3
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall z).mp hs.isCompact.isBounded
  have hκ : MemLp (cauchyCap z (R + 1)) (ENNReal.conjExponent p) (volume : Measure ℂ) :=
    memLp_cauchyCap z (R + 1) hq1 hq2
  have hprod : Integrable (fun w : ℂ => ν w * cauchyCap z (R + 1) w) (volume : Measure ℂ) :=
    hν.integrable_mul hκ
  refine Integrable.mono' hprod.norm ?_ ?_
  · have h1 : AEStronglyMeasurable (fun w : ℂ => (w - z)⁻¹) (volume : Measure ℂ) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    have h2 : AEStronglyMeasurable (fun w : ℂ => ν w * (w - z)⁻¹) (volume : Measure ℂ) :=
      hν.aestronglyMeasurable.mul h1
    simpa only [div_eq_mul_inv] using h2
  · filter_upwards with w
    by_cases hw : w ∈ tsupport ν
    · have hwz : ‖w - z‖ ≤ R + 1 := by
        have h1 : w ∈ closedBall z R := hR hw
        rw [mem_closedBall] at h1
        have h2 : ‖w - z‖ ≤ R := by simpa [dist_eq_norm] using h1
        linarith
      simp only [norm_mul, norm_inv, norm_cauchyCap_of_mem z (R + 1) hwz, div_eq_mul_inv]
      exact le_refl _
    · simp [image_eq_zero_of_notMem_tsupport hw]

end Work.MRMT.Cauchy
