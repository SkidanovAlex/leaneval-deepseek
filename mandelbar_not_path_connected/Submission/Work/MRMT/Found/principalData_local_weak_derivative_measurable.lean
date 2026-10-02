import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.QC.isQCOn_of_lipschitz
import Submission.Work.MRMT.Found.PLWD2.pairing_tendsto_of_eLpNorm
import Submission.Work.MRMT.Found.PLWD2.eLpNorm_mul_sub_tendsto

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

set_option linter.unusedVariables false
set_option linter.style.haveILetI false


theorem memLp_of_tendsto_eLpNorm_zero {u : ℕ → ℂ → ℂ} {D : ℂ → ℂ} {K : Set ℂ}
    (hu : ∀ n, MemLp (u n) 2 ((volume : Measure ℂ).restrict K))
    (hcon : Tendsto (fun n => eLpNorm (fun z => u n z - D z) 2 ((volume : Measure ℂ).restrict K)) atTop (𝓝 0)) :
    MemLp D 2 ((volume : Measure ℂ).restrict K) := by
  have hev : ∀ᶠ n in atTop, eLpNorm (fun z => u n z - D z) 2 ((volume : Measure ℂ).restrict K) < 1 :=
    hcon.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hsub : MemLp (fun z => u N z - D z) 2 ((volume : Measure ℂ).restrict K) :=
    memLp_iff.mpr (lt_of_lt_of_le (hN N le_rfl) le_top)
  have hmem : MemLp (fun z => u N z - (u N z - D z)) 2 ((volume : Measure ℂ).restrict K) :=
    (hu N).sub hsub
  have heq : (fun z => u N z - (u N z - D z)) = D := by funext z; ring
  rwa [heq] at hmem

theorem aesm_and_integrableOn_normSq_of_memLp_closedBall {D : ℂ → ℂ} {R : ℝ}
    (hD : MemLp D 2 ((volume : Measure ℂ).restrict (Metric.closedBall 0 R))) :
    AEStronglyMeasurable D ((volume : Measure ℂ).restrict (Metric.ball 0 R)) ∧
    IntegrableOn (fun z => ‖D z‖ ^ 2) (Metric.ball 0 R) (volume : Measure ℂ) := by
  have hsub : (volume : Measure ℂ).restrict (Metric.ball 0 R)
      ≤ (volume : Measure ℂ).restrict (Metric.closedBall 0 R) :=
    Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
  have hDb : MemLp D 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := hD.mono_measure hsub
  exact ⟨hDb.aestronglyMeasurable, hDb.integrable_norm_pow (p := 2) (by norm_num)⟩

theorem continuous_dz_of_cd {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dz f) :=
  Work.MRMT.QC.continuous_dz_of_contDiff' hf (by norm_num)

theorem continuous_dzbar_of_cd {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzbar f) :=
  Work.MRMT.QC.continuous_dzbar_of_contDiff' hf (by norm_num)

theorem hasCompactSupport_dz_of_cd {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (dz f) := by
  refine IsCompact.of_isClosed_subset (show IsCompact (tsupport f) from hf) (isClosed_tsupport _) ?_
  exact (closure_mono (Work.MRMT.QC.support_dz_subset f)).trans
    (le_of_eq (isClosed_tsupport f).closure_eq)

theorem hasCompactSupport_dzbar_of_cd {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (dzbar f) := by
  refine IsCompact.of_isClosed_subset (show IsCompact (tsupport f) from hf) (isClosed_tsupport _) ?_
  exact (closure_mono (Work.MRMT.QC.support_dzbar_subset f)).trans
    (le_of_eq (isClosed_tsupport f).closure_eq)

theorem memLp_dz_restrict_compact {μ : ℂ → ℂ} (d : PrincipalData μ)
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ n, MemLp (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2 ((volume : Measure ℂ).restrict K) := by
  intro n
  haveI : IsFiniteMeasure ((volume : Measure ℂ).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hcont : Continuous (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) :=
    continuous_dz_of_cd (d.contDiff_Fn n)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact MemLp.of_bound (hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) C
    ((ae_restrict_iff' hK.isClosed.measurableSet).mpr (Eventually.of_forall fun z hz => hC z hz))

/-- relation 1. -/
theorem dz_pairing_eq {μ : ℂ → ℂ} (d : PrincipalData μ) {D : ℂ → ℂ}
    (hDtend : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => eLpNorm
      (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - D z) 2 ((volume : Measure ℂ).restrict K)) atTop (𝓝 0))
    {ψ : ℂ → ℂ} (hψcd : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ z, D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dz ψ z := by
  set K : Set ℂ := tsupport ψ with hKdef
  have hK : IsCompact K := hψcs
  have hψc : Continuous ψ := hψcd.continuous
  have hsupp : Function.support ψ ⊆ K := by rw [hKdef]; exact subset_closure
  have hu : ∀ n, MemLp (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2 ((volume : Measure ℂ).restrict K) :=
    memLp_dz_restrict_compact d hK
  have hpair := PLWD2.pairing_tendsto_of_eLpNorm hK hψc hsupp hu (hDtend K hK)
  have hIBP : ∀ n, ∫ z, dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * ψ z
      = -∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dz ψ z := by
    intro n
    have h := Work.MRMT.Beltrami.integral_mul_dz_eq_neg (d.contDiff_Fn n) hψcd hψcs
    rw [h]; ring
  have hdzψcont : Continuous (dz ψ) := continuous_dz_of_cd hψcd
  have hdzψcs : HasCompactSupport (dz ψ) := hasCompactSupport_dz_of_cd hψcs
  have hdxψsupp : Function.support (dz ψ) ⊆ K := by
    rw [hKdef]; exact Work.MRMT.QC.support_dz_subset ψ
  have hunif : TendstoUniformlyOn (fun n => ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ)) (d.φ : ℂ → ℂ) atTop K :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_Fn) K hK
  have hd := tendsto_integral_sub_mul_of_tendstoUniformlyOn_aux hK hunif hdxψsupp hdzψcont.continuousOn
  have hFnint : ∀ n, Integrable (fun z => ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dz ψ z) := by
    intro n
    exact (((d.Fn n).continuous.mul hdzψcont).integrable_of_hasCompactSupport hdzψcs.mul_left)
  have hφint : Integrable (fun z => (d.φ : ℂ → ℂ) z * dz ψ z) :=
    ((d.φ.continuous.mul hdzψcont).integrable_of_hasCompactSupport hdzψcs.mul_left)
  have hEq : (fun n => ∫ z, ((((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - (d.φ : ℂ → ℂ) z) * dz ψ z))
      = fun n => (∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dz ψ z)
          - (∫ z, (d.φ : ℂ → ℂ) z * dz ψ z) := by
    funext n
    rw [← integral_sub (hFnint n) hφint]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hEq] at hd
  have hFnlim : Tendsto (fun n => ∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dz ψ z) atTop
      (𝓝 (∫ z, (d.φ : ℂ → ℂ) z * dz ψ z)) :=
    tendsto_sub_nhds_zero_iff.mp hd
  have hneg : Tendsto (fun n => ∫ z, dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * ψ z) atTop
      (𝓝 (-∫ z, (d.φ : ℂ → ℂ) z * dz ψ z)) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n => (hIBP n).symm) hFnlim.neg
  exact tendsto_nhds_unique hpair hneg

/-- relation 2. -/
theorem dzbar_pairing_eq {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {D : ℂ → ℂ}
    (hDtend : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => eLpNorm
      (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - D z) 2 ((volume : Measure ℂ).restrict K)) atTop (𝓝 0))
    {ψ : ℂ → ℂ} (hψcd : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z := by
  set K : Set ℂ := tsupport ψ with hKdef
  have hK : IsCompact K := hψcs
  have hψc : Continuous ψ := hψcd.continuous
  have hsupp : Function.support ψ ⊆ K := by rw [hKdef]; exact subset_closure
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg (d.μn 0 0)) (d.norm_μn 0 0)
  have hμbdd : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ d.k := by
    filter_upwards [d.tendsto_μn] with z hz
    exact le_of_tendsto' ((continuous_norm.tendsto (μ z)).comp hz) fun n => d.norm_μn n z
  have hμnmeas : ∀ n, AEStronglyMeasurable (d.μn n) (volume : Measure ℂ) :=
    fun n => (d.contDiff_μn n).continuous.aestronglyMeasurable
  have hu : ∀ n, MemLp (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2 ((volume : Measure ℂ).restrict K) :=
    memLp_dz_restrict_compact d hK
  have hcon2 : Tendsto (fun n => eLpNorm (fun z => d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - μ z * D z) 2
      ((volume : Measure ℂ).restrict K)) atTop (𝓝 0) :=
    PLWD2.eLpNorm_mul_sub_tendsto hk0 hu (hDtend K hK) hμnmeas d.norm_μn hμ.meas hμbdd d.tendsto_μn
  have hu' : ∀ n, MemLp (fun z => d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2
      ((volume : Measure ℂ).restrict K) := by
    intro n
    have hcont : Continuous (fun z => d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) :=
      (d.contDiff_μn n).continuous.mul (continuous_dz_of_cd (d.contDiff_Fn n))
    refine (hu n).of_le_mul (c := d.k) hcont.aestronglyMeasurable ?_
    filter_upwards with z
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (d.norm_μn n z) (norm_nonneg _)
  have hpair := PLWD2.pairing_tendsto_of_eLpNorm hK hψc hsupp hu' hcon2
  have hbelt : ∀ n, ∫ z, d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * ψ z
      = -∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dzbar ψ z := by
    intro n
    have hb := Work.MRMT.QC.integral_mul_dzbar_eq_neg (d.contDiff_Fn n) hψcd hψcs
    simp only [d.beltrami_Fn n] at hb
    rw [hb]; ring
  have hdzbarψcont : Continuous (dzbar ψ) := continuous_dzbar_of_cd hψcd
  have hdzbarψcs : HasCompactSupport (dzbar ψ) := hasCompactSupport_dzbar_of_cd hψcs
  have hdbarψsupp : Function.support (dzbar ψ) ⊆ K := by
    rw [hKdef]; exact Work.MRMT.QC.support_dzbar_subset ψ
  have hunif : TendstoUniformlyOn (fun n => ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ)) (d.φ : ℂ → ℂ) atTop K :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_Fn) K hK
  have hd := tendsto_integral_sub_mul_of_tendstoUniformlyOn_aux hK hunif hdbarψsupp hdzbarψcont.continuousOn
  have hFnint : ∀ n, Integrable (fun z => ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dzbar ψ z) := by
    intro n
    exact (((d.Fn n).continuous.mul hdzbarψcont).integrable_of_hasCompactSupport hdzbarψcs.mul_left)
  have hφint : Integrable (fun z => (d.φ : ℂ → ℂ) z * dzbar ψ z) :=
    ((d.φ.continuous.mul hdzbarψcont).integrable_of_hasCompactSupport hdzbarψcs.mul_left)
  have hEq : (fun n => ∫ z, ((((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - (d.φ : ℂ → ℂ) z) * dzbar ψ z))
      = fun n => (∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dzbar ψ z)
          - (∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z) := by
    funext n
    rw [← integral_sub (hFnint n) hφint]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [hEq] at hd
  have hFnlim : Tendsto (fun n => ∫ z, ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * dzbar ψ z) atTop
      (𝓝 (∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) :=
    tendsto_sub_nhds_zero_iff.mp hd
  have hneg : Tendsto (fun n => ∫ z, d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * ψ z) atTop
      (𝓝 (-∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n => (hbelt n).symm) hFnlim.neg
  have huniq := tendsto_nhds_unique hpair hneg
  simpa only [mul_assoc] using huniq

theorem principalData_local_weak_derivative_measurable {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ)
    (d : Work.MRMT.Found.PrincipalData μ) (R : ℝ) (hR : 0 < R) :
    ∃ D : ℂ → ℂ,
      MeasureTheory.AEStronglyMeasurable D (MeasureTheory.volume.restrict (Metric.ball 0 R)) ∧
      MeasureTheory.IntegrableOn (fun z => ‖D z‖ ^ 2) (Metric.ball 0 R) MeasureTheory.volume ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * Work.MRMT.dz ψ z) ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z) := by
  obtain ⟨D, hDtend⟩ := d.dz_tendsto
  have hK0 : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have huc : ∀ n, MemLp (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2
      ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) := memLp_dz_restrict_compact d hK0
  have hDmem0 : MemLp D 2 ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) :=
    memLp_of_tendsto_eLpNorm_zero huc (hDtend _ hK0)
  obtain ⟨hAE, hInt⟩ := aesm_and_integrableOn_normSq_of_memLp_closedBall hDmem0
  exact ⟨D, hAE, hInt,
    fun ψ h1 h2 _ => dz_pairing_eq d hDtend h1 h2,
    fun ψ h1 h2 _ => dzbar_pairing_eq hμ d hDtend h1 h2⟩

end Work.MRMT.Found
