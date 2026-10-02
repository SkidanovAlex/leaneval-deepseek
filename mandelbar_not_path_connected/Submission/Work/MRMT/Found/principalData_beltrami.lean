/-
Copyright: Work.MRMT (mandelbar) subproject.

# The principal solution of the Beltrami equation is a solution a.e.

`principalData_beltrami`: for an admissible coefficient `μ` and a `PrincipalData μ`, the
homeomorphism `φ` satisfies `∂̄φ = μ ∂φ` almost everywhere.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.QC.isQCOn_of_lipschitz
import Submission.Work.MRMT.Found.bump_scale_spec
import Submission.Work.MRMT.Found.integral_mul_wirtinger_moments
import Submission.Work.MRMT.Found.weak_relation_at_translate
import Submission.Work.MRMT.Found.tendsto_integral_bump_of_locallyIntegrable
import Submission.Work.MRMT.Found.integral_affine_mul_dzbar
import Submission.Work.MRMT.Found.integral_affine_mul_dz
import Submission.Work.MRMT.Found.principalData_local_weak_derivative_measurable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped ENNReal

namespace Work.MRMT.Found

/-! ## Placeholders for the lemmas still being produced -/






/-! ## Elementary facts -/

/-- The Wirtinger decomposition of the real Fréchet derivative. -/
theorem fderiv_apply_eq_dz (f : ℂ → ℂ) (z u : ℂ) :
    (fderiv ℝ f z) u = dz f z * u + dzbar f z * star u := by
  have h := Work.MRMT.QC.clm_apply_eq (fderiv ℝ f z) u
  rw [dz, dzbar]
  simpa using h

/-- `∂̄` of a `C¹` compactly supported function integrates to zero. -/
theorem integral_dzbar_eq_zero_of_cd (h : ℂ → ℂ) (hc : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) : ∫ u, dzbar h u = 0 :=
  Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff h (n := 1) (by norm_num) hc hs

/-- `∂` of a `C¹` compactly supported function integrates to zero. -/
theorem integral_dz_eq_zero_of_cd (h : ℂ → ℂ) (hc : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) : ∫ u, dz h u = 0 :=
  Work.MRMT.Beltrami.integral_dz_eq_zero_of_contDiff h (n := 1) (by norm_num) hc hs

/-- `dzbar` of a `C¹` function is continuous. -/
theorem continuous_dzbar_cd {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzbar f) :=
  Work.MRMT.QC.continuous_dzbar_of_contDiff' hf (by norm_num)

/-- `dz` of a `C¹` function is continuous. -/
theorem continuous_dz_cd {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dz f) :=
  Work.MRMT.QC.continuous_dz_of_contDiff' hf (by norm_num)

/-- `dzbar` of a `C¹` compactly supported function is compactly supported. -/
theorem hasCompactSupport_dzbar_cd {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dzbar f) := by
  refine IsCompact.of_isClosed_subset (show IsCompact (tsupport f) from hf)
    (isClosed_tsupport _) ?_
  exact (closure_mono (Work.MRMT.QC.support_dzbar_subset f)).trans
    (le_of_eq (isClosed_tsupport f).closure_eq)

/-- `dz` of a `C¹` compactly supported function is compactly supported. -/
theorem hasCompactSupport_dz_cd {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dz f) := by
  refine IsCompact.of_isClosed_subset (show IsCompact (tsupport f) from hf)
    (isClosed_tsupport _) ?_
  exact (closure_mono (Work.MRMT.QC.support_dz_subset f)).trans
    (le_of_eq (isClosed_tsupport f).closure_eq)

/-- An `L²` function on a ball is integrable after multiplication with the indicator of the
ball. -/
theorem integrable_indicator_of_integrableOn_sq {F : ℂ → ℂ} {R : ℝ}
    (hF : IntegrableOn (fun z => ‖F z‖ ^ 2) (Metric.ball 0 R) (volume : Measure ℂ))
    (hmeas : AEStronglyMeasurable F ((volume : Measure ℂ).restrict (Metric.ball 0 R))) :
    Integrable (Set.indicator (Metric.ball 0 R) F) (volume : Measure ℂ) := by
  haveI hfin : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    exact ne_top_of_le_ne_top
      (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hF' : Integrable (fun z => ‖F z‖ ^ 2)
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := hF
  have h1 : Integrable (fun z => (2 : ℝ)⁻¹ * (1 + ‖F z‖ ^ 2))
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
    ((integrable_const (1 : ℝ)).add hF').const_mul _
  have h2 : Integrable F ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
    refine h1.mono' hmeas ?_
    filter_upwards with z
    have hz : 0 ≤ ‖F z‖ := norm_nonneg _
    have h3 : ‖F z‖ ≤ (2 : ℝ)⁻¹ * (1 + ‖F z‖ ^ 2) := by
      nlinarith [sq_nonneg (‖F z‖ - 1), hz]
    simpa using h3
  exact MeasureTheory.IntegrableOn.integrable_indicator h2 Metric.isOpen_ball.measurableSet

/-- `LocallyIntegrable` of an integrable function. -/
theorem locallyIntegrable_of_integrable {f : ℂ → ℂ} (h : Integrable f (volume : Measure ℂ)) :
    LocallyIntegrable f (volume : Measure ℂ) :=
  MeasureTheory.locallyIntegrable_iff.mpr fun _ _ => h.integrableOn


/-! ## The main local argument -/

/-- At almost every point of `ball 0 (R-1)` (Lebesgue points of `D` and of `μD`), the
classical derivative of `φ`, where it exists, is given by `(D, μD)`. -/
theorem ae_beltrami_of_local_weak_derivative {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    {R : ℝ} (hR : 2 < R) {D : ℂ → ℂ}
    (hDmem : IntegrableOn (fun z => ‖D z‖ ^ 2) (Metric.ball 0 R) (volume : Measure ℂ))
    (hDmeas : AEStronglyMeasurable D ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
      (∫ z, D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dz ψ z) ∧
      (∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) :
    ∀ᵐ z ∂(volume.restrict (Metric.ball 0 (R - 1))),
      dzbar (d.φ : ℂ → ℂ) z = μ z * dz (d.φ : ℂ → ℂ) z := by
  set φ : ℂ → ℂ := (d.φ : ℂ → ℂ) with hφ
  have hφcont : Continuous φ := by rw [hφ]; exact d.φ.continuous
  obtain ⟨η, r, hηcd, hηcs, hsupp, hpos, hr, hint, hdbz, hdbd, hbm⟩ := bump_scale_spec
  obtain ⟨Cz, hCz⟩ := hdbz
  obtain ⟨Cd, hCd⟩ := hdbd
  have hμbdd : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ d.k := by
    filter_upwards [d.tendsto_μn] with z hz
    exact le_of_tendsto' ((continuous_norm.tendsto (μ z)).comp hz) fun n => d.norm_μn n z
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg _) (d.norm_μn 0 0)
  have hCznn : 0 ≤ Cz := by
    have h1 : 0 ≤ ∫ u, ‖dzbar (η 0) u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ Cz / r 0 := h1.trans (hCz 0)
    rcases div_nonneg_iff.mp h2 with h | h
    · exact h.1
    · exact absurd h.2 (not_le.mpr (hpos 0))
  have hCdd : 0 ≤ Cd := by
    have h1 : 0 ≤ ∫ u, ‖dz (η 0) u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ Cd / r 0 := h1.trans (hCd 0)
    rcases div_nonneg_iff.mp h2 with h | h
    · exact h.1
    · exact absurd h.2 (not_le.mpr (hpos 0))
  -- localised functions
  set D' : ℂ → ℂ := Set.indicator (Metric.ball 0 R) D with hD'
  set E' : ℂ → ℂ := Set.indicator (Metric.ball 0 R) (fun z => μ z * D z) with hE'
  have hDint : Integrable D' (volume : Measure ℂ) :=
    integrable_indicator_of_integrableOn_sq hDmem hDmeas
  have hEsq : IntegrableOn (fun z => ‖μ z * D z‖ ^ 2) (Metric.ball 0 R) (volume : Measure ℂ) := by
    have hdom : Integrable (fun z => d.k ^ 2 * ‖D z‖ ^ 2)
        ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := hDmem.const_mul _
    refine hdom.mono' ?_ ?_
    · exact ((hμ.meas.mono_measure MeasureTheory.Measure.restrict_le_self).mul
        hDmeas).norm.pow 2
    · filter_upwards [MeasureTheory.ae_restrict_of_ae hμbdd] with z hz
      have h1 : ‖μ z * D z‖ ^ 2 = ‖μ z‖ ^ 2 * ‖D z‖ ^ 2 := by rw [norm_mul, mul_pow]
      have h2 : ‖‖μ z * D z‖ ^ 2‖ = ‖μ z‖ ^ 2 * ‖D z‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h1]
      rw [h2]
      have h4 : ‖μ z‖ ^ 2 ≤ d.k ^ 2 := by nlinarith [hk0, norm_nonneg (μ z), hz]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hEmeas : AEStronglyMeasurable (fun z => μ z * D z)
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
    (hμ.meas.mono_measure MeasureTheory.Measure.restrict_le_self).mul hDmeas
  have hEint : Integrable E' (volume : Measure ℂ) :=
    integrable_indicator_of_integrableOn_sq hEsq hEmeas
  have hDloc : LocallyIntegrable D' (volume : Measure ℂ) := locallyIntegrable_of_integrable hDint
  have hEloc : LocallyIntegrable E' (volume : Measure ℂ) := locallyIntegrable_of_integrable hEint
  have hcontη : ∀ i, Continuous (η i) := fun i => (hηcd i).continuous
  have hconvD : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun i => ∫ u, D' (z + u) * η i u) atTop (𝓝 (D' z)) :=
    tendsto_integral_bump_of_locallyIntegrable hDloc hcontη hpos hr hint hbm hsupp
  have hconvE : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun i => ∫ u, E' (z + u) * η i u) atTop (𝓝 (E' z)) :=
    tendsto_integral_bump_of_locallyIntegrable hEloc hcontη hpos hr hint hbm hsupp
  have hEv1 : ∀ᶠ i in atTop, r i ≤ 1 := by
    filter_upwards [Filter.Tendsto.eventually hr (Metric.ball_mem_nhds (0 : ℝ) one_pos)]
      with i hi
    have := Metric.mem_ball.mp hi
    rw [Real.dist_eq, sub_zero, abs_lt] at this
    exact this.2.le
  have hgz : ∀ᵐ z ∂(volume.restrict (Metric.ball 0 (R - 1))),
      (Tendsto (fun i => ∫ u, D' (z + u) * η i u) atTop (𝓝 (D' z))) ∧
        (Tendsto (fun i => ∫ u, E' (z + u) * η i u) atTop (𝓝 (E' z))) :=
    (MeasureTheory.ae_restrict_of_ae (s := Metric.ball 0 (R - 1)) hconvD).and
      (MeasureTheory.ae_restrict_of_ae (s := Metric.ball 0 (R - 1)) hconvE)
  refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Metric.ball 0 (R - 1))
    Metric.isOpen_ball.measurableSet).mpr ?_
  filter_upwards [MeasureTheory.ae_imp_of_ae_restrict hgz] with z hz hzball
  obtain ⟨hzD, hzE⟩ := hz hzball
  have hznorm : ‖z‖ < R - 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hzball
    exact hzball
  have hzR : z ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hsub : ∀ i, r i ≤ 1 → tsupport (fun w => η i (w - z)) ⊆ Metric.ball 0 R := by
    intro i hri w hw
    rw [Metric.mem_ball, dist_zero_right]
    have key : ∀ ε : ℝ, 0 < ε → ‖w‖ ≤ r i + ‖z‖ + ε := by
      intro ε hε
      obtain ⟨y, hy, hyε⟩ := (Metric.mem_closure_iff.mp hw) ε hε
      have hyne : η i (y - z) ≠ 0 := Function.mem_support.mp hy
      have hyc : y - z ∈ Metric.closedBall (0 : ℂ) (r i) :=
        hsupp i (Function.mem_support.mpr hyne)
      have h3 : ‖y - z‖ ≤ r i := by simpa [dist_eq_norm] using hyc
      have h4 : ‖w - y‖ < ε := by simpa [dist_eq_norm] using hyε
      have h5 : ‖y‖ ≤ r i + ‖z‖ := by
        calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ r i + ‖z‖ := by linarith
      calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
        _ ≤ r i + ‖z‖ + ε := by linarith
    have h6 : ‖w‖ ≤ r i + ‖z‖ := le_of_forall_pos_le_add key
    linarith
  have htsuppη : ∀ i, tsupport (η i) ⊆ Metric.closedBall 0 (r i) := fun i =>
    (closure_mono (hsupp i)).trans (le_of_eq (Metric.isClosed_closedBall).closure_eq)
  -- integrability of the four products
  have hI1 : ∀ i, Integrable (fun u => dzbar (η i) u) := fun i =>
    (continuous_dzbar_cd (hηcd i)).integrable_of_hasCompactSupport
      (hasCompactSupport_dzbar_cd (hηcs i))
  have hI2 : ∀ i, Integrable (fun u => u * dzbar (η i) u) := fun i =>
    (continuous_id.mul (continuous_dzbar_cd (hηcd i))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_dzbar_cd (hηcs i)))
  have hI3 : ∀ i, Integrable (fun u => (starRingEnd ℂ) u * dzbar (η i) u) := fun i =>
    (continuous_star.mul (continuous_dzbar_cd (hηcd i))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_dzbar_cd (hηcs i)))
  have hJ1 : ∀ i, Integrable (fun u => dz (η i) u) := fun i =>
    (continuous_dz_cd (hηcd i)).integrable_of_hasCompactSupport (hasCompactSupport_dz_cd (hηcs i))
  have hJ2 : ∀ i, Integrable (fun u => u * dz (η i) u) := fun i =>
    (continuous_id.mul (continuous_dz_cd (hηcd i))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_dz_cd (hηcs i)))
  have hJ3 : ∀ i, Integrable (fun u => (starRingEnd ℂ) u * dz (η i) u) := fun i =>
    (continuous_star.mul (continuous_dz_cd (hηcd i))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_dz_cd (hηcs i)))
  by_cases hdiff : DifferentiableAt ℝ φ z
  · -- the differentiable case
    set a : ℂ := dz φ z with ha
    set b : ℂ := dzbar φ z with hb
    have hfderiv : ∀ u : ℂ, (fderiv ℝ φ z) u = a * u + b * star u := by
      intro u
      simpa only [← ha, ← hb] using fderiv_apply_eq_dz φ z u
    set e : ℂ → ℂ := fun u => φ (z + u) - φ z - (a * u + b * star u) with he
    have hecont : Continuous e := by
      rw [he]
      exact (((hφcont.comp (continuous_const.add continuous_id)).sub continuous_const).sub
        ((continuous_const.mul continuous_id).add (continuous_const.mul continuous_star)))
    have heo : e =o[𝓝 0] (fun u : ℂ => u) := by
      have ht : Tendsto (fun u : ℂ => z + u) (𝓝 0) (𝓝 z) := by
        have h := (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun u : ℂ => z + u) (𝓝 0) (𝓝 (z + 0)))
        simpa using h
      have hbase : (fun y : ℂ => φ y - φ z - (fderiv ℝ φ z) (y - z)) =o[𝓝 z]
          (fun y : ℂ => y - z) := hdiff.hasFDerivAt.isLittleO
      have hcomp := hbase.comp_tendsto ht
      have hfun : (fun u : ℂ => φ (z + u) - φ z - (a * u + b * star u))
          = (fun u : ℂ => φ (z + u) - φ z - (fderiv ℝ φ z) ((z + u) - z)) := by
        funext u
        rw [hfderiv]
        have huz : (z + u) - z = u := by ring
        rw [huz]
      have hg : (fun u : ℂ => u) = (fun u : ℂ => (z + u) - z) := by
        funext u
        have huz : (z + u) - z = u := by ring
        rw [huz]
      rw [he, hfun, hg]
      exact hcomp
    -- the error sequence tends to zero
    have herr_tend : Tendsto (fun i => ∫ u, e u * dzbar (η i) u) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hε' : 0 < ε / (Cz + 1) := by positivity
      rw [← Filter.eventually_atTop]
      obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (heo.def (c := ε / (Cz + 1)) hε')
      have hev : ∀ᶠ i in atTop, r i < min δ 1 := by
        filter_upwards [Filter.Tendsto.eventually hr
          (Metric.ball_mem_nhds (0 : ℝ) (lt_min hδpos one_pos))] with i hi
        have := Metric.mem_ball.mp hi
        rw [Real.dist_eq, sub_zero, abs_lt] at this
        exact this.2
      filter_upwards [hev] with i hi
      have hri1 : r i ≤ 1 := le_of_lt (hi.trans_le (min_le_right _ _))
      have hriδ : r i < δ := lt_of_lt_of_le hi (min_le_left _ _)
      have hdiffe : Integrable (fun u => e u * dzbar (η i) u) (volume : Measure ℂ) :=
        (hecont.mul (continuous_dzbar_cd (hηcd i))).integrable_of_hasCompactSupport
          (HasCompactSupport.mul_left (hasCompactSupport_dzbar_cd (hηcs i)))
      have hpt : ∀ᵐ u ∂(volume : Measure ℂ),
          ‖e u * dzbar (η i) u‖ ≤ (ε / (Cz + 1)) * r i * ‖dzbar (η i) u‖ := by
        filter_upwards with u
        rw [norm_mul]
        by_cases hu : dzbar (η i) u = 0
        · simp [hu]
        · have husupp : u ∈ tsupport (η i) :=
            Work.MRMT.QC.support_dzbar_subset (η i) (Function.mem_support.mpr hu)
          have h1 : ‖u‖ ≤ r i := by
            have := htsuppη i husupp
            simpa [dist_eq_norm] using this
          have h2 : ‖e u‖ ≤ (ε / (Cz + 1)) * ‖u‖ := hδ (by simpa [dist_eq_norm] using lt_of_le_of_lt h1 hriδ)
          have h3 : 0 ≤ ‖dzbar (η i) u‖ := norm_nonneg _
          calc ‖e u‖ * ‖dzbar (η i) u‖
              ≤ ((ε / (Cz + 1)) * ‖u‖) * ‖dzbar (η i) u‖ := by
                exact mul_le_mul_of_nonneg_right h2 h3
            _ ≤ ((ε / (Cz + 1)) * r i) * ‖dzbar (η i) u‖ := by
                refine mul_le_mul_of_nonneg_right ?_ h3
                exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hmono : (∫ u, ‖e u * dzbar (η i) u‖) ≤
          ∫ u, (ε / (Cz + 1)) * r i * ‖dzbar (η i) u‖ :=
        integral_mono_ae hdiffe.norm ((hI1 i).norm.const_mul _) hpt
      have hconst : (∫ u, (ε / (Cz + 1)) * r i * ‖dzbar (η i) u‖)
          = (ε / (Cz + 1)) * r i * (∫ u, ‖dzbar (η i) u‖) := by
        rw [MeasureTheory.integral_const_mul]
      have hle : (∫ u, ‖dzbar (η i) u‖) ≤ Cz / r i := hCz i
      have hmain : ‖∫ u, e u * dzbar (η i) u‖
          ≤ (ε / (Cz + 1)) * r i * (Cz / r i) := by
        calc ‖∫ u, e u * dzbar (η i) u‖ ≤ ∫ u, ‖e u * dzbar (η i) u‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ (ε / (Cz + 1)) * r i * (Cz / r i) := by
              rw [hconst] at hmono
              refine hmono.trans ?_
              refine mul_le_mul_of_nonneg_left hle ?_
              exact mul_nonneg (div_nonneg hε.le (by linarith)) (hpos i).le
      have hfin : (ε / (Cz + 1)) * r i * (Cz / r i) = ε * Cz / (Cz + 1) := by
        field_simp [ne_of_gt (hpos i)]
      rw [dist_eq_norm, sub_zero]
      refine lt_of_le_of_lt hmain ?_
      rw [hfin]
      have hden : (0 : ℝ) < Cz + 1 := by linarith
      calc ε * Cz / (Cz + 1) < ε * (Cz + 1) / (Cz + 1) := by
            exact div_lt_div_of_pos_right (by nlinarith [hε]) hden
        _ = ε := by field_simp
    -- the two limit relations
    have hEv : ∀ i, r i ≤ 1 →
        ∫ u, (μ (z + u) * D (z + u)) * η i u = b - ∫ u, e u * dzbar (η i) u := by
      intro i hri
      have hwr := weak_relation_at_translate hweak (hηcd i) (hηcs i) z (hsub i hri)
      have hmo := integral_mul_wirtinger_moments (hηcd i) (hηcs i)
      have hexp : ∫ u, φ (z + u) * dzbar (η i) u = -b + ∫ u, e u * dzbar (η i) u := by
        have hpt : ∀ u : ℂ, φ (z + u) = φ z + (a * u + b * star u) + e u := by
          intro u
          rw [he]
          dsimp only
          ring
        calc ∫ u, φ (z + u) * dzbar (η i) u
            = ∫ u, (φ z + (a * u + b * (starRingEnd ℂ) u) + e u) * dzbar (η i) u := by
              refine integral_congr_ae (Eventually.of_forall fun u => ?_)
              dsimp only
              rw [hpt u]
              simp only [starRingEnd_apply]
          _ = -b + ∫ u, e u * dzbar (η i) u :=
              integral_affine_mul_dzbar (hηcd i) (hηcs i) (hI1 i) (hI2 i) (hI3 i)
                (integral_dzbar_eq_zero_of_cd (η i) (hηcd i) (hηcs i)) hmo.1
                (by rw [hmo.2.1, hint i]) (φ z) a b e hecont
                (hecont.mul (continuous_dzbar_cd (hηcd i)) |>.integrable_of_hasCompactSupport
                  (HasCompactSupport.mul_left (hasCompactSupport_dzbar_cd (hηcs i))))
      rw [hwr.2] at hexp
      linear_combination -hexp
    have hDd : ∀ i, r i ≤ 1 →
        ∫ u, D (z + u) * η i u = a - ∫ u, e u * dz (η i) u := by
      intro i hri
      have hwr := weak_relation_at_translate hweak (hηcd i) (hηcs i) z (hsub i hri)
      have hmo := integral_mul_wirtinger_moments (hηcd i) (hηcs i)
      have hexp : ∫ u, φ (z + u) * dz (η i) u = -a + ∫ u, e u * dz (η i) u := by
        have hpt : ∀ u : ℂ, φ (z + u) = φ z + (a * u + b * star u) + e u := by
          intro u
          rw [he]
          dsimp only
          ring
        calc ∫ u, φ (z + u) * dz (η i) u
            = ∫ u, (φ z + (a * u + b * (starRingEnd ℂ) u) + e u) * dz (η i) u := by
              refine integral_congr_ae (Eventually.of_forall fun u => ?_)
              dsimp only
              rw [hpt u]
              simp only [starRingEnd_apply]
          _ = -a + ∫ u, e u * dz (η i) u :=
              integral_affine_mul_dz (hηcd i) (hηcs i) (hJ1 i) (hJ2 i) (hJ3 i)
                (integral_dz_eq_zero_of_cd (η i) (hηcd i) (hηcs i))
                (by rw [hmo.2.2.1, hint i]) hmo.2.2.2 (φ z) a b e hecont
                (hecont.mul (continuous_dz_cd (hηcd i)) |>.integrable_of_hasCompactSupport
                  (HasCompactSupport.mul_left (hasCompactSupport_dz_cd (hηcs i))))
      rw [hwr.1] at hexp
      linear_combination -hexp
    -- limits
    have hlimE : Tendsto (fun i => ∫ u, (μ (z + u) * D (z + u)) * η i u) atTop (𝓝 b) := by
      have h0 : Tendsto (fun i => b - ∫ u, e u * dzbar (η i) u) atTop (𝓝 b) := by
        simpa using (tendsto_const_nhds.sub herr_tend)
      exact Filter.Tendsto.congr' (hEv1.mono fun i hi => (hEv i hi).symm) h0
    have hlimE' : Tendsto (fun i => ∫ u, (μ (z + u) * D (z + u)) * η i u) atTop (𝓝 (E' z)) := by
      refine Filter.Tendsto.congr' ?_ hzE
      filter_upwards [hEv1] with i hi
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      by_cases hu : η i u = 0
      · simp [hu]
      · have hu' : u ∈ Function.support (η i) := Function.mem_support.mpr hu
        have h1 : ‖u‖ ≤ r i := by
          have := hsupp i hu'
          simpa [dist_eq_norm] using this
        have h2 : z + u ∈ Metric.ball 0 R := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z + u‖ ≤ ‖z‖ + ‖u‖ := norm_add_le _ _
            _ ≤ ‖z‖ + r i := by linarith
            _ < (R - 1) + 1 := by linarith
            _ = R := by ring
        rw [hE', Set.indicator_of_mem h2]
    have hbE : b = E' z := (tendsto_nhds_unique hlimE' hlimE).symm
    have hlimD : Tendsto (fun i => ∫ u, D (z + u) * η i u) atTop (𝓝 a) := by
      have herr2 : Tendsto (fun i => ∫ u, e u * dz (η i) u) atTop (𝓝 0) := by
        -- same argument, with `dz` in place of `dzbar`
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hε' : 0 < ε / (Cd + 1) := by positivity
        rw [← Filter.eventually_atTop]
        obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (heo.def (c := ε / (Cd + 1)) hε')
        have hev : ∀ᶠ i in atTop, r i < min δ 1 := by
          filter_upwards [Filter.Tendsto.eventually hr
            (Metric.ball_mem_nhds (0 : ℝ) (lt_min hδpos one_pos))] with i hi
          have := Metric.mem_ball.mp hi
          rw [Real.dist_eq, sub_zero, abs_lt] at this
          exact this.2
        filter_upwards [hev] with i hi
        have hri1 : r i ≤ 1 := le_of_lt (hi.trans_le (min_le_right _ _))
        have hriδ : r i < δ := lt_of_lt_of_le hi (min_le_left _ _)
        have hdiffe : Integrable (fun u => e u * dz (η i) u) (volume : Measure ℂ) :=
          (hecont.mul (continuous_dz_cd (hηcd i))).integrable_of_hasCompactSupport
            (HasCompactSupport.mul_left (hasCompactSupport_dz_cd (hηcs i)))
        have hpt : ∀ᵐ u ∂(volume : Measure ℂ),
            ‖e u * dz (η i) u‖ ≤ (ε / (Cd + 1)) * r i * ‖dz (η i) u‖ := by
          filter_upwards with u
          rw [norm_mul]
          by_cases hu : dz (η i) u = 0
          · simp [hu]
          · have husupp : u ∈ tsupport (η i) :=
              Work.MRMT.QC.support_dz_subset (η i) (Function.mem_support.mpr hu)
            have h1 : ‖u‖ ≤ r i := by
              have := htsuppη i husupp
              simpa [dist_eq_norm] using this
            have h2 : ‖e u‖ ≤ (ε / (Cd + 1)) * ‖u‖ :=
              hδ (by simpa [dist_eq_norm] using lt_of_le_of_lt h1 hriδ)
            have h3 : 0 ≤ ‖dz (η i) u‖ := norm_nonneg _
            calc ‖e u‖ * ‖dz (η i) u‖ ≤ ((ε / (Cd + 1)) * ‖u‖) * ‖dz (η i) u‖ :=
                  mul_le_mul_of_nonneg_right h2 h3
              _ ≤ ((ε / (Cd + 1)) * r i) * ‖dz (η i) u‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ h3
                  exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hmono : (∫ u, ‖e u * dz (η i) u‖) ≤
            ∫ u, (ε / (Cd + 1)) * r i * ‖dz (η i) u‖ :=
          integral_mono_ae hdiffe.norm ((hJ1 i).norm.const_mul _) hpt
        have hconst : (∫ u, (ε / (Cd + 1)) * r i * ‖dz (η i) u‖)
            = (ε / (Cd + 1)) * r i * (∫ u, ‖dz (η i) u‖) := by
          rw [MeasureTheory.integral_const_mul]
        have hle : (∫ u, ‖dz (η i) u‖) ≤ Cd / r i := hCd i
        have hmain : ‖∫ u, e u * dz (η i) u‖ ≤ (ε / (Cd + 1)) * r i * (Cd / r i) := by
          calc ‖∫ u, e u * dz (η i) u‖ ≤ ∫ u, ‖e u * dz (η i) u‖ :=
                MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ (ε / (Cd + 1)) * r i * (Cd / r i) := by
                rw [hconst] at hmono
                refine hmono.trans ?_
                refine mul_le_mul_of_nonneg_left hle ?_
                exact mul_nonneg (div_nonneg hε.le (by linarith)) (hpos i).le
        have hfin : (ε / (Cd + 1)) * r i * (Cd / r i) = ε * Cd / (Cd + 1) := by
          field_simp [ne_of_gt (hpos i)]
        rw [dist_eq_norm, sub_zero]
        refine lt_of_le_of_lt hmain ?_
        rw [hfin]
        have hden : (0 : ℝ) < Cd + 1 := by linarith
        calc ε * Cd / (Cd + 1) < ε * (Cd + 1) / (Cd + 1) := by
              exact div_lt_div_of_pos_right (by nlinarith [hε]) hden
          _ = ε := by field_simp
      have h0 : Tendsto (fun i => a - ∫ u, e u * dz (η i) u) atTop (𝓝 a) := by
        simpa using (tendsto_const_nhds.sub herr2)
      exact Filter.Tendsto.congr' (hEv1.mono fun i hi => (hDd i hi).symm) h0
    have hlimD' : Tendsto (fun i => ∫ u, D (z + u) * η i u) atTop (𝓝 (D' z)) := by
      refine Filter.Tendsto.congr' ?_ hzD
      filter_upwards [hEv1] with i hi
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      by_cases hu : η i u = 0
      · simp [hu]
      · have hu' : u ∈ Function.support (η i) := Function.mem_support.mpr hu
        have h1 : ‖u‖ ≤ r i := by
          have := hsupp i hu'
          simpa [dist_eq_norm] using this
        have h2 : z + u ∈ Metric.ball 0 R := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z + u‖ ≤ ‖z‖ + ‖u‖ := norm_add_le _ _
            _ ≤ ‖z‖ + r i := by linarith
            _ < (R - 1) + 1 := by linarith
            _ = R := by ring
        rw [hD', Set.indicator_of_mem h2]
    have haD : a = D' z := (tendsto_nhds_unique hlimD' hlimD).symm
    have hEz : E' z = μ z * D z := by
      rw [hE', Set.indicator_of_mem hzR]
    have hDz : D' z = D z := by
      rw [hD', Set.indicator_of_mem hzR]
    calc dzbar φ z = b := hb.symm
      _ = E' z := hbE
      _ = μ z * D z := hEz
      _ = μ z * D' z := by rw [hDz]
      _ = μ z * a := by rw [← haD]
      _ = μ z * dz φ z := by rw [← ha]
  · -- the non-differentiable case
    have hzero : fderiv ℝ φ z = 0 := fderiv_zero_of_not_differentiableAt hdiff
    have h1 : dz φ z = 0 := by
      simp only [dz, hzero]
      simp
    have h2 : dzbar φ z = 0 := by
      simp only [dzbar, hzero]
      simp
    rw [h1, h2, mul_zero]

/-! ## The principal solution -/

theorem principalData_beltrami {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      dzbar (d.φ : ℂ → ℂ) z = μ z * dz (d.φ : ℂ → ℂ) z := by
  have hkey : ∀ j : ℕ, ∀ᵐ z ∂(volume.restrict (Metric.ball 0 (j : ℝ))),
      dzbar (d.φ : ℂ → ℂ) z = μ z * dz (d.φ : ℂ → ℂ) z := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    obtain ⟨D, hDmeas, hDmem, hD1, hD2⟩ :=
      principalData_local_weak_derivative_measurable hμ d ((j : ℝ) + 3) (by linarith)
    have hR : 2 < (j : ℝ) + 3 := by linarith
    have hmain := ae_beltrami_of_local_weak_derivative hμ d (R := (j : ℝ) + 3) hR hDmem hDmeas
      (fun ψ hψ hψc hψt => ⟨hD1 ψ hψ hψc hψt, hD2 ψ hψ hψc hψt⟩)
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset ?_ hmain
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith
  have hall : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j : ℕ, z ∈ Metric.ball 0 (j : ℝ) →
      dzbar (d.φ : ℂ → ℂ) z = μ z * dz (d.φ : ℂ → ℂ) z :=
    MeasureTheory.ae_all_iff.mpr fun j =>
      MeasureTheory.ae_imp_of_ae_restrict (hkey j)
  filter_upwards [hall] with z hz
  obtain ⟨j, hj⟩ := exists_nat_gt (‖z‖)
  exact hz j (by rw [Metric.mem_ball, dist_zero_right]; exact hj)

end Work.MRMT.Found
