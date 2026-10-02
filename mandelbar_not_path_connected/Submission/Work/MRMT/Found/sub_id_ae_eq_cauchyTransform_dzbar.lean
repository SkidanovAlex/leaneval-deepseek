import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_inversion
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Weyl.weyl_lemma
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay
import Submission.Work.MRMT.Sobolev.isDbarDeriv_id_add
import Submission.Work.MRMT.Found.beurlingL2_eq_cauchyTransform_dz

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-- An entire function which agrees a.e. with a function decaying like `C / ‖z‖` at infinity
vanishes identically.

Indeed, let `E = {z | u z ≠ g z}` (null) and let `D = {z | R₀ < ‖z‖ ∧ C / ‖z‖ < ‖u z‖}` with
`R₀ = max R 1 > 0`.  On `D` one has `u ≠ g` (otherwise `‖g z‖ ≤ C / ‖z‖` contradicts the defining
inequality), so `D ⊆ E` is null; but `D` is open (`R₀ < ‖z‖` is open and, where it holds,
`C / ‖z‖ < ‖u z‖ ⟺ 0 < ‖z‖ ‖u z‖ − C`), hence empty.  So `‖u z‖ ≤ C / ‖z‖` for `‖z‖ > R₀`, and
`u → 0` along the cocompact filter; Liouville's theorem (`Differentiable.apply_eq_of_tendsto_cocompact`)
then gives `u = 0`. -/
private theorem analytic_decay_zero {u g : ℂ → ℂ}
    (hu : AnalyticOn ℂ u Set.univ)
    (heq : u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] g)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z‖ ≤ C / ‖z‖) : u = 0 := by
  have hudiff : Differentiable ℂ u := by
    have h := hu.differentiableOn
    rwa [differentiableOn_univ] at h
  have hcont : Continuous u := hudiff.continuous
  obtain ⟨C, R, hCR⟩ := hdec
  have hE0 : volume {z : ℂ | ¬ (u z = g z)} = 0 := MeasureTheory.ae_iff.mp heq
  let R₀ : ℝ := max R 1
  have hR₀1 : 1 ≤ R₀ := le_max_right R 1
  have hRR₀ : R ≤ R₀ := le_max_left R 1
  let D : Set ℂ := {z : ℂ | R₀ < ‖z‖ ∧ C / ‖z‖ < ‖u z‖}
  have hDsub : D ⊆ {z : ℂ | ¬ (u z = g z)} := by
    intro z hz
    have hz' : R₀ < ‖z‖ ∧ C / ‖z‖ < ‖u z‖ := hz
    obtain ⟨hzR, hzC⟩ := hz'
    show ¬ (u z = g z)
    intro hzug
    have hb : ‖g z‖ ≤ C / ‖z‖ := hCR z (le_trans hRR₀ hzR.le)
    rw [hzug] at hzC
    exact (not_lt_of_ge hb) hzC
  have hDnull : volume D = 0 := measure_mono_null hDsub hE0
  have hDopen : IsOpen D := by
    have hA : IsOpen {z : ℂ | R₀ < ‖z‖} := isOpen_lt continuous_const continuous_norm
    have hB : IsOpen {z : ℂ | (0 : ℝ) < ‖u z‖ * ‖z‖ - C} :=
      isOpen_lt continuous_const ((hcont.norm.mul continuous_norm).sub continuous_const)
    have hDeq : D = {z : ℂ | R₀ < ‖z‖} ∩ {z : ℂ | (0 : ℝ) < ‖u z‖ * ‖z‖ - C} := by
      ext z
      simp only [D, Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have hzpos : 0 < ‖z‖ := lt_trans (by linarith [hR₀1] : (0 : ℝ) < R₀) h1
        exact ⟨h1, sub_pos.mpr ((div_lt_iff₀ hzpos).mp h2)⟩
      · rintro ⟨h1, h2⟩
        have hzpos : 0 < ‖z‖ := lt_trans (by linarith [hR₀1] : (0 : ℝ) < R₀) h1
        exact ⟨h1, (div_lt_iff₀ hzpos).mpr (sub_pos.mp h2)⟩
    rw [hDeq]
    exact hA.inter hB
  have hDempty : D = ∅ := hDopen.eq_empty_of_measure_zero hDnull
  have hbound : ∀ z : ℂ, R₀ < ‖z‖ → ‖u z‖ ≤ C / ‖z‖ := by
    intro z hz
    have hznot : z ∉ D := by rw [hDempty]; exact Set.notMem_empty z
    exact not_lt.mp (fun h => hznot ⟨hz, h⟩)
  have htend : Tendsto u (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.hasBasis_cocompact.eventually_iff]
    refine ⟨Metric.closedBall 0 (max R₀ (C / ε)), isCompact_closedBall _ _, ?_⟩
    intro z hz
    have hzT : max R₀ (C / ε) < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzR : R₀ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hzT
    have hzpos : 0 < ‖z‖ := lt_trans (by linarith [hR₀1] : (0 : ℝ) < R₀) hzR
    have hCs : C / ε < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hzT
    have hlt : C < ε * ‖z‖ := by
      have h := (div_lt_iff₀ hε).mp hCs
      linarith
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hbound z hzR) ((div_lt_iff₀ hzpos).mpr hlt)
  funext z
  exact hudiff.apply_eq_of_tendsto_cocompact z htend

/-- `F - z` agrees a.e. with the Cauchy transform of `∂̄ F`.

This is the "other direction" of `Work.MRMT.Beltrami.cauchyTransform_inversion`: if `∂̄ F` is
continuous with compact support and `F z - z = O(1/‖z‖)` at infinity, then
`F - z = C(∂̄ F)` a.e.  The proof shows that the weak `∂̄`-derivative of
`(F - z) - C(∂̄ F)` vanishes, so by Weyl's lemma it agrees a.e. with an entire function; the
`1/‖z‖` decay of both `F - z` (hypothesis) and `C(∂̄ F)` (smooth kernel estimate) forces that
entire function to vanish. -/
theorem sub_id_ae_eq_cauchyTransform_dzbar {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport (fun z => Work.MRMT.dzbar F z))
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    (fun z => F z - z) =ᵐ[MeasureTheory.volume]
      Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) := by
  have hFdb : Work.MRMT.IsDbarDeriv F (fun w => Work.MRMT.dzbar F w) :=
    Work.MRMT.Weyl.isDbarDeriv_dzbar hF (by norm_num)
  have hωcont : Continuous (fun w => Work.MRMT.dzbar F w) :=
    Work.MRMT.Weyl.continuous_dzbar_of_contDiff hF (by norm_num)
  have hωint : Integrable (fun w => Work.MRMT.dzbar F w) volume :=
    hωcont.integrable_of_hasCompactSupport hs
  have hGdb : Work.MRMT.IsDbarDeriv (Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w))
      (fun w => Work.MRMT.dzbar F w) :=
    Work.MRMT.Beltrami.cauchyTransform_inversion _ hωint
  have hid0 : Work.MRMT.IsDbarDeriv (fun z : ℂ => z) (0 : ℂ → ℂ) :=
    Work.MRMT.Sobolev.isDbarDeriv_id_zero_aux
  -- the weak `∂̄`-derivative of `(F - C(∂̄F)) - z` vanishes
  have hsub0 : Work.MRMT.IsDbarDeriv
      (fun z => (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z)
      (0 : ℂ → ℂ) := by
    have h1 : Work.MRMT.IsDbarDeriv
        (fun z => F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z)
        (fun z => Work.MRMT.dzbar F z - Work.MRMT.dzbar F z) :=
      isDbarDeriv_sub hFdb hGdb
    have h2 : Work.MRMT.IsDbarDeriv
        (fun z => F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z)
        (0 : ℂ → ℂ) :=
      Work.MRMT.Weyl.isDbarDeriv_congr h1 (fun z => sub_self _)
    have h3 : Work.MRMT.IsDbarDeriv
        (fun z => (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z)
        (fun z => (0 : ℂ) - 0) :=
      isDbarDeriv_sub h2 hid0
    exact Work.MRMT.Weyl.isDbarDeriv_congr h3 (fun z => sub_zero 0)
  have hloc : LocallyIntegrable
      (fun z => (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z)
      volume := hsub0.1
  have hwc : Work.MRMT.IsWeaklyConformal
      (fun z => (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z) :=
    ⟨0, hsub0, Eventually.of_forall (fun z => rfl)⟩
  obtain ⟨u, hua, hueq⟩ := Work.MRMT.Weyl.weyl_lemma hloc hwc
  -- decay of the Cauchy transform of the compactly supported `∂̄ F`
  obtain ⟨M, hM0, hM⟩ :=
    Work.MRMT.Beltrami.decay_exists_support_radius (fun w => Work.MRMT.dzbar F w) hs
  have hdecCtF : ∀ z : ℂ, max 1 (2 * M) ≤ ‖z‖ →
      ‖Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z‖
        ≤ (2 * (∫ ζ, ‖Work.MRMT.dzbar F ζ‖)) / Real.pi / ‖z‖ := by
    intro z hz
    exact Work.MRMT.Beltrami.decay_cauchyTransform_le _ hωint.norm hM
      (le_trans (le_max_left _ _) hz) (le_trans (le_max_right _ _) hz)
  obtain ⟨C, R, hCR⟩ := hdec
  -- decay of `(F - C(∂̄F)) - z`
  have hdecH : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖(F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z‖ ≤ C / ‖z‖ := by
    refine ⟨C + (2 * (∫ ζ, ‖Work.MRMT.dzbar F ζ‖)) / Real.pi,
      max R (max 1 (2 * M)), fun z hz => ?_⟩
    have hzR : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have hzG : max 1 (2 * M) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    have h1 : (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z
        = (F z - z) - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z := by ring
    rw [h1]
    calc ‖(F z - z) - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z‖
        ≤ ‖F z - z‖ + ‖Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z‖ :=
          norm_sub_le _ _
      _ ≤ C / ‖z‖ + (2 * (∫ ζ, ‖Work.MRMT.dzbar F ζ‖)) / Real.pi / ‖z‖ :=
          add_le_add (hCR z hzR) (hdecCtF z hzG)
      _ = (C + (2 * (∫ ζ, ‖Work.MRMT.dzbar F ζ‖)) / Real.pi) / ‖z‖ := by ring
  have hu0 : u = 0 := analytic_decay_zero hua hueq.symm hdecH
  have hH0 : (fun z => (F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z) - z)
      =ᵐ[volume] (0 : ℂ → ℂ) := by
    filter_upwards [hueq] with z hz
    rw [hu0] at hz
    simpa using hz
  filter_upwards [hH0] with z hz
  have h2 : F z - Work.MRMT.cauchyTransform (fun w => Work.MRMT.dzbar F w) z = z :=
    sub_eq_zero.mp hz
  linear_combination h2

end Work.MRMT.Found
