/-
# `ModalSolR/PerMode` — the per-mode weak identity on the open quadrant

Assembles `perMode_box` (`ModalSolR/PerModeInner`) with the reduction of both sides to the box
containing the support of the test function and the Fubini theorem.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.ModalSolR.PerModeInner

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

set_option maxHeartbeats 3200000
/-! ## The operator applied to a smooth function is continuous -/

/-- `bslOp α ψ` is continuous on the open quadrant for a smooth `ψ`. -/
theorem continuousOn_bslOp {α : ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pz).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.EllipticEst.ModalSolution.continuousOn_Lzero hψ
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := continuousOn_fst
  have h4 : ContinuousOn (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2)) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul (hz.pow 2)).neg
  have h5 : ContinuousOn (fun p : ℝ × ℝ => α * (5 + α) * p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.mul hz
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 ψ p.1 p.2
        - (α * (5 + α) * p.1) * Work.Spaces.pz ψ p.1 p.2
        + Work.Elliptic.Lzero ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((h4.mul h1).sub (h5.mul h2)).add h3
  simpa only [Work.Elliptic.bslOp_apply] using hmain

/-! ## The per-mode identity on the quadrant -/

/-- **The per-mode weak identity.** -/
theorem perModeQ0 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
            * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ## integrability on the box
  have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact (radGreenContinuousOn hα hα1 m hc2 hcm).mono
      (fun z hz => lt_of_lt_of_le ha hz.1)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  have hzq : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 ^ ((5 - α) / α) * Real.cos p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.rpow_const (fun p hp =>
      Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
      (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  have hbsl : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α φ p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) := (continuousOn_bslOp hφsm).mono hKsub
  have hLint : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((((hAcont.comp continuousOn_fst (fun p hp => hp.1)).mul
      (hem.comp_continuousOn continuousOn_snd)).mul hbsl).mul hzq).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2
      * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((hem.comp_continuousOn continuousOn_snd).mul (hφsm.continuousOn.mono hKsub)).mul hzq
  have hRint : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hbase := Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable hc2 hcm ha hab.le
      hc0 hcd.le hg
    refine hbase.congr_fun (fun p _ => ?_) hKmeas
    ring
  -- ## reduction of both sides to the box
  have hLred : (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [bslOp_eq_zero_off_box hbox hp.2]
      ring)
  have hRred : (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
        (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      have hφ0 : φ p.1 p.2 = 0 := by
        by_cases h1 : p.1 ∈ Set.Ioo a b
        · exact test_vanishes_off_theta hbox
            (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩)
        · exact test_vanishes_off_z hbox h1
      rw [hφ0]
      ring)
  rw [hLred, hRred, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.setIntegral_prod _ hLint, MeasureTheory.setIntegral_prod _ hRint]
  exact perMode_box α hα hα1 m hm hc2 hcm hφ hφc hφs ha hab hc0 hcd hd hbox

end Work.FTS.H2.ModalSolR
