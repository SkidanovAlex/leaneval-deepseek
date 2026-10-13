import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

-- the hypotheses `0 < δ` and `0 < z` of the statement are not needed for measurability
set_option linter.unusedVariables false

/-- **Joint continuity of the Schur integrand.**  For a datum `C^∞` on the open quadrant, the
function

  `(s, t) ↦ sKerd δ (log z - t) · ∂_θG(e^t, s)`

is continuous on `(0, π/2) × ℝ`: the kernel factor is a continuous function of `t`, while the
point `(e^t, s)` lies in the open quadrant, where `∂_θG` is continuous (and the map
`(s,t) ↦ (e^t, s)` is continuous). -/
theorem continuousOn_sKerd_pth_joint {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (δ z : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2)
        * Work.Spaces.pth G (Real.exp p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) := by
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth G (Real.exp p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) := by
    have hbase : ContinuousOn (Function.uncurry (Work.Spaces.pth G)) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.SmoothOpen.pth hG).continuousOn
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.2, p.1)) :=
      (Real.continuous_exp.comp continuous_snd).prodMk continuous_fst
    have hmap : MapsTo (fun p : ℝ × ℝ => (Real.exp p.2, p.1))
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Set.mem_prod] at hp
      show (Real.exp p.2, p.1) ∈ Work.FTS.EllipticEst.Q0
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos p.2, hp.1.1, hp.1.2⟩
    exact (hbase.comp hφ.continuousOn hmap).congr (fun p _ => rfl)
  have hK : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) :=
    ((Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).comp
      (continuous_const.sub continuous_snd)).continuousOn
  exact hK.mul hpth

/-- **A.e. strong measurability of the weighted square of the Schur transform of an angular
derivative.**  For fixed `δ ≥ 0` and `z`, the function

  `s ↦ sin(2s)^{-η} · (zSchur δ (fun w => ∂_θG(w,s)) z)²`

is a.e. strongly measurable on the angular interval `Iθ = [0, π/2]`.

The proof unwinds `zSchur` as the `t`-integral of the jointly continuous density
`(s,t) ↦ sKerd δ (log z - t) · ∂_θG(e^t, s)` (`continuousOn_sKerd_pth_joint`); Fubini's
measurability theorem `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` then gives the
a.e. strong measurability of the marginal in `s`, and `sin(2s)^{-η}` is everywhere continuous. -/
theorem aesm_thEta_zSchur_pth_sq (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (δ : ℝ) (hδ : 0 < δ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.FTS.EllipticEst.thEta s
        * (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- the (measurable) set on which the joint integrand is continuous
  have hmeasU : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.2)
        * Work.Spaces.pth G (Real.exp p.2) p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ (Set.univ : Set ℝ))) :=
    (continuousOn_sKerd_pth_joint hG δ z).aestronglyMeasurable hmeasU
  -- rewrite the restricted product measure as the product of the restricted measure
  rw [← MeasureTheory.Measure.restrict_prod_eq_prod_univ] at hjoint
  -- Fubini: the marginal in `s` is a.e. strongly measurable
  have hzschur : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => zSchur δ (fun w => Work.Spaces.pth G w s) z)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    simpa only [zSchur] using hjoint.integral_prod_right'
  have hsq : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hzschur.pow 2
  have hfull : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.FTS.EllipticEst.thEta s
        * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_thEta.aestronglyMeasurable (μ :=
      MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))).mul hsq
  -- transfer from the open interval to `Iθ = [0, π/2]` (the two endpoints are null)
  have hIθ : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  rw [hIθ]
  exact hfull

end Work.FTS.EllSol.EllPkgAux.MollDom
