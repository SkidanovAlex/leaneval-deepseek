import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open MeasureTheory Set Filter
open scoped Real Topology

/-- **A.e. strong measurability of the angular integral
`s ↦ ∫_θ |K_θ θ| · |D_z^j g s θ| / s` on `(0,∞)`, for `g` smooth on the open quadrant.**

The integrand `(s,θ) ↦ |K_θ θ| · |D_z^j g s θ| / s` is continuous on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (the `D_z`-iterate of `g` is `C^∞` there and `s ↦ s` does not vanish),
hence a.e. strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`).  Fubini's measurability clause
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then makes the `θ`-marginal
a.e. strongly measurable w.r.t. `volume.restrict Iz`, and `Iz = [0,∞)` agrees a.e. with
`(0,∞)` since `{0}` is null. -/
theorem aesm_integral_abs_Ktheta_dzIter (j : ℕ) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- the angular factor `θ ↦ |K_θ θ|` is continuous
  have hK : Continuous (fun θ : ℝ => |Work.Elliptic.Ktheta θ|) := by
    simp only [Work.Elliptic.Ktheta]
    fun_prop
  -- the joint integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Work.Elliptic.Ktheta p.2| * |Work.Spaces.DzIter j g p.1 p.2| / p.1)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Elliptic.Ktheta p.2|)
        (Work.FTS.EllipticEst.Q0) := (hK.comp continuous_snd).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.DzIter j g p.1 p.2|)
        (Work.FTS.EllipticEst.Q0) :=
      ((hsm.DzIter j).continuousOn).abs
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℝ)) (Work.FTS.EllipticEst.Q0) :=
      continuousOn_fst
    refine (h1.mul h2).div h3 (fun p hp => ?_)
    exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  -- a.e. strong measurability of the uncurried integrand for the product measure
  have hX : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      |Work.Elliptic.Ktheta p.2| * |Work.Spaces.DzIter j g p.1 p.2| / p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- the `θ`-marginal is a.e. strongly measurable w.r.t. `volume.restrict Iz`
  have hInner : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ))).symm)
  rw [← hmeas]
  exact hInner

end Work.FTS_EllLimOK.ThetaJets
