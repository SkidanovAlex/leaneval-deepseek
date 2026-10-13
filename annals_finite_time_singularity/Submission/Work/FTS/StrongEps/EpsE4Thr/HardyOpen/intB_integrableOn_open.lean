import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.H2.L12ZeroQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.HardyOpen

/-- The angular slice `z ↦ ∫_θ (f z θ)²` is a.e. strongly measurable on `(0,∞)` for a datum
which is merely continuous on the open quadrant. -/
theorem phi_aesm_of_continuousOn {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) from hcont)).pow 2
  have haesmJoint : AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hc
  have hnumIz : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  exact hnumIz.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
    (show Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz from Set.Ioi_subset_Ici_self))

/-- `intB` of `HardyHyp` in the *open* class: `z ↦ (∫_θ f z θ²)/z^{2j}` is integrable on `(0,∞)` for `j ≤ 2`, from `SmoothOpen f` (in place of `SmoothQuad f`) and `HkMem α 4 f`.  Verbatim adaptation of `Work.FTS.CoercivityFix.Coer1T.intB_integrableOn` (in `Submission/Work/FTS/CoercivityFix/Coer1T/HardyBasic.lean`), whose only use of `SmoothQuad` is the a.e. strong measurability of `z ↦ ∫_θ (f z θ)²`, which in the open class follows from `ContinuousOn (Function.uncurry f) Q0` via `Work.Spaces.aesm_of_continuousOn_Qd` (using `Work.FTS.EllipticEst.SmoothOpen.forall 0`); the domination step is `phi_div_rpow_le_B4` and `B4_integrableOn`, both of which need only `hmem`. -/
theorem intB_integrableOn_open (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ)
    (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)))
      (Set.Ioi 0) := by
  have hnum : AEMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (phi_aesm_of_continuousOn
      ((Work.FTS.EllipticEst.SmoothOpen.forall hsm 0).continuousOn)).aemeasurable
  have hden : AEMeasurable (fun z : ℝ => z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    have hEq : (fun z : ℝ => z ^ (2 * (j : ℝ))) = fun z => z ^ (2 * j) := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact ((continuous_pow (2 * j)).measurable).aemeasurable
  have haesm : AEStronglyMeasurable
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := (hnum.div hden).aestronglyMeasurable
  refine (Work.FTS.CoercivityFix.Coer1T.B4_integrableOn α f hmem).mono' haesm ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (div_nonneg (integral_nonneg fun θ => sq_nonneg _)
    (le_of_lt (Real.rpow_pos_of_pos hz _)))]
  exact Work.FTS.CoercivityFix.Coer1T.phi_div_rpow_le_B4 α hmem hz j hj

end Work.FTS.StrongEps.EpsE4Thr.HardyOpen
