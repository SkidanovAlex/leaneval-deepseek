import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

namespace Z3Clean

set_option autoImplicit false


/-- The radial weight `w` does not vanish at any `z > 0`. -/
lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ≠ 0 := by linarith
  simp only [Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 (ne_of_gt hz))

/-- The radial weight `w` is measurable. -/
lemma measurable_w : Measurable (fun z : ℝ => Spaces.w z) := by
  show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
  fun_prop














/-- Almost everywhere strong measurability transfers from `(0,∞)` to `Iz`. -/
lemma aesm_of_continuousOn_Ioi {g : ℝ → ℝ} (h : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable g (volume.restrict Spaces.Iz) := by
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioi 0)) :=
    h.aestronglyMeasurable measurableSet_Ioi
  rw [show Spaces.Iz = Set.Ici 0 from rfl,
    ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact h1


/-- `L₁₂(f)` is differentiable (hence continuous) on `(0,∞)`. -/
lemma hasDerivAt_L12f (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (L12f f) (-(FM.L12dens Spaces.K f z)) z :=
  FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
    hfH.hint (hfH.hcont z hz) hz

/-- `L₁₂(f)` is a.e. strongly measurable on `Iz`. -/
lemma aesm_L12f (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEStronglyMeasurable (fun z => L12f f z) (volume.restrict Spaces.Iz) :=
  aesm_of_continuousOn_Ioi fun z hz => (hasDerivAt_L12f f hfH hz).continuousAt.continuousWithinAt











/-! ## The assembly of the `Z₃` bound -/
















end Z3Clean

end Work.Coercivity
