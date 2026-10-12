import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsW_le_L2_Dir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.Decomp

open MeasureTheory
open scoped Topology

/-- For `h : ℝ³ → ℝ` smooth with compact support, the weighted spectral integrand
`p ↦ [‖p‖ − c]₊² · ‖bsPsi h p‖²` is integrable.  The symbol bound
`fsKinCoeff c r ≤ 2r² + 2c²` (`Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul`) reduces this to the
unweighted and `‖p‖²`-weighted integrability statements `integrable_kinFT_sq` and
`integrable_kinFT_energy_cspt`; `aestronglyMeasurable` comes from continuity of `bsPsi`. -/
theorem integrable_fsKinCoeff_mul_bsPsi_sq {c : ℝ} {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hd : ContDiff ℝ (⊤ : ENat) h) (hc : HasCompactSupport h) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
  -- unweighted integrability of `‖bsPsi h p‖²`
  have hKint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq h hd hc
  -- integrability of the `‖p‖²`-weighted mass
  have hK2int : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt h hd hc
  -- the dominating integrand is a linear combination of the two
  have hGint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    have h1 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        2 * (‖p‖ ^ 2 * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)) := hK2int.const_mul 2
    have h2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (2 * c ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := hKint.const_mul (2 * c ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    ring
  -- the weighted integrand is a.e. strongly measurable: continuous symbol times `L¹` mass
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖) :=
    ((continuous_norm.sub continuous_const).max continuous_const).pow 2
  have haesm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) :=
    hcont.aestronglyMeasurable.mul hKint.aestronglyMeasurable
  -- the pointwise symbol bound `[r − c]₊² ≤ 2r² + 2c²` dominates the integrand
  refine hGint.mono' haesm (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c ‖p‖)
    (sq_nonneg _)

end Work.BSKinetic.Decomp
