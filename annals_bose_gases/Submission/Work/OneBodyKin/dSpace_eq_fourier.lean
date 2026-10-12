import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open scoped ContDiff Topology Real

set_option autoImplicit false

/-- `dSpace` as a single integral of the pointwise (squared) gradient.  The finite sum over the
coordinate directions is exchanged with the integral; each directional derivative is continuous
with compact support, hence integrable. -/
private lemma dSpace_eq_integral_sum (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.dSpace ψ
      = ∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  rw [Work.BSKinetic.dSpace]
  refine (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
    (f := fun k (x : ℝ³) => (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2) ?_).symm
  intro k _
  have hD_cd : ContDiff ℝ (⊤ : ENat)
      (fun y : ℝ³ => fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hD_cs : HasCompactSupport (fun y : ℝ³ => fderiv ℝ ψ y (Submission.BoseGases.kcStdBasis k)) :=
    hcs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis k)
  exact Continuous.integrable_of_hasCompactSupport (hD_cd.continuous.pow 2)
    (hD_cs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))

/-- The one-body Dirichlet word is the `p`-space kinetic integral: `Σ_k ∫ (∂_kψ)²` equals
`(2π)⁻³ ∫‖q‖²‖kinFT ψ q‖²dq`. -/
theorem dSpace_eq_fourier (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.dSpace ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  have hsum : Work.BSKinetic.dSpace ψ
      = ∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    dSpace_eq_integral_sum ψ hψ hcs
  have hwin : Submission.BoseGases.winModeForm (fun _ : ℝ³ => 1) (fun r => r ^ 2) ψ
      = ∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    simpa using
      (Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet (fun _ : ℝ³ => 1) ψ
        contDiff_const hψ hcs)
  rw [hsum, ← hwin]
  unfold Submission.BoseGases.winModeForm
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
  simp [Complex.ofReal_one]

end Work.OneBodyKin
