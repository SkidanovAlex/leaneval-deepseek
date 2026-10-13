/-
# `Work.FTS.Regularity.smulEThetaHolder`

The quantitative Hölder estimate for a scalar amplitude times the azimuthal frame vector, in the
`HolderWith`-with-explicit-constant form used by the per-slice transfer of the regularity chapter.

If `A : ℝ³ → ℝ` is `α`-Hölder with constant `CA` (`0 < α ≤ 1`) and vanishes at least like
`radial^α` (`|A x| ≤ Ca · r(x)^α`, `Ca ≥ 0`), then `x ↦ A x • e_θ(x)` is `α`-Hölder with the
explicit constant `|CA + 2 Ca|` (`Work.FTS.Regularity.smulEThetaConst`).

The mechanism is the one of `Work.ConstructionInstance.holder_smul_eTheta`, but with the constant
kept explicit (`HolderWith` rather than the existential `Holder`), which is what makes the estimate
uniform in the fake-time parameter.  Writing

  `A x • e_θ x - A y • e_θ y = (A x - A y) • e_θ x + A y • (e_θ x - e_θ y)`

the first summand is controlled by the Hölder regularity of `A` and `‖e_θ‖ ≤ 1`, while the second
is controlled by

  `|A y| · ‖e_θ x - e_θ y‖ ≤ Ca · r(y)^α · 2 dist x y / r(y) ≤ 2 Ca · dist x y ^ α`,

which is the geometric input `Work.Cyl.eTheta_sub_norm_mul_le` combined with the elementary
inequality `Work.Stability.mul_rpow_le`: although `e_θ` is *discontinuous* on the axis
(`eTheta = 0` there, a jump of length `1`), the vanishing of `A` kills it.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.Cyl.eTheta_sub_norm_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open scoped NNReal

namespace Work.FTS.Regularity

/-- The azimuthal frame vector is a unit vector off the axis and `0` on it, so its norm is at
most `1`. -/
private theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  by_cases h : Work.Cyl.radial x = 0
  · simp [Work.Cyl.eTheta, h]
  · rw [Work.Cyl.norm_eTheta x h]

theorem smulEThetaHolder {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {A : Work.FTS.Regularity.R3 → ℝ} {CA Ca : ℝ} (hCA : 0 ≤ CA) (hCa : 0 ≤ Ca)
    (hA : HolderWith ⟨CA, hCA⟩ (⟨α, hα.le⟩ : NNReal) A)
    (hvanA : ∀ x : Work.FTS.Regularity.R3, |A x| ≤ Ca * (Work.Cyl.radial x) ^ α) :
    HolderWith (Work.FTS.Regularity.smulEThetaConst CA Ca) (⟨α, hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 => A x • Work.Cyl.eTheta x) := by
  -- the Hölder bound of `A`, as a `dist` estimate with the explicit constant `CA`
  have hcay : ∀ x y : R3, dist (A x) (A y) ≤ CA * dist x y ^ α := by
    intro x y
    exact hA.dist_le x y
  -- the weighted geometric bound `r(y)^α ‖e_θ x - e_θ y‖ ≤ 2 dist x y ^ α`
  have hw : ∀ x y : R3,
      Work.Cyl.radial y ^ α * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ 2 * dist x y ^ α := by
    intro x y
    rw [mul_comm]
    refine Work.Stability.mul_rpow_le (p := ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖)
      (ρ := Work.Cyl.radial y) (d := dist x y) (α := α) hα hα1
      (Work.Cyl.radial_nonneg y) dist_nonneg (norm_nonneg _)
      (Work.Cyl.eTheta_sub_norm_mul_le x y) ?_
    calc ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ ‖Work.Cyl.eTheta x‖ + ‖Work.Cyl.eTheta y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith [norm_eTheta_le_one x, norm_eTheta_le_one y]
      _ = 2 := by norm_num
  refine Work.Stability.holderWith_of_dist_le (C := smulEThetaConst CA Ca)
    (r := ⟨α, hα.le⟩) (f := fun x : R3 => A x • Work.Cyl.eTheta x) ?_
  intro x y
  rw [dist_eq_norm]
  have hsplit : A x • Work.Cyl.eTheta x - A y • Work.Cyl.eTheta y
      = (A x - A y) • Work.Cyl.eTheta x
        + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y) := by
    rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  have hcore :
      ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ (CA + 2 * Ca) * dist x y ^ α := by
    calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
        ≤ ‖(A x - A y) • Work.Cyl.eTheta x‖
          + ‖A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖ := norm_add_le _ _
      _ = |A x - A y| * ‖Work.Cyl.eTheta x‖
          + |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (CA) * dist x y ^ α
          + Ca * (Work.Cyl.radial y ^ α
              * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by
          apply add_le_add
          · calc |A x - A y| * ‖Work.Cyl.eTheta x‖ ≤ |A x - A y| * 1 :=
                mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
              _ = |A x - A y| := mul_one _
              _ = dist (A x) (A y) := by rw [Real.dist_eq]
              _ ≤ CA * dist x y ^ α := hcay x y
          · calc |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
                ≤ (Ca * Work.Cyl.radial y ^ α)
                    * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ :=
                  mul_le_mul_of_nonneg_right (hvanA y) (norm_nonneg _)
              _ = Ca * (Work.Cyl.radial y ^ α
                    * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by ring
      _ ≤ CA * dist x y ^ α + Ca * (2 * dist x y ^ α) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hw x y) hCa)
      _ = (CA + 2 * Ca) * dist x y ^ α := by ring
  calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
      ≤ (CA + 2 * Ca) * dist x y ^ α := hcore
    _ ≤ ((smulEThetaConst CA Ca : NNReal) : ℝ)
          * dist x y ^ (((⟨α, hα.le⟩ : NNReal)) : ℝ) := by
        simp only [smulEThetaConst]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg dist_nonneg α)

end Work.FTS.Regularity
