/-
# `Work.ConstructionInstance.holder_smul_eTheta`

The basic Hölder estimate for a scalar profile times the angular frame vector:

if `A : ℝ³ → ℝ` is `α`-Hölder (`0 < α ≤ 1`) and vanishes at least like `radial^α`
(`|A x| ≤ Ca · r(x)^α`), then `x ↦ A x • e_θ(x)` is `α`-Hölder.

The point is that, although `e_θ` itself is *discontinuous* on the axis `r = 0` (it jumps from
`0` to a unit vector), the vanishing of `A` there kills the jump: writing

  `A x • e_θ x - A y • e_θ y = (A x - A y) • e_θ x + A y • (e_θ x - e_θ y)`

the first summand is controlled by the Hölder regularity of `A` and `‖e_θ‖ ≤ 1`, while the
second is controlled by

  `|A y| · ‖e_θ x - e_θ y‖ ≤ Ca · r(y)^α · 2 dist x y / r(y) ≤ 2 Ca · dist x y ^ α`,

which is the content of the geometric input `Work.Cyl.eTheta_sub_norm_mul_le` combined with the
elementary inequality `Work.Stability.mul_rpow_le`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.Cyl.eTheta_sub_norm_mul_le
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem holder_smul_eTheta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {A : Work.ConstructionInstance.R3 → ℝ} {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hA : Holder ⟨α, hα.le⟩ A)
    (hvanA : ∀ x : Work.ConstructionInstance.R3, |A x| ≤ Ca * (Work.Cyl.radial x) ^ α) :
    Holder ⟨α, hα.le⟩
      (fun x : Work.ConstructionInstance.R3 => A x • Work.Cyl.eTheta x) := by
  obtain ⟨CA, hCA⟩ := hA
  -- the Hölder bound of `A`, as a `dist` estimate
  have hcay : ∀ x y : Work.ConstructionInstance.R3,
      dist (A x) (A y) ≤ (CA : ℝ) * dist x y ^ α := by
    intro x y; exact hCA.dist_le x y
  -- the weighted geometric bound `r(y)^α ‖e_θ x - e_θ y‖ ≤ 2 dist x y ^ α`
  have hw : ∀ x y : Work.ConstructionInstance.R3,
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
  refine ⟨⟨(CA : ℝ) + 2 * Ca, add_nonneg CA.coe_nonneg (by linarith)⟩, ?_⟩
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [dist_eq_norm]
  have hsplit : A x • Work.Cyl.eTheta x - A y • Work.Cyl.eTheta y
      = (A x - A y) • Work.Cyl.eTheta x
        + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y) := by
    rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
      ≤ ‖(A x - A y) • Work.Cyl.eTheta x‖
        + ‖A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖ := norm_add_le _ _
    _ = |A x - A y| * ‖Work.Cyl.eTheta x‖
        + |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (CA : ℝ) * dist x y ^ α
        + Ca * (Work.Cyl.radial y ^ α
            * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by
        apply add_le_add
        · calc |A x - A y| * ‖Work.Cyl.eTheta x‖ ≤ |A x - A y| * 1 :=
              mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
            _ = |A x - A y| := mul_one _
            _ = dist (A x) (A y) := by rw [Real.dist_eq]
            _ ≤ (CA : ℝ) * dist x y ^ α := hcay x y
        · calc |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
              ≤ (Ca * Work.Cyl.radial y ^ α)
                  * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ :=
                mul_le_mul_of_nonneg_right (hvanA y) (norm_nonneg _)
            _ = Ca * (Work.Cyl.radial y ^ α
                  * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by ring
    _ ≤ (CA : ℝ) * dist x y ^ α + Ca * (2 * dist x y ^ α) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hw x y) hCa)
    _ = ((CA : ℝ) + 2 * Ca) * dist x y ^ α := by ring

end Work.ConstructionInstance
