import Mathlib
import Submission.Work.Whitney.EuclidModel

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **Closeness of the transported scaled model to the axis.**  If `β` is `δ`-close to `inclModel`
in the sup norm and `√n ≤ lam`, then `euclidModel n lam β` is `δ`-close to the axis in the `L²`
norm: the factor `√n` in `norm_lpOfEuclid_le` is absorbed by the scaling. -/
theorem norm_euclidModel_sub_axis_le {n : ℕ} {lam δ : ℝ}
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hlam : 0 < lam) (hsqrt : Real.sqrt n ≤ lam)
    (hβδ : ∀ x, ‖β x - Work.Whitney.inclModel n x‖ ≤ δ) (hδ : 0 ≤ δ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖Work.Whitney.euclidModel n lam β u - (u, 0)‖ ≤ δ := by
  -- Work in the sup-norm world: `x = euclidOfLp u`.
  set x : Fin n → ℝ := euclidOfLp n u with hx
  -- The axis in the `L²` world is the transport of the axis in the sup world.
  have hkey : euclidModel n lam β u - (u, 0)
      = pairToE n (scaledModel n lam β x - inclModel n x) := by
    rw [euclidModel_apply, ← hx]
    have hpair : (u, 0) = pairToE n (inclModel n x) := by
      rw [hx]; simp
    rw [hpair, map_sub]
  -- The scaled model differs from the axis by the scaling of the sup-norm error of `β`.
  have hz : scaledModel n lam β x - inclModel n x
      = (1/lam) • (β (lam • x) - inclModel n (lam • x)) := by
    rw [scaledModel_apply]
    have hincl : inclModel n x = (1/lam) • inclModel n (lam • x) := by
      ext <;> simp [inclModel, smul_smul, inv_mul_cancel₀ (ne_of_gt hlam)]
    rw [hincl, smul_sub]
  -- Therefore its sup norm is at most `δ / lam`.
  have hznorm : ‖scaledModel n lam β x - inclModel n x‖ ≤ (1/lam) * δ := by
    rw [hz, norm_smul]
    have h1 : ‖(1/lam : ℝ)‖ = 1/lam := by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlam)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hβδ (lam • x)) (by positivity)
  rw [hkey]
  -- The `L²` norm is at most `√n` times the sup norm, and `√n ≤ lam` absorbs the factor `1/lam`.
  calc ‖pairToE n (scaledModel n lam β x - inclModel n x)‖
      ≤ Real.sqrt n * ‖scaledModel n lam β x - inclModel n x‖ := norm_pairToE_le n _
    _ ≤ Real.sqrt n * ((1/lam) * δ) :=
        mul_le_mul_of_nonneg_left hznorm (Real.sqrt_nonneg n)
    _ ≤ δ := by
        have hdiv : Real.sqrt n / lam ≤ 1 := by
          rw [div_le_one hlam]; exact hsqrt
        have heq : Real.sqrt n * ((1/lam) * δ) = (Real.sqrt n / lam) * δ := by ring
        rw [heq]
        calc (Real.sqrt n / lam) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hdiv hδ
          _ = δ := one_mul δ

end Work.Whitney
