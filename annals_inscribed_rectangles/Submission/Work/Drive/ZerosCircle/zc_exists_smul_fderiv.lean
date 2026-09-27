import Mathlib
import Submission.Work.Drive.ZerosCircle.Defs

/-!
# The gradient of `w ↦ ‖w‖ ^ 2` spans the dual of the plane orthogonal to `z`

If `(z, v)` is an orthonormal pair in `EuclideanSpace ℝ (Fin 2)` and `f` is a continuous linear
functional with `f v = 0`, then `f` is a multiple of the derivative of `w ↦ ‖w‖ ^ 2` at `z`
(which is `2 • innerSL ℝ z`, i.e. `w ↦ 2 ⟪z, w⟫_ℝ`).

Indeed `zc_expand` writes every `w` as `⟪z, w⟫_ℝ • z + ⟪v, w⟫_ℝ • v`, so
`f w = ⟪z, w⟫_ℝ * f z = (f z / 2) • (2 • innerSL ℝ z) w`.
-/

namespace Work.Drive.ZerosCircle

open scoped InnerProductSpace

theorem zc_exists_smul_fderiv {f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ}
    {z v : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1) (hv : ‖v‖ = 1) (hzv : inner ℝ z v = 0)
    (hf : f v = 0) :
    ∃ c : ℝ, f = c • fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) z := by
  -- Pointwise form of the claim used below.
  have hmain : ∀ w : EuclideanSpace ℝ (Fin 2), f w = (f z / 2) * (2 * inner ℝ z w) := by
    intro w
    conv_lhs => rw [Work.Drive.zc_expand z v w hz hv hzv]
    rw [map_add, map_smul, map_smul, hf, smul_zero, add_zero, smul_eq_mul]
    ring
  refine ⟨f z / 2, ?_⟩
  rw [fderiv_norm_sq_apply]
  ext w
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  exact hmain w

end Work.Drive.ZerosCircle
