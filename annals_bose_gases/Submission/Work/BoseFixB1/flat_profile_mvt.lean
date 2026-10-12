import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **Mean value bound along a segment, with a flat majorant.**  Let `f : ℝ³ → F` be
differentiable, let `x, y : ℝ³` and let `C ≥ 0`, `k : ℕ`.  Assume the Fréchet derivative is
bounded by the flat profile `C (2 - ‖z‖)^k` on the closed ball of radius `2`, and assume that
every point `x + t • (y - x)`, `t ∈ [0,1]`, of the segment has norm between `‖x‖` and `2`.
Then `‖f y - f x‖ ≤ C (2 - ‖x‖)^k ‖y - x‖`.

Proof sketch: apply `Convex.norm_image_sub_le_of_norm_fderiv_le` with `s = segment ℝ x y`
(convex, contains both endpoints) and the derivative bound `C (2 - ‖x‖)^k` on all of `s`; for
`w ∈ s` write `w = x + t • (y - x)` with `t ∈ Icc 0 1`, so `‖x‖ ≤ ‖w‖ ≤ 2` and hence
`C (2 - ‖w‖)^k ≤ C (2 - ‖x‖)^k` (monotonicity of `z ↦ z^k` on `[0,∞)`). -/
theorem flat_profile_mvt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) {f : EuclideanSpace ℝ (Fin 3) → F} {x y : EuclideanSpace ℝ (Fin 3)} {C : ℝ}
    (hdiff : Differentiable ℝ f) (hC : 0 ≤ C) (hx : ‖x‖ ≤ 2)
    (hIH : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 2 → ‖fderiv ℝ f z‖ ≤ C * (2 - ‖z‖) ^ k)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x + t • (y - x)‖ ∧ ‖x + t • (y - x)‖ ≤ 2) :
    ‖f y - f x‖ ≤ C * (2 - ‖x‖) ^ k * ‖y - x‖ := by
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := segment ℝ x y)
    (C := C * (2 - ‖x‖) ^ k) ?_ ?_ (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  · intro w _
    exact hdiff w
  · intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨hge, hle2⟩ := hseg t ht
    have hmono : (2 - ‖x + t • (y - x)‖) ^ k ≤ (2 - ‖x‖) ^ k :=
      pow_le_pow_left₀ (sub_nonneg.mpr hle2) (sub_le_sub_left hge 2) k
    exact le_trans (hIH (x + t • (y - x)) hle2) (mul_le_mul_of_nonneg_left hmono hC)

end Work.BoseFixB1
