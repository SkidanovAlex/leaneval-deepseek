import Mathlib

namespace Work.Fatou.Analysis

/-- Auxiliary: points of the segment `[z, z + a]` are at distance at most `‖a‖` from `z`. -/
private lemma norm_sub_le_of_mem_segment {z a w : ℂ} (hw : w ∈ segment ℝ z (z + a)) :
    ‖w - z‖ ≤ ‖a‖ := by
  rw [segment_eq_image'] at hw
  rcases hw with ⟨θ, hθ, rfl⟩
  have hsub : z + θ • (z + a - z) - z = θ • a := by
    rw [add_sub_cancel_left, add_sub_cancel_left]
  rw [hsub, norm_smul, Real.norm_of_nonneg hθ.1]
  calc θ * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg a)
    _ = ‖a‖ := one_mul _

/-- Second-order Taylor estimate for a complex analytic function on a segment:
if `‖(deriv (deriv f))‖ ≤ M` on the segment `[z, z + a]`, then
`‖f (z + a) - f z - a * deriv f z‖ ≤ M * ‖a‖ ^ 2`. -/
theorem norm_sub_sub_mul_deriv_le {f : ℂ → ℂ} {z a : ℂ} {M : ℝ}
    (hd : ∀ w ∈ segment ℝ z (z + a), AnalyticAt ℂ f w)
    (hb : ∀ w ∈ segment ℝ z (z + a), ‖deriv (deriv f) w‖ ≤ M) :
    ‖f (z + a) - f z - a * deriv f z‖ ≤ M * ‖a‖ ^ 2 := by
  have hseg : Convex ℝ (segment ℝ z (z + a)) := convex_segment z (z + a)
  have hz : z ∈ segment ℝ z (z + a) := left_mem_segment ℝ z (z + a)
  have hza : z + a ∈ segment ℝ z (z + a) := right_mem_segment ℝ z (z + a)
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb z hz)
  -- First-order estimate for `deriv f` on the segment (mean value inequality).
  have h1 : ∀ w ∈ segment ℝ z (z + a), ‖deriv f w - deriv f z‖ ≤ M * ‖w - z‖ := by
    intro w hw
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (f := deriv f) (s := segment ℝ z (z + a)) (x := z) (y := w) (C := M)
      (fun x hx => (hd x hx).deriv.differentiableAt) (fun x hx => hb x hx) hseg hz hw
  set G : ℂ → ℂ := fun w => f w - w * deriv f z with hGdef
  have hGdiff : ∀ w ∈ segment ℝ z (z + a), DifferentiableAt ℂ G w := by
    intro w hw
    rw [hGdef]
    exact (hd w hw).differentiableAt.sub (differentiableAt_id.mul_const _)
  -- The derivative of `G` is `deriv f · - deriv f z`.
  have hGderiv : ∀ w ∈ segment ℝ z (z + a), deriv G w = deriv f w - deriv f z := by
    intro w hw
    rw [hGdef]
    have h2 : DifferentiableAt ℂ (fun y : ℂ => y * deriv f z) w :=
      differentiableAt_id.mul_const _
    change deriv (f - fun y : ℂ => y * deriv f z) w = deriv f w - deriv f z
    rw [deriv_sub (hd w hw).differentiableAt h2, deriv_mul_const differentiableAt_id]
    simp
  -- Bound on `‖deriv G‖` on the segment.
  have h2 : ∀ w ∈ segment ℝ z (z + a), ‖deriv G w‖ ≤ M * ‖a‖ := by
    intro w hw
    rw [hGderiv w hw]
    calc ‖deriv f w - deriv f z‖ ≤ M * ‖w - z‖ := h1 w hw
      _ ≤ M * ‖a‖ :=
        mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) hM
  have hmain : ‖G (z + a) - G z‖ ≤ M * ‖a‖ ^ 2 := by
    have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := G) (s := segment ℝ z (z + a)) (x := z) (y := z + a) (C := M * ‖a‖)
      hGdiff h2 hseg hz hza
    calc ‖G (z + a) - G z‖ ≤ (M * ‖a‖) * ‖(z + a) - z‖ := hbound
      _ = M * ‖a‖ ^ 2 := by rw [add_sub_cancel_left]; ring
  have hGeq : G (z + a) - G z = f (z + a) - f z - a * deriv f z := by
    rw [hGdef]; ring
  rw [hGeq] at hmain
  exact hmain

end Work.Fatou.Analysis
