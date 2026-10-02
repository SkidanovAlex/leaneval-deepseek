import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Repelling

open Work.FatouCoord.Petal

/-- The left half-plane `{w : ℂ | w.re < -T}` is convex (it is the preimage of an open
half-line under the real-linear map `w ↦ w.re`). -/
lemma convex_LeftHalfPlane (T : ℝ) : Convex ℝ (LeftHalfPlane T) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_LeftHalfPlane] at hx hy ⊢
  rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1, zero_mul, one_mul]
    simpa using hy
  · have h1 : a * x.re < a * (-T) := mul_lt_mul_of_pos_left hx hapos
    have h2 : b * y.re ≤ b * (-T) := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have h3 : a * (-T) + b * (-T) = -T := by rw [← add_mul, hab, one_mul]
    linarith

/-- The derivative of `w ↦ log (-w)` at a point `z` of the open right half-plane
`{z | 0 < (-z).re}` is `1 / z`. -/
lemma hasDerivAt_log_neg {z : ℂ} (hz : 0 < (-z).re) :
    HasDerivAt (fun w : ℂ => Complex.log (-w)) z⁻¹ z := by
  have hz' : -z ∈ Complex.slitPlane := Or.inl hz
  have h1 : HasDerivAt (fun w : ℂ => -w) (-1) z := hasDerivAt_neg z
  have h2 : HasDerivAt (fun w : ℂ => Complex.log (-w)) ((-1) / (-z)) z := h1.clog hz'
  convert h2 using 1
  rw [div_eq_mul_inv, inv_neg]
  ring

lemma deriv_log_neg {z : ℂ} (hz : 0 < (-z).re) :
    deriv (fun w : ℂ => Complex.log (-w)) z = z⁻¹ :=
  (hasDerivAt_log_neg hz).deriv

theorem norm_Lambda_sub_le {x y : ℂ} {T : ℝ} (hT : 0 < T) (hx : Work.FatouCoord.Petal.LeftHalfPlane T x) (hy : Work.FatouCoord.Petal.LeftHalfPlane T y) : ‖Work.FatouCoord.Petal.Lambda x - Work.FatouCoord.Petal.Lambda y‖ ≤ ‖x - y‖ / T := by
  -- every point of the segment `[x, y]` lies in the left half-plane
  have hseg : ∀ z ∈ segment ℝ x y, z.re < -T :=
    fun z hz => (convex_LeftHalfPlane T).segment_subset hx hy hz
  -- `w ↦ log (-w)` is complex-differentiable on the segment
  have hdiff : ∀ z ∈ segment ℝ x y,
      DifferentiableAt ℂ (fun w : ℂ => Complex.log (-w)) z := by
    intro z hz
    exact (hasDerivAt_log_neg (by rw [Complex.neg_re]; linarith [hseg z hz])).differentiableAt
  -- and its derivative is bounded by `1 / T` there
  have hbnd : ∀ z ∈ segment ℝ x y,
      ‖deriv (fun w : ℂ => Complex.log (-w)) z‖ ≤ 1 / T := by
    intro z hz
    have hzpos : 0 < (-z).re := by rw [Complex.neg_re]; linarith [hseg z hz]
    have hzT : T ≤ ‖z‖ := by
      have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h2 : |z.re| = -z.re := abs_of_neg (by linarith [hseg z hz])
      linarith [hseg z hz]
    rw [deriv_log_neg hzpos, norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hT hzT
  -- mean value inequality on the segment
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (f := fun w : ℂ => Complex.log (-w)) (s := segment ℝ x y) (x := x) (y := y)
    (C := 1 / T) hdiff hbnd (convex_segment x y) (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)
  have hL : Lambda x - Lambda y = Complex.log (-x) - Complex.log (-y) := by
    simp only [Lambda]; ring
  calc ‖Lambda x - Lambda y‖
      = ‖Complex.log (-x) - Complex.log (-y)‖ := by rw [hL]
    _ = ‖Complex.log (-y) - Complex.log (-x)‖ := norm_sub_rev _ _
    _ ≤ (1 / T) * ‖y - x‖ := hmvt
    _ = ‖x - y‖ / T := by rw [norm_sub_rev y x, div_eq_mul_inv]; ring

end Work.FatouCoord.Repelling
