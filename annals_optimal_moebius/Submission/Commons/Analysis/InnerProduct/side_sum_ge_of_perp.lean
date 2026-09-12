import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace Commons.Analysis.InnerProduct

/-- Helper: if `x ⊥ n` then `‖x + n‖ = ‖x - n‖`. -/
theorem norm_add_eq_norm_sub_of_inner_eq_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x n : V) (h : ⟪x, n⟫_ℝ = 0) : ‖x + n‖ = ‖x - n‖ := by
  apply (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real (x := x) (y := n) h,
    norm_sub_sq_eq_norm_sq_add_norm_sq_real (x := x) (y := n) h]

/-- **Geometric Lemma A1 (reflection form)**: if `n ⊥ u` then for every real
`c` the sum of the two distances from the apex `w = c • u + n` to the base
endpoints `−(1/2) • u` and `(1/2) • u` is at least `√(‖u‖² + 4‖n‖²)`.

This is the coordinate-free form of Lemma A1 of Schwartz, "The optimal paper
Moebius band": a triangle with base `‖u‖` and height `‖n‖` has its two
non-base sides summing to at least `√(‖u‖² + 4‖n‖²)`.  Proof: reflect the
base endpoint `(1/2) • u` in the line through the apex parallel to the base
(it is `p₂' = (1/2) • u + 2 • n`, and `‖w − p₂'‖ = ‖w − p₂‖` because
`n ⊥ u`), then apply the triangle inequality to `p₁`, `w`, `p₂'`, using
`‖p₁ − p₂'‖ = ‖u + 2n‖ = √(‖u‖² + 4‖n‖²)` (again `n ⊥ u`). -/
theorem side_sum_ge_of_perp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u n : V) (c : ℝ) (hn : inner ℝ n u = 0) :
    Real.sqrt (‖u‖ ^ 2 + 4 * ‖n‖ ^ 2) ≤
      ‖(c • u + n) + (1 / 2 : ℝ) • u‖ + ‖(c • u + n) - (1 / 2 : ℝ) • u‖ := by
  have hnu : ⟪u, n⟫_ℝ = 0 := by
    rw [← real_inner_comm u n]; exact hn
  -- Pythagoras for `u + 2 n`
  have hsq : ‖u + (2 : ℝ) • n‖ ^ 2 = ‖u‖ ^ 2 + 4 * ‖n‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hnu, mul_zero, norm_smul, Real.norm_ofNat]
    ring
  have hsqrt : Real.sqrt (‖u‖ ^ 2 + 4 * ‖n‖ ^ 2) = ‖u + (2 : ℝ) • n‖ := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  -- `p₁ - p₂' = -(u + 2n)`
  have hp12 : ‖-(1 / 2 : ℝ) • u - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖ = ‖u + (2 : ℝ) • n‖ := by
    have key : -(1 / 2 : ℝ) • u - ((1 / 2 : ℝ) • u + (2 : ℝ) • n) = -(u + (2 : ℝ) • n) := by module
    rw [key, norm_neg]
  -- triangle inequality through the apex `w = c • u + n`
  have htri : ‖-(1 / 2 : ℝ) • u - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖
      ≤ ‖-(1 / 2 : ℝ) • u - (c • u + n)‖
        + ‖(c • u + n) - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖ := by
    have key : -(1 / 2 : ℝ) • u - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)
        = (-(1 / 2 : ℝ) • u - (c • u + n))
          + ((c • u + n) - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)) := by abel
    rw [key]
    exact norm_add_le _ _
  -- the reflected distance equals the original one
  have hp1w : ‖-(1 / 2 : ℝ) • u - (c • u + n)‖
      = ‖(c • u + n) + (1 / 2 : ℝ) • u‖ := by
    rw [norm_sub_rev]
    congr 1
    module
  have hp2w : ‖(c • u + n) - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖
      = ‖(c • u + n) - (1 / 2 : ℝ) • u‖ := by
    have hx : ⟪(c - 1 / 2 : ℝ) • u, n⟫_ℝ = 0 := by
      rw [real_inner_smul_left, hnu, mul_zero]
    have h1 : (c • u + n) - ((1 / 2 : ℝ) • u + (2 : ℝ) • n) = (c - 1 / 2 : ℝ) • u - n := by
      module
    have h2 : (c • u + n) - (1 / 2 : ℝ) • u = (c - 1 / 2 : ℝ) • u + n := by
      module
    rw [h1, h2]
    exact (norm_add_eq_norm_sub_of_inner_eq_zero _ _ hx).symm
  calc Real.sqrt (‖u‖ ^ 2 + 4 * ‖n‖ ^ 2)
      = ‖u + (2 : ℝ) • n‖ := hsqrt
    _ = ‖-(1 / 2 : ℝ) • u - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖ := hp12.symm
    _ ≤ ‖-(1 / 2 : ℝ) • u - (c • u + n)‖
          + ‖(c • u + n) - ((1 / 2 : ℝ) • u + (2 : ℝ) • n)‖ := htri
    _ = ‖(c • u + n) + (1 / 2 : ℝ) • u‖ + ‖(c • u + n) - (1 / 2 : ℝ) • u‖ := by
        rw [hp1w, hp2w]

end Commons.Analysis.InnerProduct