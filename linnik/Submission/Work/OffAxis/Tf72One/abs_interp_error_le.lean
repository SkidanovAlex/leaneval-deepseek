import Mathlib

open Set Filter Topology

namespace Work.OffAxis.Tf72One

/-- **Sharp two-point interpolation error bound.** For a `C²` function `f` on `[a,b]` and `M` bounding
`|f''|` on the open interval, the linear interpolant at the endpoints differs from `f` by at most
`(b-a)²/8 · M`.  The constant `1/8` is sharp (`f x = x²` on `[-1,1]`). -/
theorem abs_interp_error_le (f : ℝ → ℝ) (a b x M : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b))
    (hM : ∀ y ∈ Set.Ioo a b, |iteratedDeriv 2 f y| ≤ M) :
    |f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)| ≤ (b - a) ^ 2 / 8 * M := by
  -- `M` is nonnegative, since the open interval is nonempty by `hab`.
  have hM0 : 0 ≤ M :=
    (abs_nonneg (iteratedDeriv 2 f ((a + b) / 2))).trans (hM _ ⟨by linarith, by linarith⟩)
  -- Convexity of `t ↦ f t + M/2 * t²` (its second derivative is `f'' + M ≥ 0`).
  have hconv : ConvexOn ℝ (Set.Icc a b) (fun t => f t + M / 2 * t ^ 2) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc a b)
      (f := fun t => f t + M / 2 * t ^ 2) (f' := fun t => deriv f t + M * t)
      (f'' := fun t => iteratedDeriv 2 f t + M) (convex_Icc a b) ?_ ?_ ?_ ?_
    · exact hf.continuousOn.add (by fun_prop)
    · intro y hy
      rw [interior_Icc] at hy
      rw [interior_Icc]
      have hmem : Set.Icc a b ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
      have h1 : HasDerivAt f (deriv f y) y :=
        ((hf.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => M / 2 * t ^ 2) (M * y) y := by
        have h := (hasDerivAt_pow 2 y).const_mul (M / 2)
        simp only [Nat.reduceSub, pow_one] at h
        exact h.congr_deriv (by ring)
      exact (h1.add h2).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [interior_Icc]
      have hmem : Set.Icc a b ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
      have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
        have hcd : ContDiffAt ℝ 1 (deriv f) y :=
          (hf.contDiffAt hmem).derivWithin (m := 1) (by norm_num)
        have hd : DifferentiableAt ℝ (deriv f) y := hcd.differentiableAt (by norm_num)
        simpa [iteratedDeriv_eq_iterate] using hd.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => M * t) M y := by
        simpa using (hasDerivAt_id y).const_mul M
      exact (h1.add h2).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      linarith [(abs_le.mp (hM y hy)).1]
  -- Concavity of `t ↦ f t - M/2 * t²` (its second derivative is `f'' - M ≤ 0`).
  have hconc : ConcaveOn ℝ (Set.Icc a b) (fun t => f t - M / 2 * t ^ 2) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc a b)
      (f := fun t => f t - M / 2 * t ^ 2) (f' := fun t => deriv f t - M * t)
      (f'' := fun t => iteratedDeriv 2 f t - M) (convex_Icc a b) ?_ ?_ ?_ ?_
    · exact hf.continuousOn.sub (by fun_prop)
    · intro y hy
      rw [interior_Icc] at hy
      rw [interior_Icc]
      have hmem : Set.Icc a b ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
      have h1 : HasDerivAt f (deriv f y) y :=
        ((hf.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => M / 2 * t ^ 2) (M * y) y := by
        have h := (hasDerivAt_pow 2 y).const_mul (M / 2)
        simp only [Nat.reduceSub, pow_one] at h
        exact h.congr_deriv (by ring)
      exact (h1.sub h2).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [interior_Icc]
      have hmem : Set.Icc a b ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
      have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
        have hcd : ContDiffAt ℝ 1 (deriv f) y :=
          (hf.contDiffAt hmem).derivWithin (m := 1) (by norm_num)
        have hd : DifferentiableAt ℝ (deriv f) y := hcd.differentiableAt (by norm_num)
        simpa [iteratedDeriv_eq_iterate] using hd.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => M * t) M y := by
        simpa using (hasDerivAt_id y).const_mul M
      exact (h1.sub h2).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      linarith [(abs_le.mp (hM y hy)).2]
  -- Elementary algebra of the chord weights.
  have hba : 0 < b - a := by linarith
  have h1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith [hx.2]) hba.le
  have h2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
  have hcombo : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by field_simp; ring
  have hQ : (b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2 - x ^ 2
      = (x - a) * (b - x) := by field_simp; ring
  have hbd : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x - a - b)]
  -- Upper bound from convexity.
  have hupper : f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
      ≤ (b - a) ^ 2 / 8 * M := by
    have h3 := hconv.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) h1 h2 hsum
    simp only [smul_eq_mul] at h3
    rw [hcombo] at h3
    have hrew : (b - x) / (b - a) * (f a + M / 2 * a ^ 2)
          + (x - a) / (b - a) * (f b + M / 2 * b ^ 2)
        = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
          + M / 2 * ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2) := by ring
    rw [hrew] at h3
    calc f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
        ≤ M / 2 * ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2) - M / 2 * x ^ 2 := by
          linarith
      _ = M / 2 * ((x - a) * (b - x)) := by rw [← hQ]; ring
      _ ≤ M / 2 * ((b - a) ^ 2 / 4) := mul_le_mul_of_nonneg_left hbd (by linarith)
      _ = (b - a) ^ 2 / 8 * M := by ring
  -- Lower bound from concavity.
  have hlower : -((b - a) ^ 2 / 8 * M)
      ≤ f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b) := by
    have h3 := hconc.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) h1 h2 hsum
    simp only [smul_eq_mul] at h3
    rw [hcombo] at h3
    have hrew : (b - x) / (b - a) * (f a - M / 2 * a ^ 2)
          + (x - a) / (b - a) * (f b - M / 2 * b ^ 2)
        = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
          - M / 2 * ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2) := by ring
    rw [hrew] at h3
    have h4 : -M / 2 * ((b - a) ^ 2 / 4) ≤ -M / 2 * ((x - a) * (b - x)) := by
      have hh := mul_le_mul_of_nonneg_left hbd (by linarith : (0 : ℝ) ≤ M / 2)
      linarith
    calc -((b - a) ^ 2 / 8 * M) = -M / 2 * ((b - a) ^ 2 / 4) := by ring
      _ ≤ -M / 2 * ((x - a) * (b - x)) := h4
      _ = M / 2 * (x ^ 2 - ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2)) := by
          rw [← hQ]; ring
      _ ≤ f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b) := by linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

end Work.OffAxis.Tf72One
