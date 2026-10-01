import Mathlib

namespace Work.A7

open Set

/-!
# Antitonicity of `(1 - e^{-ct})/t`

The function `t ↦ (1 - e^{-ct})/t` is the Laplace transform of the constant `1` on
`[0, c]`; it is antitone on `(0, ∞)` (its derivative is
`((ct + 1) e^{-ct} - 1)/t² ≤ 0`).  Composing with the affine map `t ↦ (3/10) t`
gives the monotonicity of the factor `((1 - e^{-(3/10)t})/t)²` in the target bound.
-/

/-- The elementary inequality `(x + 1) e^{-x} ≤ 1`, for all real `x`, from `1 + x ≤ e^x`. -/
private lemma one_sub_mul_exp_neg_nonneg (x : ℝ) : 0 ≤ 1 - (x + 1) * Real.exp (-x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : (x + 1) * Real.exp (-x) ≤ 1 := by
    have h3 : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-x)).le
    have h4 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    linarith
  linarith

/-- Derivative of `t ↦ (1 - e^{-ct})/t` away from `0`. -/
private lemma hasDerivAt_scaledF (c x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => (1 - Real.exp (-(c * t))) / t)
      (((c * x + 1) * Real.exp (-(c * x)) - 1) / x ^ 2) x := by
  have hinner : HasDerivAt (fun t : ℝ => -(c * t)) (-c) x := by
    have h := hasDerivAt_const_mul (x := x) (-c)
    simpa only [neg_mul] using h
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(c * t))) (Real.exp (-(c * x)) * (-c)) x :=
    HasDerivAt.exp hinner
  have hnum : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(c * t))) (c * Real.exp (-(c * x))) x := by
    have h := hexp.const_sub (1 : ℝ)
    have heq : -(Real.exp (-(c * x)) * (-c)) = c * Real.exp (-(c * x)) := by ring
    rw [heq] at h
    exact h
  have hden : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have h := hnum.div hden hx
  have heq : (c * Real.exp (-(c * x)) * x - (1 - Real.exp (-(c * x))) * 1) / x ^ 2
      = ((c * x + 1) * Real.exp (-(c * x)) - 1) / x ^ 2 := by ring
  rw [heq] at h
  exact h

/-- `t ↦ (1 - e^{-ct})/t` is antitone on `(0, ∞)` for every real `c`. -/
private lemma scaledF_antitone (c : ℝ) :
    AntitoneOn (fun t : ℝ => (1 - Real.exp (-(c * t))) / t) (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f := fun t : ℝ => (1 - Real.exp (-(c * t))) / t)
    (f' := fun x => ((c * x + 1) * Real.exp (-(c * x)) - 1) / x ^ 2) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_scaledF c x (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_scaledF c x (ne_of_gt hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hnum : (c * x + 1) * Real.exp (-(c * x)) - 1 ≤ 0 := by
      have := one_sub_mul_exp_neg_nonneg (c * x)
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (pow_pos hx 2).le

theorem F2K2_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ((1 - Real.exp (-((3:ℝ)/10 * q))) / q) ^ 2 / ((9:ℝ)/100)
      ≤ ((1 - Real.exp (-((3:ℝ)/10 * p))) / p) ^ 2 / ((9:ℝ)/100) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  -- the bracket `(1 - e^{-(3/10)t})/t` is antitone on `(0,∞)`, hence decreasing in `t`
  have hanti : (1 - Real.exp (-((3:ℝ)/10 * q))) / q
      ≤ (1 - Real.exp (-((3:ℝ)/10 * p))) / p :=
    scaledF_antitone ((3:ℝ)/10) (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hq) hpq
  -- the lower bracket is nonnegative, so squaring preserves the inequality
  have hq0 : 0 ≤ (1 - Real.exp (-((3:ℝ)/10 * q))) / q := by
    apply div_nonneg _ hq.le
    rw [sub_nonneg, Real.exp_le_one_iff]
    nlinarith
  have hsq : ((1 - Real.exp (-((3:ℝ)/10 * q))) / q) ^ 2
      ≤ ((1 - Real.exp (-((3:ℝ)/10 * p))) / p) ^ 2 :=
    pow_le_pow_left₀ hq0 hanti 2
  exact div_le_div_of_nonneg_right hsq (by norm_num)

end Work.A7
