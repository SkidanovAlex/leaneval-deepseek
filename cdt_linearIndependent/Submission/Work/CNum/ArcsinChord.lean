import Mathlib

/-!
# The CNum chord/arc bound `2 arcsin u ≤ 2u + u³/3 + u⁵/5` on `[0, 1/4]`

For `0 ≤ u ≤ 1/4` we prove the elementary inequality

`2 * Real.arcsin u ≤ 2 * u + u ^ 3 / 3 + u ^ 5 / 5`.

The strategy is monotonicity.  Set
`G y = 2y + y³/3 + y⁵/5 - 2 arcsin y`, so that the claim is `G u ≥ G 0 = 0`.
On `(0, 1/4)` one has

`G' y = 2 + y² + y⁴ - 2/√(1-y²)`,

and `G' y ≥ 0` follows from `2/√(1-y²) ≤ 2 + y² + y⁴`, which after multiplying by
the positive number `√(1-y²)` and squaring is equivalent to

`4 ≤ (2 + y² + y⁴)² (1 - y²) = 4 + y⁴ (1 - 3y² - y⁴ - y⁶)`,

i.e. `3y² + y⁴ + y⁶ ≤ 1`, which holds because `y ≤ 1/4`.  Hence `G` is monotone
on `[0,1/4]` and the result follows.
-/

namespace Work.CNum

/-- The auxiliary function `2y + y³/3 + y⁵/5 - 2 arcsin y` whose monotonicity gives
the chord bound. -/
private noncomputable def G (y : ℝ) : ℝ := 2 * y + y ^ 3 / 3 + y ^ 5 / 5 - 2 * Real.arcsin y

private lemma continuousOn_G : ContinuousOn G (Set.Icc 0 (1 / 4)) := by
  have : Continuous G := by unfold G; fun_prop
  exact this.continuousOn

/-- Derivative of `G` at a point away from `±1`. -/
private lemma hasDerivAt_G (x : ℝ) (hx1 : x ≠ 1) (hxn1 : x ≠ -1) :
    HasDerivAt G (2 + x ^ 2 + x ^ 4 - 2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
  change HasDerivAt (fun y : ℝ => 2 * y + y ^ 3 / 3 + y ^ 5 / 5 - 2 * Real.arcsin y)
    (2 + x ^ 2 + x ^ 4 - 2 * (1 / Real.sqrt (1 - x ^ 2))) x
  have ha : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hb : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (((3 : ℝ) * x ^ (3 - 1) * 1) / 3) x := by
      simpa using ((hasDerivAt_id x).pow 3).div_const 3
    have hv : ((3 : ℝ) * x ^ (3 - 1) * 1) / 3 = x ^ 2 := by ring_nf
    rwa [hv] at h
  have hc : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
    have h : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (((5 : ℝ) * x ^ (5 - 1) * 1) / 5) x := by
      simpa using ((hasDerivAt_id x).pow 5).div_const 5
    have hv : ((5 : ℝ) * x ^ (5 - 1) * 1) / 5 = x ^ 4 := by ring_nf
    rwa [hv] at h
  have hpoly : HasDerivAt (fun y : ℝ => 2 * y + y ^ 3 / 3 + y ^ 5 / 5) (2 + x ^ 2 + x ^ 4) x := by
    convert (ha.add hb).add hc using 1 <;> try rfl
  have harc : HasDerivAt (fun y : ℝ => 2 * Real.arcsin y)
      (2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
    simpa using (Real.hasDerivAt_arcsin hxn1 hx1).const_mul 2
  convert hpoly.sub harc using 1 <;> try rfl

/-- The pointwise inequality `2/√(1-x²) ≤ 2 + x² + x⁴` for `0 ≤ x ≤ 1/4`. -/
private lemma arcsin_growth_key (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    2 * (1 / Real.sqrt (1 - x ^ 2)) ≤ 2 + x ^ 2 + x ^ 4 := by
  have hx2 : x ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hx4 : x ^ 4 ≤ (1 / 256 : ℝ) := by
    have h : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h]; nlinarith [sq_nonneg (x ^ 2)]
  have hx6 : x ^ 6 ≤ (1 / 4096 : ℝ) := by
    have h : x ^ 6 = (x ^ 2) ^ 3 := by ring
    rw [h]; nlinarith [sq_nonneg (x ^ 2)]
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos_of_pos hpos
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : (2 : ℝ) ^ 2 ≤ ((2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2)) ^ 2 := by
    rw [mul_pow, hs2]
    have hsum : 3 * x ^ 2 + x ^ 4 + x ^ 6 ≤ 1 := by nlinarith
    have hkey : (2 + x ^ 2 + x ^ 4) ^ 2 * (1 - x ^ 2)
        = 4 + x ^ 4 * (1 - 3 * x ^ 2 - x ^ 4 - x ^ 6) := by ring
    rw [hkey]
    have : 0 ≤ x ^ 4 * (1 - 3 * x ^ 2 - x ^ 4 - x ^ 6) := by nlinarith [sq_nonneg (x ^ 2)]
    linarith
  have hAs : 0 ≤ (2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2) := by positivity
  have h2 : (2 : ℝ) ≤ (2 + x ^ 2 + x ^ 4) * Real.sqrt (1 - x ^ 2) := by
    have habs := sq_le_sq.mp hsq
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hAs] at habs
    exact habs
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt hs
  have h3 : 2 * (Real.sqrt (1 - x ^ 2))⁻¹ ≤ (2 + x ^ 2 + x ^ 4) := by
    have h2' := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hs.le)
    rwa [mul_assoc, mul_inv_cancel₀ hsne, mul_one] at h2'
  rwa [one_div]

theorem ArcsinChord {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) :
    2 * Real.arcsin u ≤ 2 * u + u ^ 3 / 3 + u ^ 5 / 5 := by
  have hmono : MonotoneOn G (Set.Icc 0 (1 / 4)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 4)) ?_ ?_ ?_
    · exact continuousOn_G
    · rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_G x (by linarith [hx.2]) (by linarith [hx.1])).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hasDerivAt_G x (by linarith [hx.2]) (by linarith [hx.1])).deriv]
      have hk := arcsin_growth_key x (le_of_lt hx.1) (le_of_lt hx.2)
      linarith
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (1 / 4) := ⟨le_refl 0, by norm_num⟩
  have hmemu : u ∈ Set.Icc 0 (1 / 4) := ⟨h0, h1⟩
  have hgu : G 0 ≤ G u := hmono hmem0 hmemu h0
  have hgz : G 0 = 0 := by simp [G]
  have hnonneg : 0 ≤ G u := by rw [← hgz]; exact hgu
  dsimp only [G] at hnonneg
  linarith

end Work.CNum
