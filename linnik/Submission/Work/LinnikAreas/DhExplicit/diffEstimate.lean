import Mathlib

namespace Work.LinnikAreas.DhExplicit

/-!
# The elementary "pole versus exceptional zero" estimate

For `j ≥ 1`, `c ≥ 5` and `β₁ ≤ 1` we prove

`1/(c-1)^{2j} - 1/(c-β₁)^{2j}
  + Re (1/((c-1) + iγ')^{2j}) - Re (1/((c-β₁) + iγ')^{2j})
  ≤ 4 j (1-β₁) / (c-1)^{2j+1}`.

Everything is elementary: writing `δ = 1 - β₁ ≥ 0`, `x = c - 1 ≥ 4`, both summands are of
the shape `f(w) - f(w + δ)` with `f(w) = 1/w^{2j}`, `Re w ≥ x`, and each is bounded by
`2j δ / x^{2j+1}`.  The second (complex) estimate is proved by the telescoping identity

`1/w^n - 1/(w+δ)^n = (1/w^n) (1 - (w/(w+δ))^n)`, `|1 - r^n| ≤ n |1 - r|` for `‖r‖ ≤ 1`,

together with `‖1 - w/(w+δ)‖ = δ/‖w+δ‖`.
-/

/-- If `δ ≥ 0` and `Re w ≥ 0` then `‖w‖ ≤ ‖w + δ‖`. -/
lemma norm_le_norm_add {w : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w.re) :
    ‖w‖ ≤ ‖w + (δ : ℂ)‖ := by
  have h : Complex.normSq w ≤ Complex.normSq (w + (δ : ℂ)) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith [hδ, hw]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg w, norm_nonneg (w + (δ : ℂ))]

/-- **Key elementary estimate.**  For `n ≥ 0`, `δ ≥ 0`, `x > 0` and `Re w ≥ x`,

`Re (1/w^n - 1/(w+δ)^n) ≤ n δ / x^{n+1}`. -/
lemma re_inv_pow_sub_inv_pow_le {n : ℕ} {w : ℂ} {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x)
    (hwx : x ≤ w.re) :
    (1 / w ^ n - 1 / (w + (δ : ℂ)) ^ n).re ≤ (n : ℝ) * δ / x ^ (n + 1) := by
  have hwr : 0 < w.re := lt_of_lt_of_le hx hwx
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwr; simp at hwr
  have hwd0 : w + (δ : ℂ) ≠ 0 := by
    intro h
    have hre : (w + (δ : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at hre
    linarith
  have hnormw : x ≤ ‖w‖ := le_trans hwx (Complex.re_le_norm w)
  have hnormwd : x ≤ ‖w + (δ : ℂ)‖ := by
    have h1 : x ≤ (w + (δ : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    exact le_trans h1 (Complex.re_le_norm _)
  have hQpos : 0 < ‖w + (δ : ℂ)‖ := lt_of_lt_of_le hx hnormwd
  have hPpos : 0 < ‖w‖ := lt_of_lt_of_le hx hnormw
  have hle : ‖w‖ ≤ ‖w + (δ : ℂ)‖ := norm_le_norm_add hδ (le_of_lt hwr)
  set r : ℂ := w / (w + (δ : ℂ)) with hr
  have hrn : ‖r‖ ≤ 1 := by
    rw [hr, norm_div]
    exact (div_le_one hQpos).mpr hle
  have hid : 1 / w ^ n - 1 / (w + (δ : ℂ)) ^ n = (1 / w ^ n) * (1 - r ^ n) := by
    have hrw : r ^ n = w ^ n * ((w + (δ : ℂ)) ^ n)⁻¹ := by
      rw [hr, div_pow, div_eq_mul_inv]
    rw [hrw, one_div, one_div]
    have hA : (w ^ n)⁻¹ * (w ^ n * ((w + (δ : ℂ)) ^ n)⁻¹) = ((w + (δ : ℂ)) ^ n)⁻¹ := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hw0), one_mul]
    rw [mul_sub, mul_one, hA]
  have hsum_le : ‖∑ i ∈ Finset.range n, r ^ i‖ ≤ (n : ℝ) := by
    calc ‖∑ i ∈ Finset.range n, r ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖r ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hrn
      _ = (n : ℝ) := by simp
  have hrone : ‖1 - r ^ n‖ ≤ (n : ℝ) * ‖1 - r‖ := by
    have hgeom : 1 - r ^ n = (∑ i ∈ Finset.range n, r ^ i) * (1 - r) := by
      have h := geom_sum_mul r n
      have h2 : r ^ n = (∑ i ∈ Finset.range n, r ^ i) * (r - 1) + 1 := by rw [h]; ring
      rw [h2]; ring
    rw [hgeom, norm_mul]
    exact mul_le_mul_of_nonneg_right hsum_le (norm_nonneg _)
  have h1mr : ‖1 - r‖ = δ / ‖w + (δ : ℂ)‖ := by
    have h2 : 1 - r = (δ : ℂ) / (w + (δ : ℂ)) := by
      rw [hr]
      field_simp
      ring
    rw [h2, norm_div]
    simp [Real.norm_eq_abs, abs_of_nonneg hδ]
  calc (1 / w ^ n - 1 / (w + (δ : ℂ)) ^ n).re
      ≤ ‖1 / w ^ n - 1 / (w + (δ : ℂ)) ^ n‖ := Complex.re_le_norm _
    _ = (1 / ‖w‖ ^ n) * ‖1 - r ^ n‖ := by rw [hid, norm_mul, norm_div, norm_one, norm_pow]
    _ ≤ (1 / ‖w‖ ^ n) * ((n : ℝ) * (δ / ‖w + (δ : ℂ)‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← h1mr]
        exact hrone
    _ = (n : ℝ) * δ / (‖w‖ ^ n * ‖w + (δ : ℂ)‖) := by
        field_simp
    _ ≤ (n : ℝ) * δ / x ^ (n + 1) := by
        apply div_le_div_of_nonneg_left _ _ _
        · positivity
        · positivity
        · rw [pow_succ]
          exact mul_le_mul (pow_le_pow_left₀ (le_of_lt hx) hnormw n) hnormwd (le_of_lt hx)
            (by positivity)

/-- Real form of the previous estimate: `(1/r^n - 1/s^n).re` computed for real `r, s`. -/
lemma ofReal_sub_inv_pow_re (r s : ℝ) (n : ℕ) :
    (1 / ((r : ℝ) : ℂ) ^ n - 1 / ((s : ℝ) : ℂ) ^ n).re = 1 / r ^ n - 1 / s ^ n := by
  have e1 : ((1 / r ^ n : ℝ) : ℂ) = 1 / ((r : ℝ) : ℂ) ^ n := by push_cast; ring
  have e2 : ((1 / s ^ n : ℝ) : ℂ) = 1 / ((s : ℝ) : ℂ) ^ n := by push_cast; ring
  rw [← e1, ← e2, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]

/-- **The elementary "pole versus exceptional zero" estimate.**  For `j ≥ 1`, `c ≥ 5` and
`β₁ ≤ 1`,

`1/(c-1)^{2j} - 1/(c-β₁)^{2j}
  + Re (1/((c-1) + iγ')^{2j}) - Re (1/((c-β₁) + iγ')^{2j})
  ≤ 4 j (1-β₁) / (c-1)^{2j+1}`.

This is the difference between the "pole at `s = 1`" term of the explicit formula and the same
expression evaluated at the exceptional zero `β₁`, and it is precisely the constant `4j` of the
statement `diffExplicitFormulaReal`.

PROOF ROUTE (elementary, no analysis): write `δ = 1 - β₁ ≥ 0`, `x = c - 1 ≥ 4`.
* First term: `1/x^{2j} - 1/(x+δ)^{2j} = ((x+δ)^{2j} - x^{2j})/(x^{2j}(x+δ)^{2j})`; expand the
  numerator with `mul_geom_sum` (or bound it by `2j δ (x+δ)^{2j-1}` termwise, since
  `(x+δ)^{2j-1-k}x^k ≤ (x+δ)^{2j-1}` for `k < 2j`) to get
  `≤ 2j δ/(x^{2j}(x+δ)) ≤ 2j δ/x^{2j+1}`.
* Second term: `w = x + iγ'` satisfies `Re w = x > 0` and `|w + δ| ≥ |w|`, so
  `Re (1/w^{2j} - 1/(w+δ)^{2j}) = Re (((w+δ)^{2j} - w^{2j})/(w^{2j}(w+δ)^{2j}))`
  `≤ |(w+δ)^{2j} - w^{2j}|/(|w|^{2j}|w+δ|^{2j})`
  `≤ 2jδ|w+δ|^{2j-1}/(|w|^{2j}|w+δ|^{2j}) = 2jδ/(|w|^{2j}|w+δ|) ≤ 2jδ/x^{2j+1}`
  (using `|(w+δ)^{2j} - w^{2j}| ≤ 2jδ|w+δ|^{2j-1}`, from the telescoping
  `(w+δ)^{2j} - w^{2j} = δ Σ_{k<2j}(w+δ)^{2j-1-k}w^k` and `|w| ≤ |w+δ|`).
Adding the two bounds gives `4jδ/x^{2j+1}`, as claimed. -/
theorem diffEstimate {j : ℕ} (hj : 1 ≤ j) {c γ' β₁ : ℝ} (hc : 5 ≤ c) (hβ : β₁ ≤ 1) :
    (1 / (c - 1) ^ (2 * j) - 1 / (c - β₁) ^ (2 * j))
      + ((1 / (((c - 1 : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re
        - (1 / (((c - β₁ : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re)
      ≤ 4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := by
  have _ : 1 ≤ j := hj
  have hx4 : (0 : ℝ) < c - 1 := by linarith
  have hδ : (0 : ℝ) ≤ 1 - β₁ := by linarith
  have hcβ : c - β₁ = (c - 1) + (1 - β₁) := by ring
  -- first (real) term
  have hA : (1 / (c - 1) ^ (2 * j) - 1 / (c - β₁) ^ (2 * j))
      ≤ (2 * j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := by
    have h := re_inv_pow_sub_inv_pow_le (n := 2 * j) (w := ((c - 1 : ℝ) : ℂ))
      (δ := 1 - β₁) (x := c - 1) hδ hx4 (by simp)
    have hw : (((c - 1 : ℝ) : ℂ) + ((1 - β₁ : ℝ) : ℂ)) = ((c - β₁ : ℝ) : ℂ) := by
      push_cast; ring
    have h2j : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by push_cast; ring
    rw [hw, ofReal_sub_inv_pow_re, h2j] at h
    exact h
  -- second (complex) term
  have hB : ((1 / (((c - 1 : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re
        - (1 / (((c - β₁ : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re)
      ≤ (2 * j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := by
    have h := re_inv_pow_sub_inv_pow_le (n := 2 * j)
      (w := (((c - 1 : ℝ) : ℂ) + Complex.I * (γ' : ℂ))) (δ := 1 - β₁) (x := c - 1) hδ hx4
      (by simp)
    have hw : (((c - β₁ : ℝ) : ℂ) + Complex.I * (γ' : ℂ))
        = ((((c - 1 : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) + ((1 - β₁ : ℝ) : ℂ)) := by
      push_cast; ring
    have h2j : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by push_cast; ring
    rw [h2j] at h
    rw [hw, ← Complex.sub_re]
    exact h
  calc (1 / (c - 1) ^ (2 * j) - 1 / (c - β₁) ^ (2 * j))
        + ((1 / (((c - 1 : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re
          - (1 / (((c - β₁ : ℝ) : ℂ) + Complex.I * (γ' : ℂ)) ^ (2 * j)).re)
      ≤ (2 * j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1)
        + (2 * j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := add_le_add hA hB
    _ = 4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) := by ring

end Work.LinnikAreas.DhExplicit
