import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Elementary numerical estimate: if `0 < b ≤ a` and `s ≤ a - b` with `s > 0`, then
`1/a^2 ≤ (1/s) * (1/b - 1/a)`. -/
private lemma one_div_sq_le (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hs : 0 < s) (h : s ≤ a - b) :
    (1:ℝ)/a^2 ≤ (1/s)*(1/b - 1/a) := by
  have h1 : (1:ℝ)/a^2 ≤ 1/(a*b) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h2 : (1:ℝ)/(a*b) ≤ (1/s)*(1/b - 1/a) := by
    have hrw : (1/s)*(1/b - 1/a) = (a-b)/(s*a*b) := by
      field_simp
    rw [hrw, le_div_iff₀ (by positivity : (0:ℝ) < s*a*b)]
    have h3 : (1:ℝ)/(a*b) * (s*a*b) = s := by field_simp
    rw [h3]
    linarith
  linarith

theorem sum_inv_sq_le_of_sep (x : ℕ → ℝ) (a s : ℝ) (n : ℕ)
    (ha : 0 < a) (hs : 0 < s)
    (hb : ∀ j ≤ n, a ≤ x j) (hdec : ∀ j < n, x (j + 1) ≤ x j - s) :
    ∑ j ∈ Finset.range n, (1:ℝ) / (x j) ^ 2 ≤ 1 / (s * a) := by
  have key : ∀ j ∈ Finset.range n,
      (1:ℝ)/(x j)^2 ≤ (1/s) * (1/(x (j+1)) - 1/(x j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hxj : 0 < x j := lt_of_lt_of_le ha (hb j (le_of_lt hj))
    have hxj1 : 0 < x (j+1) := lt_of_lt_of_le ha (hb (j+1) (by omega))
    have hdiff : s ≤ x j - x (j+1) := by linarith [hdec j hj]
    have hba : x (j+1) ≤ x j := by linarith [hdec j hj, hs]
    exact one_div_sq_le (x j) (x (j+1)) s hxj hxj1 hba hs hdiff
  calc ∑ j ∈ Finset.range n, (1:ℝ)/(x j)^2
      ≤ ∑ j ∈ Finset.range n, (1/s) * (1/(x (j+1)) - 1/(x j)) := Finset.sum_le_sum key
    _ = (1/s) * (1/(x n) - 1/(x 0)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_sub (fun j => (1:ℝ)/(x j)) n
    _ ≤ 1 / (s * a) := by
        have hxn : a ≤ x n := hb n le_rfl
        have h1xn : (1:ℝ)/x n ≤ 1/a := one_div_le_one_div_of_le ha hxn
        have h1x0 : (0:ℝ) ≤ 1/x 0 := by
          have : (0:ℝ) < x 0 := lt_of_lt_of_le ha (hb 0 (Nat.zero_le n))
          positivity
        have hle : (1:ℝ)/x n - 1/x 0 ≤ 1/a := by linarith
        calc (1/s) * (1/(x n) - 1/(x 0))
            ≤ (1/s) * (1/a) := by
              apply mul_le_mul_of_nonneg_left hle
              positivity
          _ = 1 / (s * a) := by field_simp

end Work.PARIMPL2.Direct
