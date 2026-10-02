import Mathlib
import Submission.Work.PARIMPL2.Direct.oidDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- A sequence that drops by at least `1/3` at every step below `n` satisfies
`x m ≤ x 0 - m/3` for every `m ≤ n`. -/
theorem oidCg_telescope (x : ℕ → ℝ) (n : ℕ)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    ∀ m ≤ n, x m ≤ x 0 - m / 3 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hm' : m < n := Nat.lt_of_succ_le hm
    have h1 : x (m + 1) ≤ x m - 1 / 3 := hdec m hm'
    have h2 : x m ≤ x 0 - m / 3 := ih (Nat.le_of_lt hm')
    have h3 : x 0 - (m : ℝ) / 3 - 1 / 3 = x 0 - ((m + 1 : ℕ) : ℝ) / 3 := by
      push_cast; ring
    linarith

/-- Under `λ R² ≤ 1` and `R ≥ 128`, `3πλ ≤ 1/R`. -/
theorem oidCg_three_pi_lam_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) : 3 * Real.pi * lam ≤ 1 / R := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hlam_le : lam ≤ 1 / R ^ 2 := by
    rw [le_div_iff₀ hR2pos]; linarith
  have hpiR : 3 * Real.pi ≤ R := by
    have := Real.pi_lt_four; linarith
  have hchain : 3 * Real.pi * lam ≤ 3 * Real.pi * (1 / R ^ 2) :=
    mul_le_mul_of_nonneg_left hlam_le (by positivity)
  have hfin : 3 * Real.pi * (1 / R ^ 2) ≤ 1 / R := by
    rw [mul_one_div, div_le_iff₀ hR2pos]
    rw [show (1 / R) * R ^ 2 = R by field_simp]
    exact hpiR
  linarith

/-- The index range is short: a sequence in the window that decreases by `1/3` at each
step spans at most `3π/λ` steps, whence `n λ² ≤ 1/R`. -/
theorem oidCg_n_lam2_le (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (n : ℕ) (x : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    (n : ℝ) * lam ^ 2 ≤ 1 / R := by
  have htel := oidCg_telescope x n hdec n le_rfl
  have h2 := hx2 0 (Nat.zero_le n)
  have h3 := hx1 n le_rfl
  have hn3 : (n : ℝ) / 3 ≤ Real.pi / lam := by linarith
  have hn_le : (n : ℝ) ≤ 3 * (Real.pi / lam) := by linarith
  have h1 : (n : ℝ) * lam ^ 2 ≤ (3 * (Real.pi / lam)) * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hn_le (sq_nonneg lam)
  have h2' : (3 * (Real.pi / lam)) * lam ^ 2 = 3 * Real.pi * lam := by field_simp
  have h3' : 3 * Real.pi * lam ≤ 1 / R := oidCg_three_pi_lam_le lam R hlam hR hlamR
  linarith

/-- The `oidCg` sum splits as `cp · n λ²` plus `cp` times the `λ²/D` sum. -/
theorem oidCg_sum_split (lam cp : ℝ) (x y : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, oidCg lam cp x y j)
      = cp * ((n : ℝ) * lam ^ 2)
        + cp * (∑ j ∈ Finset.range n, lam ^ 2 / ocDen lam x y j) := by
  simp only [oidCg]
  rw [← mul_add, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem oidCg_sum (lam R cp : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcp : 0 ≤ cp) (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hG : ∑ j ∈ Finset.range n, lam ^ 2 / Work.PARIMPL2.Direct.ocDen lam x y j ≤ 24 / R) :
    ∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.oidCg lam cp x y j ≤ 25 * cp / R := by
  have hn_lam2 : (n : ℝ) * lam ^ 2 ≤ 1 / R := oidCg_n_lam2_le lam R hlam hR hlamR n x hx1 hx2 hdec
  rw [oidCg_sum_split]
  have hA : cp * ((n : ℝ) * lam ^ 2) ≤ cp * (1 / R) := mul_le_mul_of_nonneg_left hn_lam2 hcp
  have hB : cp * (∑ j ∈ Finset.range n, lam ^ 2 / ocDen lam x y j) ≤ cp * (24 / R) :=
    mul_le_mul_of_nonneg_left hG hcp
  have hfin : cp * (1 / R) + cp * (24 / R) = 25 * cp / R := by ring
  linarith

end Work.PARIMPL2.Direct
