import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem oidNatLam (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (x : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    (n : ℝ) * lam ^ 2 ≤ 3 * Real.pi / R ^ 2 := by
  -- The sequence decreases by at least 1/3 at each step, so x n ≤ x 0 - n/3.
  have hmono : ∀ k ≤ n, x k ≤ x 0 - (k:ℝ)/3 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        have hmn : m < n := Nat.lt_of_succ_le hm
        have hmle : m ≤ n := le_of_lt hmn
        have hstep := hdec m hmn
        have ihm := ih hmle
        push_cast
        linarith
  -- Since R/4 + 2 ≤ x n ≤ x 0 - n/3 ≤ π/lam - R/4 - n/3, we get n/3 ≤ π/lam.
  have hkey : (n:ℝ)/3 ≤ Real.pi / lam := by
    have h1 := hmono n le_rfl
    have h2 := hx1 n le_rfl
    have h3 := hx2 0 (Nat.zero_le n)
    have h4 := hx1 0 (Nat.zero_le n)
    linarith
  have hlam2 : 0 < lam^2 := sq_pos_of_pos hlam
  -- Multiplying by lam^2 > 0: n * lam^2 ≤ 3 * π * lam.
  have hmid : (n:ℝ) * lam^2 ≤ 3 * Real.pi * lam := by
    have hm := mul_le_mul_of_nonneg_right hkey (le_of_lt hlam2)
    have hdiv : (Real.pi / lam) * lam^2 = Real.pi * lam := by field_simp
    rw [hdiv] at hm
    have : (n:ℝ)/3 * lam^2 = (n:ℝ)*lam^2/3 := by ring
    rw [this] at hm
    linarith
  have hRpos : 0 < R := by linarith
  have hR2 : 0 < R^2 := sq_pos_of_pos hRpos
  -- lam * R^2 ≤ 1 gives lam ≤ 1/R^2, hence 3 * π * lam ≤ 3 * π / R^2.
  have hlamle : lam ≤ 1/R^2 := by
    rw [le_div_iff₀ hR2]; exact hlamR
  have hfinal : 3*Real.pi*lam ≤ 3*Real.pi/R^2 := by
    have := mul_le_mul_of_nonneg_left hlamle (by positivity : (0:ℝ) ≤ 3*Real.pi)
    rwa [mul_one_div] at this
  linarith

end Work.PARIMPL2.Direct
