import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- Cauchy–Schwarz/AM–GM step: if `|T| ≤ B·∑_{m<n}|v m|` then for nonnegative `QQ`
`|T·U·QQ| ≤ (1/4)·U²·QQ + B²·n·∑_{m<n} v m²·QQ`. -/
theorem slice_ang_A_cs (k : ℕ) (B QQ T U : ℝ) (v : ℕ → ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ QQ)
    (hT : |T| ≤ B * ∑ m ∈ Finset.range (k + 2), |v m|) :
    |T * U * QQ| ≤ (1 / 4) * (U ^ 2 * QQ)
      + (B ^ 2 * ((k : ℝ) + 2)) * ∑ m ∈ Finset.range (k + 2), (v m) ^ 2 * QQ := by
  have _hB0 : (0 : ℝ) ≤ B := hB
  rcases eq_or_lt_of_le hQ with h0 | hpos
  · rw [← h0]
    simp
  set S : ℝ := ∑ m ∈ Finset.range (k + 2), |v m| with hSdef
  set Q : ℝ := ∑ m ∈ Finset.range (k + 2), (v m) ^ 2 with hQdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; exact Finset.sum_nonneg fun m _ => sq_nonneg _
  have hcs : S ^ 2 ≤ ((k : ℝ) + 2) * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 2)) (f := fun m => |v m|) (α := ℝ)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_ofNat, sq_abs] at h
    rwa [hSdef, hQdef]
  have hkey : |T| * |U| ≤ (1 / 4) * U ^ 2 + B ^ 2 * ((k : ℝ) + 2) * Q := by
    have h1 : |T| * |U| ≤ B * S * |U| :=
      mul_le_mul_of_nonneg_right hT (abs_nonneg U)
    have h2 : B * S * |U| ≤ (1 / 4) * U ^ 2 + (B * S) ^ 2 := by
      have h := two_mul_le_add_sq (|U| / 2) (B * S)
      have hU : (|U| / 2) ^ 2 = (1 / 4) * U ^ 2 := by rw [div_pow, sq_abs]; ring
      nlinarith [h, hU]
    have h3 : (B * S) ^ 2 ≤ B ^ 2 * ((k : ℝ) + 2) * Q := by
      have h4 : (B * S) ^ 2 ≤ B ^ 2 * (((k : ℝ) + 2) * Q) := by
        calc (B * S) ^ 2 = B ^ 2 * S ^ 2 := by ring
          _ ≤ B ^ 2 * (((k : ℝ) + 2) * Q) :=
              mul_le_mul_of_nonneg_left hcs (sq_nonneg B)
      linarith [h4, hB]
    linarith
  have hprod : |T * U * QQ| = |T| * |U| * QQ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hQ]
  rw [hprod]
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
  have hsum : Q * QQ = ∑ m ∈ Finset.range (k + 2), (v m) ^ 2 * QQ := by
    rw [hQdef]; exact Finset.sum_mul _ _ _
  calc |T| * |U| * QQ
      ≤ ((1 / 4) * U ^ 2 + B ^ 2 * ((k : ℝ) + 2) * Q) * QQ := hmul
    _ = (1 / 4) * (U ^ 2 * QQ) + (B ^ 2 * ((k : ℝ) + 2)) * (Q * QQ) := by ring
    _ = (1 / 4) * (U ^ 2 * QQ)
          + (B ^ 2 * ((k : ℝ) + 2)) * ∑ m ∈ Finset.range (k + 2), (v m) ^ 2 * QQ := by
        rw [hsum]

end Work.FTS.EllipticEst.remov
