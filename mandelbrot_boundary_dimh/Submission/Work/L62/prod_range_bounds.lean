import Mathlib

namespace Work.L62

/-- If `‖a k - 1‖ ≤ b k` with `0 ≤ b k ≤ 1/2`, then the partial products of the `a k`
are trapped between the partial products of `1 - b k` and `1 + b k`, and the
distance of the partial product from `1` is at most the corresponding product of
`(1 + b k)` minus `1`. -/
theorem prod_range_bounds {a : ℕ → ℂ} {b : ℕ → ℝ} (hb0 : ∀ k, 0 ≤ b k) (hb : ∀ k, b k ≤ 1 / 2)
    (ha : ∀ k, ‖a k - 1‖ ≤ b k) (m : ℕ) :
    ‖(∏ k ∈ Finset.range m, a k) - 1‖ ≤ (∏ k ∈ Finset.range m, (1 + b k)) - 1 ∧
    (∏ k ∈ Finset.range m, (1 - b k)) ≤ ‖(∏ k ∈ Finset.range m, a k)‖ ∧
    ‖(∏ k ∈ Finset.range m, a k)‖ ≤ ∏ k ∈ Finset.range m, (1 + b k) := by
  have h1 : ∀ k, (0 : ℝ) < 1 + b k := fun k => by linarith [hb0 k]
  have h2 : ∀ k, (0 : ℝ) ≤ 1 - b k := fun k => by linarith [hb k]
  -- upper bound for the norm of each factor
  have hA : ∀ k, ‖a k‖ ≤ 1 + b k := fun k => by
    have h := norm_add_le (a k - 1) (1 : ℂ)
    have h' : (a k - 1) + 1 = a k := by ring
    rw [h', norm_one] at h
    linarith [ha k]
  -- lower bound for the norm of each factor
  have hB : ∀ k, 1 - b k ≤ ‖a k‖ := fun k => by
    have h := abs_norm_sub_norm_le (a k) (1 : ℂ)
    rw [norm_one] at h
    have h' : (-(‖a k - 1‖) : ℝ) ≤ ‖a k‖ - 1 := (abs_le.mp h).1
    linarith [ha k]
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ihA, ihB, ihC⟩ := ih
    have hBpnn : 0 ≤ ∏ k ∈ Finset.range m, (1 + b k) :=
      Finset.prod_nonneg fun k _ => le_of_lt (h1 k)
    have hBmnn : 0 ≤ ∏ k ∈ Finset.range m, (1 - b k) :=
      Finset.prod_nonneg fun k _ => h2 k
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    refine ⟨?_, ?_, ?_⟩
    · have hdecomp : (∏ k ∈ Finset.range m, a k) * a m - 1
          = ((∏ k ∈ Finset.range m, a k) - 1) + (∏ k ∈ Finset.range m, a k) * (a m - 1) := by
        ring
      rw [hdecomp]
      calc ‖((∏ k ∈ Finset.range m, a k) - 1) + (∏ k ∈ Finset.range m, a k) * (a m - 1)‖
          ≤ ‖(∏ k ∈ Finset.range m, a k) - 1‖
              + ‖(∏ k ∈ Finset.range m, a k) * (a m - 1)‖ := norm_add_le _ _
        _ = ‖(∏ k ∈ Finset.range m, a k) - 1‖ + ‖(∏ k ∈ Finset.range m, a k)‖ * ‖a m - 1‖ := by
              rw [norm_mul]
        _ ≤ ((∏ k ∈ Finset.range m, (1 + b k)) - 1)
              + (∏ k ∈ Finset.range m, (1 + b k)) * b m :=
              add_le_add ihA (mul_le_mul ihC (ha m) (norm_nonneg _) hBpnn)
        _ = (∏ k ∈ Finset.range m, (1 + b k)) * (1 + b m) - 1 := by ring
    · calc (∏ k ∈ Finset.range m, (1 - b k)) * (1 - b m)
          ≤ ‖∏ k ∈ Finset.range m, a k‖ * ‖a m‖ :=
            mul_le_mul ihB (hB m) (h2 m) (norm_nonneg _)
        _ = ‖(∏ k ∈ Finset.range m, a k) * a m‖ := (norm_mul _ _).symm
    · rw [norm_mul]
      calc ‖∏ k ∈ Finset.range m, a k‖ * ‖a m‖
          ≤ (∏ k ∈ Finset.range m, (1 + b k)) * (1 + b m) :=
            mul_le_mul ihC (hA m) (norm_nonneg _) hBpnn
        _ = (∏ k ∈ Finset.range m, (1 + b k)) * (1 + b m) := rfl

end Work.L62
