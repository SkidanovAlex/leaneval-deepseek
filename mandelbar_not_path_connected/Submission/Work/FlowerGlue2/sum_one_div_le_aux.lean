import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- The pointwise logarithmic bound `1/(b+1) ≤ log ((b+1)/b)` for `b > 0`.
This is `log x ≤ x - 1` applied to `x = b/(b+1)`. -/
lemma one_div_succ_le_log {b : ℝ} (hb : 0 < b) :
    (1 : ℝ) / (b + 1) ≤ Real.log ((b + 1) / b) := by
  have hx : 0 < b / (b + 1) := div_pos hb (by positivity)
  have hlog : Real.log (b / (b + 1)) ≤ b / (b + 1) - 1 := Real.log_le_sub_one_of_pos hx
  have h1 : b / (b + 1) - 1 = -(1 / (b + 1)) := by field_simp; ring
  rw [h1] at hlog
  have h2 : Real.log ((b + 1) / b) = Real.log ((b / (b + 1))⁻¹) := by
    congr 1
    field_simp
  rw [h2, Real.log_inv]
  linarith

/-- Telescoping bound for the tail of the harmonic-type sum:
`∑_{k<n} 1/(a+k+1) ≤ log ((a+n)/a)` for `a > 0`. -/
lemma sum_tail_le_log {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (a + (k + 1)) ≤ Real.log ((a + n) / a) := by
  induction n with
  | zero => simp [ha.ne']
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hstep : (1 : ℝ) / (a + (↑n + 1)) ≤ Real.log ((a + (↑n + 1)) / (a + ↑n)) := by
      have h := one_div_succ_le_log (b := a + ↑n) (by positivity)
      simpa [add_assoc] using h
    have hkey : Real.log ((a + (↑n + 1)) / a)
        = Real.log ((a + ↑n) / a) + Real.log ((a + (↑n + 1)) / (a + ↑n)) := by
      rw [← Real.log_mul]
      · congr 1
        field_simp
      · positivity
      · positivity
    rw [hkey]
    linarith

theorem sum_one_div_le_aux {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 : ℝ) / (a + k) ≤ 1 / a + Real.log ((a + m) / a) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero,
      div_self ha.ne', Real.log_one]
    positivity
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [Finset.sum_range_succ']
    push_cast
    have htail := sum_tail_le_log ha n
    have hlog : Real.log ((a + ↑n) / a) ≤ Real.log ((a + (↑n + 1)) / a) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt ha)
    have hfirst : (1 : ℝ) / (a + (0 : ℝ)) = 1 / a := by norm_num
    rw [hfirst]
    linarith

end Work.FlowerGlue2
