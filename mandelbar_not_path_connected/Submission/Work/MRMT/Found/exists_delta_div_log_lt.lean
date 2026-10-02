import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

theorem exists_delta_div_log_lt {c A ε : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∀ t : ℝ, 0 < t → t < δ → c * A / Real.log (1 / t) < ε ^ 2 := by
  have hcA : 0 ≤ c * A := mul_nonneg hc.le hA
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  set M : ℝ := c * A / ε ^ 2 with hM
  have hMnn : 0 ≤ M := by rw [hM]; exact div_nonneg hcA hε2.le
  refine ⟨min (1/4) (Real.exp (-(M + 1))), ?_, min_le_left _ _, ?_⟩
  · exact lt_min (by norm_num) (Real.exp_pos _)
  · intro t ht0 htδ
    have ht_exp : t < Real.exp (-(M + 1)) := lt_of_lt_of_le htδ (min_le_right _ _)
    have h1 : Real.exp (M + 1) < 1 / t := by
      have h := one_div_lt_one_div_of_lt ht0 ht_exp
      rw [Real.exp_neg, one_div, inv_inv] at h
      simpa [one_div] using h
    have hlog' : M + 1 < Real.log (1 / t) := by
      have h := Real.log_lt_log (Real.exp_pos (M + 1)) h1
      rwa [Real.log_exp] at h
    have hlog : M < Real.log (1 / t) := by linarith
    have hpos : 0 < Real.log (1 / t) := by linarith
    rw [div_lt_iff₀ hpos]
    have hcA_eq : c * A = M * ε ^ 2 := by rw [hM]; field_simp
    rw [hcA_eq]
    calc M * ε ^ 2 = ε ^ 2 * M := by ring
      _ < ε ^ 2 * Real.log (1 / t) := mul_lt_mul_of_pos_left hlog hε2

end Work.MRMT.Found
