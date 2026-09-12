import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

lemma exists_geom_pow_le_one_div {θ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hL1 : 1 ≤ L) :
    ∃ q : ℕ, 1 ≤ q ∧ θ ^ q ≤ 1 / L := by
  have hθinv1 : 1 < θ⁻¹ := (one_lt_inv₀ hθ0).2 hθ1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt L hθinv1
  -- hn : L < (θ⁻¹) ^ n
  have hn_ne : n ≠ 0 := by
    intro hn0
    rw [hn0, pow_zero] at hn
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hle : θ ^ n ≤ 1 / L := by
    rw [inv_pow] at hn
    -- hn : L < (θ ^ n)⁻¹
    have hlt : θ ^ n < 1 / L := by
      simpa using one_div_lt_one_div_of_lt hLpos hn
    exact le_of_lt hlt
  exact ⟨n, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne), hle⟩

end Commons.Analysis.Real