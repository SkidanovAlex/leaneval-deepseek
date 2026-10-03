import Mathlib

namespace Work.Peluse.PET

noncomputable section

/-- Régime (B) core: the rearrangement `a · γ^(2^m−1) · H ≤ T · M / 2` from
`H · (1000 · (m+1)) ≤ γ · M` (multiply by `2 · 1000^(2^m)` and cancel `γ^(2^m-1)`). -/
theorem regimeB_core {m : ℕ} {γ T a : ℝ} {H M : ℕ}
    (hγ : 0 < γ) (hTdef : T = γ ^ (2 ^ m) / (1000 : ℝ) ^ (2 ^ m))
    (ha : a = ((m : ℝ) + 1) / (2 * (1000 : ℝ) ^ (2 ^ m - 1)))
    (hH : 0 < (H : ℝ)) (hM : 0 < (M : ℝ))
    (hbase : (H : ℝ) * ((1000 : ℝ) * ((m : ℝ) + 1)) ≤ γ * (M : ℝ)) :
    a * γ ^ (2 ^ m - 1) * (H : ℝ) ≤ T * (M : ℝ) / 2 := by
  have hsub : (2 : ℕ) ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel (Nat.one_le_two_pow)
  have hD2 : (1000 : ℝ) ^ (2 ^ m) = (1000 : ℝ) ^ (2 ^ m - 1) * 1000 := by
    have := pow_succ (1000 : ℝ) (2 ^ m - 1)
    rwa [hsub] at this
  have hN1 : γ ^ (2 ^ m) = γ ^ (2 ^ m - 1) * γ := by
    have := pow_succ γ (2 ^ m - 1)
    rwa [hsub] at this
  rw [ha, hTdef, hD2, hN1]
  have h1 : (0 : ℝ) < (1000 : ℝ) ^ (2 ^ m - 1) := by positivity
  have h2 : (0 : ℝ) < γ ^ (2 ^ m - 1) := by positivity
  field_simp
  nlinarith [hbase, hH, hM, hγ]


end

end Work.Peluse.PET
