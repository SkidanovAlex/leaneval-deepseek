import Mathlib

namespace Work.GM.S2

/-- For fixed positive `c` and positive exponent `β`, the quantity `c * N ^ (-β)`
eventually drops below `1` as `N → ∞` through the naturals. -/
theorem exists_nat_rpow_neg_mul_le (c : ℝ) (hc : 0 < c) (β : ℝ) (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c * (N : ℝ) ^ (-β) ≤ 1 := by
  have hlim : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-β)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ (-β) < 1 / c :=
    (tendsto_order.1 hlim).2 (1 / c) (by positivity)
  rw [Filter.eventually_atTop] at h1
  obtain ⟨N₀, hN₀⟩ := h1
  refine ⟨N₀, fun N hN => ?_⟩
  have hc1 : c * (1 / c) = 1 := by field_simp
  have hlt : c * (N : ℝ) ^ (-β) < c * (1 / c) :=
    mul_lt_mul_of_pos_left (hN₀ N hN) hc
  rw [hc1] at hlt
  exact le_of_lt hlt

end Work.GM.S2
