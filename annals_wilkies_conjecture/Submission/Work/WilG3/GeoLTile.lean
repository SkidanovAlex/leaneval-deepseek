import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

/-- Left half of the geometric interval cover: every `x ∈ [ρ^K/2, 1/2]` lies in one of the
charts `[ρ^(k+1)/2, ρ^k/2]` for `k < K`. -/
theorem GeoLTile (r K : ℕ) (hK : 1 ≤ K) (x : ℝ)
    (hlo : geoRho r ^ K / 2 ≤ x) (hhi : x ≤ 1 / 2) :
    ∃ k < K, geoRho r ^ (k + 1) / 2 ≤ x ∧ x ≤ geoRho r ^ k / 2 := by
  classical
  -- Take the least scale `k0` for which the upper endpoint `ρ^k0 / 2` has dropped below `x`.
  have hex : ∃ k, geoRho r ^ k / 2 ≤ x := ⟨K, hlo⟩
  have hspec : geoRho r ^ (Nat.find hex) / 2 ≤ x := Nat.find_spec hex
  have hle : Nat.find hex ≤ K := Nat.find_min' hex hlo
  have hmin : ∀ m < Nat.find hex, ¬ (geoRho r ^ m / 2 ≤ x) :=
    fun m hm => Nat.find_min hex hm
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · -- `k0 = 0`: the very first chart contains `x`, and necessarily `x = 1/2`.
    refine ⟨0, hK, ?_, hhi⟩
    rw [h0] at hspec
    have h1 : geoRho r ^ (0 + 1) / 2 ≤ (1 : ℝ) / 2 := by
      have := pow_le_pow_of_le_one (geoRho_nonneg r) (geoRho_le_one r) (Nat.zero_le 1)
      linarith
    linarith
  · -- `k0 = m + 1`: the chart of scale `m` contains `x`.
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    refine ⟨m, ?_, ?_, ?_⟩
    · omega
    · rw [hm] at hspec; exact hspec
    · have hlt : m < Nat.find hex := by omega
      have := hmin m hlt
      linarith [not_le.mp this]

end Work.WilG3
