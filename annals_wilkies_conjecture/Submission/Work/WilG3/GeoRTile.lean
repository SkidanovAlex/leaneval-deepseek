import Mathlib
import Submission.Work.WilG3.Defs

open Classical

namespace Work.WilG3

/-- Monotonicity of the right-chart tile endpoints: `1 - ρ^k/2` is nondecreasing in `k`.
This is the statement that the tiles `[1 - ρ^k/2, 1 - ρ^(k+1)/2]` are ordered and
contiguous, and reduces to `ρ^(k+1) ≤ ρ^k`, i.e. `0 ≤ ρ ≤ 1`. -/
theorem geoRTile_endpoint_mono (r k : ℕ) :
    1 - geoRho r ^ k / 2 ≤ 1 - geoRho r ^ (k + 1) / 2 := by
  have hρ0 : 0 ≤ geoRho r := geoRho_nonneg r
  have hρ1 : geoRho r ≤ 1 := geoRho_le_one r
  have h : geoRho r ^ (k + 1) ≤ geoRho r ^ k := by
    calc geoRho r ^ (k + 1) = geoRho r ^ k * geoRho r := pow_succ (geoRho r) k
      _ ≤ geoRho r ^ k * 1 := mul_le_mul_of_nonneg_left hρ1 (pow_nonneg hρ0 k)
      _ = geoRho r ^ k := mul_one _
  linarith

theorem GeoRTile (r K : ℕ) (hK : 1 ≤ K) (x : ℝ)
    (hlo : 1 / 2 ≤ x) (hhi : x ≤ 1 - geoRho r ^ K / 2) :
    ∃ k < K, 1 - geoRho r ^ k / 2 ≤ x ∧ x ≤ 1 - geoRho r ^ (k + 1) / 2 := by
  classical
  -- The tiles `[1 - ρ^k/2, 1 - ρ^(k+1)/2]` for `k < K` are ordered and contiguous; the
  -- first begins at `1/2` and the last ends at `1 - ρ^K/2`.  Take the last tile whose left
  -- endpoint is below `x`.
  let S : Finset ℕ := (Finset.range K).filter fun k => 1 - geoRho r ^ k / 2 ≤ x
  have h0mem : 0 ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp only [pow_zero]
    linarith
  have hne : S.Nonempty := ⟨0, h0mem⟩
  set k : ℕ := S.max' hne with hk
  have hkS : k ∈ S := by
    rw [hk]
    exact Finset.max'_mem S hne
  have hkK : k < K := Finset.mem_range.mp (Finset.mem_filter.mp hkS).1
  have hkx : 1 - geoRho r ^ k / 2 ≤ x := (Finset.mem_filter.mp hkS).2
  refine ⟨k, hkK, hkx, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  rcases lt_or_ge (k + 1) K with h | h
  · -- then the tile `k+1` would also qualify, contradicting maximality of `k`
    have hmem : k + 1 ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, le_of_lt hcon⟩
    have hle : k + 1 ≤ k := by
      have := Finset.le_max' S (k + 1) hmem
      rwa [← hk] at this
    omega
  · -- otherwise `k + 1 = K` and `x ≤ 1 - ρ^K/2` is contradicted
    have hEq : k + 1 = K := by omega
    rw [hEq] at hcon
    linarith

end Work.WilG3
