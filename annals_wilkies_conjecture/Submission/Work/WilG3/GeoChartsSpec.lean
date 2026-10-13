import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

-- Geometric half of `WilkieDesign.CG.G3_affine_cover` for the concrete chart family of
-- `Submission/Work/WilG3/Defs.lean` (re-read the definitions there: every pair `p` in
-- `geoCharts r K` is stored as `(lower endpoint, upper endpoint)`).  Every chart is a
-- nondegenerate interval inside `(0,1)` whose length times `(r+1)` is at most its distance to the
-- boundary of `(0,1)`.  For a left chart `p = (ρ^(k+1)/2, ρ^k/2)` the inequality reads
-- `(r+1)·ρ^k(1-ρ)/2 ≤ ρ^(k+1)/2`, which is an equality because `(1-ρ)(r+1) = (r+1)/(r+2) = ρ`
-- (`sub_geoRho_mul`), and `min p.1 (1 - p.2) = p.1` because `ρ^(k+1)/2 ≤ 1 - ρ^k/2` follows from
-- `geoRho_pow_add_mul_le`; the right charts are the mirror image under `x ↦ 1 - x`.

/-! ### Basic facts about the ratio -/

/-- `(1 - ρ)(r+1) = ρ`, i.e. the chart of scale `k` has length exactly `ρ^k (1-ρ)/2`. -/
theorem sub_geoRho_mul_eq (r : ℕ) : (1 - geoRho r) * ((r : ℝ) + 1) = geoRho r := by
  have h : ((r : ℝ) + 2) ≠ 0 := by positivity
  rw [sub_geoRho_mul, geoRho]
  field_simp
  ring

/-- The powers of `ρ` strictly decrease: `ρ^(k+1) < ρ^k`, since `0 < ρ < 1`. -/
theorem geoRho_pow_succ_lt (r k : ℕ) : geoRho r ^ (k + 1) < geoRho r ^ k := by
  rw [pow_succ]
  calc geoRho r ^ k * geoRho r < geoRho r ^ k * 1 :=
        mul_lt_mul_of_pos_left (geoRho_lt_one r) (geoRho_pow_pos r k)
    _ = geoRho r ^ k := mul_one _

/-- `ρ^(k+1)/2 ≤ 1 - ρ^k/2`, equivalently `ρ^k(1+ρ) ≤ 2`. -/
theorem geoRho_succ_half_le (r k : ℕ) :
    geoRho r ^ (k + 1) / 2 ≤ 1 - geoRho r ^ k / 2 := by
  have h := geoRho_pow_add_mul_le r k
  have h3 : geoRho r ^ (k + 1) + geoRho r ^ k = geoRho r ^ k * (1 + geoRho r) := by
    rw [pow_succ]; ring
  linarith

/-- Length identity: the length of the `k`-th chart, times `(r+1)`, is exactly `ρ^(k+1)/2`. -/
theorem geoRho_len (r k : ℕ) :
    (geoRho r ^ k / 2 - geoRho r ^ (k + 1) / 2) * ((r : ℝ) + 1)
      = geoRho r ^ (k + 1) / 2 := by
  have hpow : geoRho r ^ k * (1 - geoRho r) * ((r : ℝ) + 1) = geoRho r ^ (k + 1) := by
    rw [mul_assoc, sub_geoRho_mul_eq, pow_succ]
  have h0 : geoRho r ^ k / 2 - geoRho r ^ (k + 1) / 2
      = geoRho r ^ k * (1 - geoRho r) / 2 := by
    rw [pow_succ]; ring
  rw [h0]
  rw [show geoRho r ^ k * (1 - geoRho r) / 2 * ((r : ℝ) + 1)
        = geoRho r ^ k * (1 - geoRho r) * ((r : ℝ) + 1) / 2 by ring]
  rw [hpow]

theorem GeoChartsSpec (r K : ℕ) : ∀ p ∈ geoCharts r K,
    0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * ((r : ℝ) + 1) ≤ min p.1 (1 - p.2) := by
  intro p hp
  rw [mem_geoCharts] at hp
  rcases hp with hp | hp
  · -- left chart `p = (ρ^(k+1)/2, ρ^k/2)`
    rw [mem_geoL] at hp
    rcases hp with ⟨k, -, hp⟩
    obtain rfl : p = (geoRho r ^ (k + 1) / 2, geoRho r ^ k / 2) := hp.symm
    refine ⟨div_pos (geoRho_pow_pos r (k + 1)) two_pos, ?_, ?_, ?_⟩
    · exact div_lt_div_of_pos_right (geoRho_pow_succ_lt r k) two_pos
    · rw [div_lt_one two_pos]
      linarith [geoRho_pow_le_one r k]
    · rw [geoRho_len, min_eq_left (geoRho_succ_half_le r k)]
  · -- right chart `p = (1 - ρ^k/2, 1 - ρ^(k+1)/2)`
    rw [mem_geoR] at hp
    rcases hp with ⟨k, -, hp⟩
    obtain rfl : p = (1 - geoRho r ^ k / 2, 1 - geoRho r ^ (k + 1) / 2) := hp.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [geoRho_pow_le_one r k]
    · linarith [geoRho_pow_succ_lt r k]
    · linarith [geoRho_pow_pos r (k + 1)]
    · rw [show (1 - geoRho r ^ (k + 1) / 2) - (1 - geoRho r ^ k / 2)
            = geoRho r ^ k / 2 - geoRho r ^ (k + 1) / 2 by ring]
      rw [show 1 - (1 - geoRho r ^ (k + 1) / 2) = geoRho r ^ (k + 1) / 2 by ring]
      rw [geoRho_len, min_eq_right (geoRho_succ_half_le r k)]

end Work.WilG3
