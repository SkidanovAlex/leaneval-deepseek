/-
# Shared helpers for the proof of *FI* Theorem 2ψ (26.2)

Small lemmas used by the assembly (`Submission/Work/FIArea7/theorem2psi.lean`):

* `t2psi_norm_grossenChar` — the Grössencharacter of a character with `‖χ‖ ≤ 1` is bounded by `1`;
* `t2psi_log_rpow_le` — a polylogarithm is dominated by any positive power;
* `t2psi_absorb` — consequently `K N^α (log N)^B ≤ C N^β` for `α < β`.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The Grössencharacter is bounded by `1`.**  If `‖χ z‖ ≤ 1` for all `z` then
`‖ψ(z)‖ = ‖χ(z)‖·‖(z/|z|)^k‖ ≤ 1`, because `z/|z|` is either `0` or on the unit circle. -/
theorem t2psi_norm_grossenChar (chi : GaussianInt → ℂ) (hchi : ∀ z, ‖chi z‖ ≤ 1) (k : ℤ)
    (z : GaussianInt) : ‖grossenChar chi k z‖ ≤ 1 := by
  rw [grossenChar, norm_mul]
  refine mul_le_one₀ (hchi z) (norm_nonneg _) ?_
  set w : ℂ := z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ) with hw
  have hwnorm : ‖w‖ = ‖z.toComplex‖ / ‖z.toComplex‖ := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hcases : ‖w‖ = 0 ∨ ‖w‖ = 1 := by
    rcases eq_or_ne ‖z.toComplex‖ 0 with h | h
    · left; rw [hwnorm, h, div_zero]
    · right; rw [hwnorm, div_self h]
  have hpow : ‖w‖ ^ k ≤ 1 := by
    rcases hcases with h | h
    · rcases eq_or_ne k 0 with hk | hk
      · subst hk; simp
      · rw [h, zero_zpow _ hk]; norm_num
    · rw [h]; simp
  rw [norm_zpow]
  exact hpow

/-- For `B ≥ 0` and `δ > 0`, `(log x)^B ≪ x^δ` for `x ≥ 1`. -/
theorem t2psi_log_rpow_le (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ B ≤ K * x ^ δ := by
  refine ⟨max 1 ((B / δ) ^ B), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · rw [← hB0, Real.rpow_zero]
    have hxδ : (1:ℝ) ≤ x ^ δ := Real.one_le_rpow hx (le_of_lt hδ)
    have hK : (1:ℝ) ≤ max 1 ((0/δ) ^ (0:ℝ)) := le_max_left _ _
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ max 1 ((0/δ) ^ (0:ℝ)) * x ^ δ := mul_le_mul hK hxδ zero_le_one (le_trans zero_le_one hK)
  · have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hstep : Real.log x ≤ x ^ (δ / B) / (δ / B) :=
      Real.log_le_rpow_div (le_of_lt hx0) (div_pos hδ hBpos)
    have hdiv : x ^ (δ / B) / (δ / B) = (B / δ) * x ^ (δ / B) := by field_simp
    rw [hdiv] at hstep
    have h2 : Real.log x ^ B ≤ ((B / δ) * x ^ (δ / B)) ^ B := Real.rpow_le_rpow hlogx hstep hB
    have hsplit : ((B / δ) * x ^ (δ / B)) ^ B = (B / δ) ^ B * x ^ δ := by
      rw [Real.mul_rpow (le_of_lt (div_pos hBpos hδ)) (le_of_lt (Real.rpow_pos_of_pos hx0 _))]
      congr 1
      rw [← Real.rpow_mul (le_of_lt hx0)]
      congr 1
      field_simp
    rw [hsplit] at h2
    exact le_trans h2
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Real.rpow_pos_of_pos hx0 _)))

/-- **Absorption of polylogarithms.**  For `α < β` the bound `K N^α (log(N+2))^B` is dominated
by `C N^β`. -/
theorem t2psi_absorb (K B α β : ℝ) (hK : 0 < K) (hB : 0 ≤ B) (hαβ : α < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      K * (N : ℝ) ^ α * Real.log ((N : ℝ) + 2) ^ B ≤ C * (N : ℝ) ^ β := by
  obtain ⟨K1, hK1pos, hK1⟩ := t2psi_log_rpow_le B (β - α) hB (by linarith)
  refine ⟨K * K1 * 3 ^ (β - α), by positivity, fun N hN => ?_⟩
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
  have hlog : Real.log ((N:ℝ)+2) ^ B ≤ K1 * (((N:ℝ)+2) ^ (β - α)) := hK1 _ (by linarith)
  have hlog2 : Real.log ((N:ℝ)+2) ^ B ≤ K1 * (3 ^ (β - α) * (N:ℝ) ^ (β - α)) := by
    refine le_trans hlog (mul_le_mul_of_nonneg_left ?_ (le_of_lt hK1pos))
    calc ((N:ℝ)+2) ^ (β - α) ≤ (3 * (N:ℝ)) ^ (β - α) := by
          apply Real.rpow_le_rpow (by linarith) ?_ (by linarith)
          linarith
      _ = 3 ^ (β - α) * (N:ℝ) ^ (β - α) := Real.mul_rpow (by norm_num) (le_of_lt hNpos)
  calc K * (N:ℝ) ^ α * Real.log ((N:ℝ)+2) ^ B
      ≤ K * (N:ℝ) ^ α * (K1 * (3 ^ (β - α) * (N:ℝ) ^ (β - α))) :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = K * K1 * 3 ^ (β - α) * (N:ℝ) ^ β := by
        have h : (N:ℝ) ^ α * (N:ℝ) ^ (β - α) = (N:ℝ) ^ β := by
          rw [← Real.rpow_add hNpos]; ring_nf
        calc K * (N:ℝ) ^ α * (K1 * (3 ^ (β - α) * (N:ℝ) ^ (β - α)))
            = (K * K1 * 3 ^ (β - α)) * ((N:ℝ) ^ α * (N:ℝ) ^ (β - α)) := by ring
          _ = (K * K1 * 3 ^ (β - α)) * (N:ℝ) ^ β := by rw [h]

end

end Work.FIArea7
