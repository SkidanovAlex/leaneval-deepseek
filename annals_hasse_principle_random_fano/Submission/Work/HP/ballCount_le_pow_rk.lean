import Mathlib
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.lam_basic

/-!
# `Work.HP.ballCount_le_pow_rk`

A crude but completely uniform lattice point bound: there is a constant `K = K(ι) > 0`
such that for every `ℤ`-sublattice `L ⊆ ℤ^ι` and every `T ≥ 0`

`#(L ∩ B(T)) ≤ K · (T + 1)^{rk L}`.

## Proof

For `T ≥ 1` this follows from Schmidt's bound (`Work.HP.Sig2.schmidt_bound`)

`#(L ∩ B(T)) ≤ K₀ · ∏_{i < rk L} (T/λ_i(L) + 1)`,

together with `λ_i(L) ≥ 1` for `1 ≤ i ≤ rk L` (every nonzero integral vector has norm `≥ 1`,
`Work.HP.MDEstimates.one_le_lam`), which gives `T/λ_i + 1 ≤ T + 1` and hence a bound by
`(T + 1)^{rk L}`.

For `T < 1` the only lattice point of norm `≤ T` is the origin
(`Work.HP.one_le_eNorm`: a nonzero integral vector has norm `≥ 1`), so the count is `1`,
and `1 ≤ (T + 1)^{rk L}` because `T + 1 ≥ 1`.

The constant is taken to be `K₀ + 1` so that both regimes are covered without any information
about the size of `K₀`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open Finset

theorem ballCount_le_pow_rk {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 0 ≤ T →
      (ballCount L T : ℝ) ≤ K * (T + 1) ^ (rk L) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := Sig2.schmidt_bound (ι := ι)
  refine ⟨K + 1, by linarith, ?_⟩
  intro L T hT
  rcases lt_or_ge T 1 with hT1 | hT1
  · -- `T < 1`: the only lattice point of norm `≤ T` is `0`.
    have hset : {v : ι → ℤ | v ∈ L ∧ eNorm v ≤ T} = {0} := by
      ext v
      constructor
      · rintro ⟨hvL, hvT⟩
        by_contra hv
        have h1 : 1 ≤ eNorm v := one_le_eNorm hv
        linarith
      · rintro rfl
        exact ⟨L.zero_mem, by simp [eNorm, hT]⟩
    have hbc : ballCount L T = 1 := by
      rw [ballCount, hset, Set.ncard_singleton]
    rw [hbc]
    have hpow : (1 : ℝ) ≤ (T + 1) ^ (rk L) := one_le_pow₀ (by linarith)
    have hK1 : (1 : ℝ) ≤ K + 1 := by linarith
    have hcast : (((1 : ℕ) : ℝ)) = 1 := by norm_num
    rw [hcast]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (K + 1) * (T + 1) ^ (rk L) :=
          mul_le_mul hK1 hpow (by norm_num) (by linarith)
  · -- `T ≥ 1`: Schmidt's bound plus `λ_i ≥ 1`.
    have hb := hK L T hT1
    have hprod : ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) ≤ (T + 1) ^ (rk L) := by
      have hterm : ∀ i ∈ Finset.range (rk L), T / lam L (i + 1) + 1 ≤ T + 1 := by
        intro i hi
        have hi1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
        have hir : i + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hlam1 : 1 ≤ lam L (i + 1) := MDEstimates.one_le_lam L hi1 hir
        have hquot : T / lam L (i + 1) ≤ T := by
          have h := div_le_div_of_nonneg_left hT zero_lt_one hlam1
          simpa using h
        linarith
      have hnonneg : ∀ i ∈ Finset.range (rk L), (0 : ℝ) ≤ T / lam L (i + 1) + 1 := by
        intro i hi
        have hi1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
        have hir : i + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hlam1 : 1 ≤ lam L (i + 1) := MDEstimates.one_le_lam L hi1 hir
        have hpos : 0 < lam L (i + 1) := lt_of_lt_of_le zero_lt_one hlam1
        have : 0 ≤ T / lam L (i + 1) := div_nonneg hT hpos.le
        linarith
      calc ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)
          ≤ ∏ _i ∈ Finset.range (rk L), (T + 1) := Finset.prod_le_prod₀ hnonneg hterm
        _ = (T + 1) ^ (rk L) := by rw [Finset.prod_const, Finset.card_range]
    calc (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := hb
      _ ≤ K * (T + 1) ^ (rk L) := mul_le_mul_of_nonneg_left hprod hKpos.le
      _ ≤ (K + 1) * (T + 1) ^ (rk L) :=
          mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (pow_nonneg (by linarith) _)

end Work.HP
