import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

/-!
# `S₂`: the number of dyadic levels is `≤ N^{δ/4}` (GM §6, book-keeping)

GM's §6 works with the truncation point `N ≥ 1` and the "level" `k = ⌊log₂|t|⌋` of a
frequency `t ∈ W ⊆ [0, T]`, where `T = M N = N^{6/5}`.  Since `|t| ≤ T`, only
`⌊log₂(M N)⌋ + 1` dyadic levels occur, and this file records that for every `δ > 0`
and every sufficiently large `N` this count of levels is at most `N^{δ/4}` — so that the
`T^δ = (M N)^δ` losses accumulated over the levels may be absorbed into a *polynomial*
power of `N`.

The proof is the elementary comparison "log grows slower than any positive power":
`⌊2 M N⌋₊ ≤ 2 N^{6/5}`, hence `Nat.log 2 ⌊2 M N⌋₊ ≤ log (2 N^{6/5}) / log 2
= 1 + (6/5) log N / log 2`, and `log N ≤ N^{δ/8}/(δ/8)`.
-/

open Filter

namespace Work.GM.S2

/-- `Nat.log 2 A ≤ log x / log 2` whenever `(A : ℝ) ≤ x` and `1 ≤ x`.

Indeed `2 ^ Nat.log 2 A ≤ A ≤ x`, so taking logarithms gives the claim. -/
lemma nat_log_le_log_div {A : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hAx : (A : ℝ) ≤ x) :
    (Nat.log 2 A : ℝ) ≤ Real.log x / Real.log 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA
    simp only [Nat.log_zero_right, Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hx1) hlog2pos.le
  · have hpow : (2 : ℝ) ^ (Nat.log 2 A) ≤ (A : ℝ) := by
      have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hA)
      exact_mod_cast this
    have hle : (2 : ℝ) ^ (Nat.log 2 A) ≤ x := le_trans hpow hAx
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 A) := by positivity
    have h := Real.log_le_log h2pos hle
    rw [Real.log_pow] at h
    rw [le_div_iff₀ hlog2pos]
    linarith

/-- The number of dyadic levels below `2 * M N = 2 N^{6/5}` is eventually `≤ N^{δ/4}`. -/
theorem level_count_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (Nat.log 2 ⌊2 * Submission.LargeValues.M N⌋₊ + 1 : ℝ) ≤ (N : ℝ) ^ (δ / 4) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 48 / (5 * δ * Real.log 2) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hδ8 : (0 : ℝ) < δ / 8 := by linarith
  have hEv : ∀ᶠ N : ℕ in atTop, K + 3 ≤ (N : ℝ) ^ (δ / 8) :=
    (tendsto_rpow_atTop hδ8).comp tendsto_natCast_atTop_atTop
      |>.eventually_ge_atTop (K + 3)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hEv
  refine ⟨max N₁ 2, ?_⟩
  intro N hN
  have hN1le : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hs : K + 3 ≤ (N : ℝ) ^ (δ / 8) := hN₁ N hN1le
  have hM : Submission.LargeValues.M N = (N : ℝ) ^ (6 / 5 : ℝ) := rfl
  have hMpos : (0 : ℝ) < Submission.LargeValues.M N := by rw [hM]; positivity
  have hfloor : (⌊2 * Submission.LargeValues.M N⌋₊ : ℝ) ≤ 2 * Submission.LargeValues.M N :=
    Nat.floor_le (by linarith)
  have hx1 : (1 : ℝ) ≤ 2 * Submission.LargeValues.M N := by
    rw [hM]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    linarith
  have hlogbound : (Nat.log 2 ⌊2 * Submission.LargeValues.M N⌋₊ : ℝ)
      ≤ Real.log (2 * Submission.LargeValues.M N) / Real.log 2 :=
    nat_log_le_log_div hx1 hfloor
  have hlogexpand : Real.log (2 * Submission.LargeValues.M N)
      = Real.log 2 + (6 / 5) * Real.log (N : ℝ) := by
    rw [hM, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNpos]
  have hstep1 : (Nat.log 2 ⌊2 * Submission.LargeValues.M N⌋₊ + 1 : ℝ)
      ≤ 2 + (6 / 5) * Real.log (N : ℝ) / Real.log 2 := by
    have h1 := hlogbound
    rw [hlogexpand] at h1
    have h2 : (Real.log 2 + (6 / 5) * Real.log (N : ℝ)) / Real.log 2
        = 1 + (6 / 5) * Real.log (N : ℝ) / Real.log 2 := by
      rw [add_div, div_self hlog2pos.ne']
    linarith
  have hlogNbound : (6 / 5) * Real.log (N : ℝ) / Real.log 2
      ≤ K * (N : ℝ) ^ (δ / 8) := by
    have hlogN := Real.log_le_rpow_div hNpos.le hδ8
    have h8 : (N : ℝ) ^ (δ / 8) / (δ / 8) = 8 * (N : ℝ) ^ (δ / 8) / δ := by field_simp
    rw [hKdef]
    have hL : (6 / 5) * Real.log (N : ℝ) / Real.log 2
        ≤ (6 / 5) * (8 * (N : ℝ) ^ (δ / 8) / δ) / Real.log 2 := by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← h8]; exact hlogN
      · exact hlog2pos.le
    refine le_trans hL (le_of_eq ?_)
    field_simp
    ring
  have hsq : (N : ℝ) ^ (δ / 8) * (N : ℝ) ^ (δ / 8) = (N : ℝ) ^ (δ / 4) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hfinal : 2 + K * (N : ℝ) ^ (δ / 8) ≤ (N : ℝ) ^ (δ / 4) := by
    have hprod : 0 ≤ ((N : ℝ) ^ (δ / 8) - K) * ((N : ℝ) ^ (δ / 8) - 3) :=
      mul_nonneg (by linarith) (by linarith)
    rw [← hsq]
    nlinarith [hprod]
  linarith [hstep1, hlogNbound, hfinal]

end Work.GM.S2
