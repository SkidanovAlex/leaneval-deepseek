import Mathlib
import Submission.Work.GM.S3.gen_defs

namespace Work.GM.S3.Gen

/-- The truncation level `Klev N δ = (M N)^{1+δ}/N` is strictly below `2^{cellJ N δ - 1}`.

Since `M N = N^{6/5}`, one has `Klev N δ = N^{(1+6δ)/5}` for `N ≥ 1`; more generally
`Klev N δ ≤ N^{(1+6δ)/5}`, and `N < 2^{Nat.log 2 N + 1}`, so

`Klev N δ ≤ N^{(1+6δ)/5} < 2^{(Nat.log 2 N + 1)·(1+6δ)/5} ≤ 2^{8⌈δ⌉(Nat.log 2 N + 1) + 255}`,

using `(1+6δ)/5 ≤ 8⌈δ⌉` (from `⌈δ⌉ ≥ δ` and `⌈δ⌉ ≥ 1`). The exponent
`8⌈δ⌉(Nat.log 2 N + 1) + 255` is exactly `cellJ N δ - 1`. -/
lemma Klev_lt_pow_two (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Work.GM.S3.Gen.Klev N δ < (2 : ℝ) ^ (Work.GM.S3.Gen.cellJ N δ - 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hk : Klev 0 δ = 0 := by simp [Klev]
    rw [hk]
    exact pow_pos (by norm_num) _
  · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have ha : (0 : ℝ) < (1 + 6 * δ) / 5 := by linarith
    have hC : Klev N δ = (N : ℝ) ^ ((1 + 6 * δ) / 5) := by
      rw [Klev, Submission.LargeValues.M]
      rw [← Real.rpow_mul (le_of_lt hNR) (6 / 5) (1 + δ)]
      have hsub : (N : ℝ) ^ ((6 / 5) * (1 + δ) - 1) = (N : ℝ) ^ ((6 / 5) * (1 + δ)) / (N : ℝ) := by
        have := Real.rpow_sub hNR ((6 / 5) * (1 + δ)) 1
        rwa [Real.rpow_one] at this
      rw [← hsub]
      congr 1
      ring
    rw [hC]
    have hNlt : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
      rw [Nat.succ_eq_add_one] at h
      exact_mod_cast h
    have hstep : (N : ℝ) ^ ((1 + 6 * δ) / 5)
        < (2 : ℝ) ^ (((Nat.log 2 N + 1 : ℕ) : ℝ) * ((1 + 6 * δ) / 5)) := by
      have := Real.rpow_lt_rpow (le_of_lt hNR) hNlt ha
      rwa [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) (Nat.log 2 N + 1)
        ((1 + 6 * δ) / 5)] at this
    have hexp : ((Nat.log 2 N + 1 : ℕ) : ℝ) * ((1 + 6 * δ) / 5)
        ≤ ((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 : ℕ) : ℝ) := by
      have hcast : ((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 : ℕ) : ℝ)
          = 8 * (Nat.ceil δ : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) + 255 := by
        push_cast; ring
      rw [hcast]
      have ha8c : ((1 + 6 * δ) / 5) ≤ 8 * (Nat.ceil δ : ℝ) := by
        have hcδ : δ ≤ (Nat.ceil δ : ℝ) := Nat.le_ceil δ
        have hc1 : (1 : ℝ) ≤ (Nat.ceil δ : ℝ) := by
          have := Nat.one_le_ceil_iff.mpr hδ
          exact_mod_cast this
        nlinarith [hcδ, hc1]
      have hK0 : (0 : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ha8c hK0, hK0]
    have hstep2 : (2 : ℝ) ^ (((Nat.log 2 N + 1 : ℕ) : ℝ) * ((1 + 6 * δ) / 5))
        ≤ (2 : ℝ) ^ (((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hconv : (2 : ℝ) ^ (((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 : ℕ) : ℝ))
        = (2 : ℝ) ^ (cellJ N δ - 1) := by
      have hcell : cellJ N δ - 1 = 8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 := by
        rw [cellJ]; omega
      rw [hcell]
      exact Real.rpow_natCast 2 _
    calc (N : ℝ) ^ ((1 + 6 * δ) / 5)
          < (2 : ℝ) ^ (((Nat.log 2 N + 1 : ℕ) : ℝ) * ((1 + 6 * δ) / 5)) := hstep
      _ ≤ (2 : ℝ) ^ (((8 * Nat.ceil δ * (Nat.log 2 N + 1) + 255 : ℕ) : ℝ)) := hstep2
      _ = (2 : ℝ) ^ (cellJ N δ - 1) := hconv

theorem exists_level (N : ℕ) (δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht1 : 1 ≤ t)
    (htK : t ≤ Work.GM.S3.Gen.Klev N δ) :
    ∃ j : ℕ, j < Work.GM.S3.Gen.cellJ N δ ∧ Work.GM.S3.Gen.Mdy N δ j < t ∧
      t ≤ 2 * Work.GM.S3.Gen.Mdy N δ j := by
  have hKlev_lt := Klev_lt_pow_two N δ hδ
  -- `t` is never below `Klev/1 = Klev`, so level `0` is not the one we look for
  have hp0 : ¬ (Klev N δ < t * 2 ^ 0) := by
    simpa using (not_lt.mpr htK : ¬ (Klev N δ < t))
  -- ... but there is *some* level: `Klev < 2^{cellJ-1} ≤ t · 2^{cellJ}`
  have hpex : ∃ j, Klev N δ < t * 2 ^ j := by
    refine ⟨cellJ N δ, ?_⟩
    have h1 : (2 : ℝ) ^ (cellJ N δ - 1) ≤ t * 2 ^ (cellJ N δ) := by
      have hle1 : (2 : ℝ) ^ (cellJ N δ - 1) ≤ (2 : ℝ) ^ (cellJ N δ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _)
      have hle2 : (2 : ℝ) ^ (cellJ N δ) ≤ t * 2 ^ (cellJ N δ) :=
        le_mul_of_one_le_left (by positivity) ht1
      linarith
    linarith
  set j := Nat.find hpex with hj
  -- `j` is the least such level, hence `j ≥ 1` and `j - 1` is not such a level
  have hPj : Klev N δ < t * 2 ^ j := by rw [hj]; exact Nat.find_spec hpex
  have hj1 : 1 ≤ j := by
    have h0 : 0 < Nat.find hpex := (Nat.find_pos hpex).mpr hp0
    omega
  have hPm : ¬ (Klev N δ < t * 2 ^ (j - 1)) := by
    have hlt : j - 1 < Nat.find hpex := by omega
    exact Nat.find_min hpex hlt
  have hle : t * 2 ^ (j - 1) ≤ Klev N δ := le_of_not_gt hPm
  -- the dyadic bound `Klev < 2^{cellJ-1}` then forces `j < cellJ`
  have h2mle : (2 : ℝ) ^ (j - 1) ≤ Klev N δ := by
    have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ 2 ^ (j - 1)) ht1
    linarith
  have hpow_lt : (2 : ℝ) ^ (j - 1) < (2 : ℝ) ^ (cellJ N δ - 1) :=
    lt_of_le_of_lt h2mle hKlev_lt
  have hjn : j - 1 < cellJ N δ - 1 := by
    have hnat : (2 ^ (j - 1) : ℕ) < (2 ^ (cellJ N δ - 1) : ℕ) := by exact_mod_cast hpow_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hnat
  have hjcell : j < cellJ N δ := by
    have hc : 1 ≤ cellJ N δ := by rw [cellJ]; omega
    have h1 : j - 1 + 1 < cellJ N δ - 1 + 1 := Nat.add_lt_add_right hjn 1
    rwa [Nat.sub_add_cancel hj1, Nat.sub_add_cancel hc] at h1
  refine ⟨j, hjcell, ?_, ?_⟩
  · -- `Mdy j < t`
    show Klev N δ / 2 ^ j < t
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)]
    exact hPj
  · -- `t ≤ 2 * Mdy j`, i.e. `t ≤ Klev/2^{j-1}`
    show t ≤ 2 * (Klev N δ / 2 ^ j)
    have h2j : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      have h' : (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 1) + 1) := by rw [Nat.sub_add_cancel hj1]
      rw [h', pow_succ']
    rw [h2j]
    rw [show 2 * (Klev N δ / (2 * 2 ^ (j - 1))) = Klev N δ / 2 ^ (j - 1) by
      rw [← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (j - 1))]
    exact hle

end Work.GM.S3.Gen
