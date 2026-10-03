import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTPlan.A6Clean

/-- The Farey/Platt bookkeeping lemma: if `2^k · q · 8 ≤ N` (the Farey-denominator bound) and
`k + 2U + 1 ≤ Log N` (the Platt/verification height), then the radius `2^{k - Log N}` is at most
`2^{-2U-1}` and `2^{k - Log N} · q ≤ 1/4`.

The two inequalities are exactly the two uses of the dyadic radius in the major-arc analysis:
the first is the height/radius comparison, the second is the Farey-denominator control
(`N < 2^{Log N + 1}` gives `N/(8·2^{Log N}) < 1/4`, and `q ≤ N/(8·2^k)`). -/
theorem bandRadius_le (k U N q : ℕ) (hN : 0 < N)
    (hfarey : (2 : ℝ) ^ k * (q : ℝ) * 8 ≤ (N : ℝ))
    (hplat : k + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ∧
      (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hlogcast : (Work.Analysis.EndVar.logN N : ℝ) = (Nat.log 2 (max N 2) : ℝ) := by
    simp [Work.Analysis.EndVar.logN]
  have htoNat : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := by
    simp [Work.Analysis.EndVar.logN, Int.toNat_natCast]
  have hlk : k + 2 * U + 1 ≤ Nat.log 2 (max N 2) := by
    rw [htoNat] at hplat
    exact hplat
  constructor
  · -- first conjunct: compare the exponents
    have hLz : ((-(2 * (U : ℤ)) - 1 : ℤ) : ℝ) = -2 * (U : ℝ) - 1 := by
      push_cast
      ring
    rw [hlogcast, ← Real.rpow_intCast (2 : ℝ) (-(2 * (U : ℤ)) - 1), hLz]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hexp : (k : ℝ) + 2 * (U : ℝ) + 1 ≤ (Nat.log 2 (max N 2) : ℝ) := by
      exact_mod_cast hlk
    linarith
  · -- second conjunct: the Farey bound
    set lr : ℝ := (Nat.log 2 (max N 2) : ℝ) with hlr
    have hden : (0 : ℝ) < (2 : ℝ) ^ lr := Real.rpow_pos_of_pos h2pos _
    have hrw : (2 : ℝ) ^ ((k : ℝ) - lr) = (2 : ℝ) ^ k / (2 : ℝ) ^ lr := by
      rw [Real.rpow_sub h2pos, Real.rpow_natCast]
    rw [hlogcast, hrw, div_mul_eq_mul_div]
    have hq : (2 : ℝ) ^ k * (q : ℝ) ≤ (N : ℝ) / 8 := by linarith [hfarey]
    have hquarter : ((N : ℝ) / 8) / (2 : ℝ) ^ lr < 1 / 4 := by
      -- `N < 2 * 2 ^ Log N`
      have hM : max N 2 < 2 ^ (Nat.log 2 (max N 2) + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
        rwa [Nat.succ_eq_add_one] at h
      have hNltNat : N < 2 ^ (Nat.log 2 (max N 2) + 1) :=
        lt_of_le_of_lt (Nat.le_max_left N 2) hM
      have hcast : ((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℝ) = 2 * (2 : ℝ) ^ lr := by
        push_cast
        rw [← Real.rpow_natCast]
        have hs : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) = lr + 1 := by
          push_cast
          rw [← hlr]
        rw [hs, Real.rpow_add h2pos, Real.rpow_one]
        ring
      have hNltR : (N : ℝ) < 2 * (2 : ℝ) ^ lr := by
        have h' : (N : ℝ) < ((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℝ) := by
          exact_mod_cast hNltNat
        rwa [hcast] at h'
      have hden2 : (0 : ℝ) < 8 * (2 : ℝ) ^ lr := mul_pos (by norm_num) hden
      rw [div_div, div_lt_iff₀ hden2]
      have hcoef : (1 : ℝ) / 4 * (8 * (2 : ℝ) ^ lr) = 2 * (2 : ℝ) ^ lr := by ring
      rw [hcoef]
      exact hNltR
    exact le_trans (div_le_div_of_nonneg_right hq (le_of_lt hden)) (le_of_lt hquarter)

end Work.KMTPlan.A6Clean
