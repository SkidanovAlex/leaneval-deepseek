import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

namespace Work.WilkiesH.Interp.V2Q

open Work.WilkiesH.Interp

/-- Auxiliary estimate: for `1 ≤ l` and `1 ≤ K`, the ceiling of
`exp (b · log K / l)` is at most `K ^ b`. -/
private lemma ceil_exp_log_div_le (b K l : ℕ) (hl : 1 ≤ l) (hK : 1 ≤ K) :
    Nat.ceil (Real.exp ((b : ℝ) * Real.log (K : ℝ) / (l : ℝ))) ≤ K ^ b := by
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := lt_of_lt_of_le zero_lt_one hlR
  have hnum : 0 ≤ (b : ℝ) * Real.log (K : ℝ) := mul_nonneg hb hlogK
  have hle : (b : ℝ) * Real.log (K : ℝ) / (l : ℝ) ≤ (b : ℝ) * Real.log (K : ℝ) := by
    rw [div_le_iff₀ hlpos]
    nlinarith [hnum, hlR]
  calc Real.exp ((b : ℝ) * Real.log (K : ℝ) / (l : ℝ))
      ≤ Real.exp ((b : ℝ) * Real.log (K : ℝ)) := Real.exp_le_exp.mpr hle
    _ = (K : ℝ) ^ b := by rw [Real.exp_nat_mul, Real.exp_log hKpos]

theorem log_QV_le (μ g H : ℕ) (hlam : 1 ≤ Work.WilkiesH.Interp.lamV μ g H) :
    Real.log ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ) ≤
      Real.log 16 + Real.log ((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) +
        ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) *
          Real.log ((Work.WilkiesH.Interp.KK μ : ℕ) : ℝ) := by
  have hK : 1 ≤ KK μ := le_of_lt (one_lt_KK μ)
  have hceil :
      Nat.ceil (Real.exp ((bV μ g H : ℝ) * Real.log ((KK μ : ℝ)) / ((lamV μ g H : ℕ) : ℝ)))
        ≤ (KK μ) ^ (bV μ g H) :=
    ceil_exp_log_div_le (bV μ g H) (KK μ) (lamV μ g H) hlam hK
  have hN1 : 1 ≤ N1V μ g H := one_le_N1V μ g H
  have hKb : 1 ≤ (KK μ) ^ (bV μ g H) := Nat.one_le_pow _ _ (KK_pos μ)
  have hQVN : QV μ g H ≤ 8 * N1V μ g H * (KK μ) ^ (bV μ g H) := by
    rw [QV]
    have h1 : 4 * N1V μ g H *
          Nat.ceil (Real.exp ((bV μ g H : ℝ) * Real.log ((KK μ : ℝ)) / ((lamV μ g H : ℕ) : ℝ)))
        ≤ 4 * N1V μ g H * (KK μ) ^ (bV μ g H) := Nat.mul_le_mul_left _ hceil
    have h2 : 2 ≤ 4 * N1V μ g H * (KK μ) ^ (bV μ g H) :=
      le_trans (by norm_num) (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 4) hN1) hKb)
    calc 4 * N1V μ g H *
            Nat.ceil (Real.exp ((bV μ g H : ℝ) * Real.log ((KK μ : ℝ)) / ((lamV μ g H : ℕ) : ℝ)))
            + 2
        ≤ 4 * N1V μ g H * (KK μ) ^ (bV μ g H) + 4 * N1V μ g H * (KK μ) ^ (bV μ g H) :=
          add_le_add h1 h2
      _ = 8 * N1V μ g H * (KK μ) ^ (bV μ g H) := by ring
  have hQVcast : ((QV μ g H : ℕ) : ℝ) ≤ ((8 * N1V μ g H * (KK μ) ^ (bV μ g H) : ℕ) : ℝ) := by
    exact_mod_cast hQVN
  have hQpos : (0 : ℝ) < ((QV μ g H : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H))
  have hN1pos : (0 : ℝ) < ((N1V μ g H : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H))
  have hKpos : (0 : ℝ) < ((KK μ : ℕ) : ℝ) := Nat.cast_pos.mpr (KK_pos μ)
  have hlog : ((8 * N1V μ g H * (KK μ) ^ (bV μ g H) : ℕ) : ℝ)
      = 8 * (N1V μ g H : ℝ) * ((KK μ : ℝ)) ^ (bV μ g H) := by
    push_cast
    ring
  calc Real.log ((QV μ g H : ℕ) : ℝ)
      ≤ Real.log (((8 * N1V μ g H * (KK μ) ^ (bV μ g H) : ℕ)) : ℝ) :=
        Real.log_le_log hQpos hQVcast
    _ = Real.log 8 + Real.log ((N1V μ g H : ℕ) : ℝ) +
          ((bV μ g H : ℕ) : ℝ) * Real.log ((KK μ : ℕ) : ℝ) := by
        rw [hlog,
          Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hN1pos))
            (pow_ne_zero _ (ne_of_gt hKpos)),
          Real.log_mul (by norm_num) (ne_of_gt hN1pos), Real.log_pow]
    _ ≤ Real.log 16 + Real.log ((N1V μ g H : ℕ) : ℝ) +
          ((bV μ g H : ℕ) : ℝ) * Real.log ((KK μ : ℕ) : ℝ) := by
        have h8 : Real.log 8 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
        exact add_le_add (add_le_add h8 le_rfl) le_rfl

end Work.WilkiesH.Interp.V2Q
