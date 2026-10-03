import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FITop4.Areas6

namespace Work.FIArea6

/-- The fixed exponent `ν = nuU = 3·sigmaChoice Asave + 4` is positive and `≥ 1`. -/
private lemma nuU_ge_one : (1 : ℝ) ≤ Work.FITop4.nuU := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- **The exponential beats the fifth power, with a deficit `c·t^{1/4}` in the exponent.**
For every `c > 0` there is `t₀ > 0` with `(t+2)^5 ≤ exp(√t − c·t^{1/4})` for all `t ≥ t₀`. -/
private lemma exp_growth (c : ℝ) (hc : 0 < c) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, t0 ≤ t →
      (t + 2) ^ (5 : ℕ) ≤ Real.exp (Real.sqrt t - c * t ^ ((1 : ℝ) / 4)) := by
  have hDpos : (0:ℝ) < (2:ℝ)^12 * (Nat.factorial 12 : ℝ) := by
    have h := Nat.factorial_pos 12; positivity
  refine ⟨max 1 (max ((2*c)^(4:ℕ)) (max 2 (32 * ((2:ℝ)^12 * (Nat.factorial 12 : ℝ))))),
    by positivity, ?_⟩
  intro t ht
  have ht1 : (1:ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have ht2c4 : ((2*c)^(4:ℕ)) ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht2 : (2:ℝ) ≤ t :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) ht
  have htA : 32 * ((2:ℝ)^12 * (Nat.factorial 12 : ℝ)) ≤ t :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) ht
  have htpos : (0:ℝ) < t := lt_of_lt_of_le one_pos ht1
  -- `2c ≤ t^{1/4}`
  have hb : (0:ℝ) ≤ 2*c := by positivity
  have h24 : (2*c)^((4:ℕ):ℝ) ≤ t := by rw [Real.rpow_natCast]; exact ht2c4
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hb _) h24 (show (0:ℝ) ≤ (1:ℝ)/4 by norm_num)
  have hlhs : ((2*c)^((4:ℕ):ℝ))^((1:ℝ)/4) = 2*c := by
    rw [← Real.rpow_mul hb]; norm_num
  have hroot : 2*c ≤ t^((1:ℝ)/4) := by rw [← hlhs]; exact hpow
  -- hence `c·t^{1/4} ≤ √t/2`
  have htq_nonneg : (0:ℝ) ≤ t^((1:ℝ)/4) := Real.rpow_nonneg htpos.le _
  have hc_le : c ≤ t^((1:ℝ)/4)/2 := by linarith
  have h1 : c * t^((1:ℝ)/4) ≤ (t^((1:ℝ)/4)/2) * t^((1:ℝ)/4) :=
    mul_le_mul_of_nonneg_right hc_le htq_nonneg
  have hsq : t^((1:ℝ)/4) * t^((1:ℝ)/4) = Real.sqrt t := by
    rw [← Real.rpow_add htpos, Real.sqrt_eq_rpow]; norm_num
  have h2 : (t^((1:ℝ)/4)/2) * t^((1:ℝ)/4) = Real.sqrt t / 2 := by
    rw [div_mul_eq_mul_div, hsq]
  have hct : c * t^((1:ℝ)/4) ≤ Real.sqrt t / 2 := by rw [← h2]; exact h1
  have hexp_le : Real.exp (Real.sqrt t / 2) ≤ Real.exp (Real.sqrt t - c * t ^ ((1:ℝ)/4)) :=
    Real.exp_le_exp.mpr (by linarith [hct])
  -- `(t+2)^5 ≤ exp(√t/2)` via the Taylor bound `x^12/12! ≤ exp x`
  have hfac := Real.pow_div_factorial_le_exp (Real.sqrt t / 2) (by positivity) 12
  have hnum : (Real.sqrt t)^12 = t^6 := by
    rw [show (12:ℕ) = 2*6 by norm_num, pow_mul, Real.sq_sqrt htpos.le]
  have hsimp : (Real.sqrt t / 2)^12 / (Nat.factorial 12 : ℝ)
      = t^6 / ((2:ℝ)^12 * (Nat.factorial 12 : ℝ)) := by
    rw [div_pow, hnum, div_div]
  have hpoly : (t+2)^(5:ℕ) ≤ (Real.sqrt t / 2)^12 / (Nat.factorial 12 : ℝ) := by
    rw [hsimp]
    have h1 : (t+2)^(5:ℕ) ≤ (2*t)^(5:ℕ) :=
      pow_le_pow_left₀ (by linarith) (by linarith) 5
    have h2 : (2*t)^(5:ℕ) = 32 * t^5 := by ring
    rw [h2] at h1
    refine le_trans h1 ?_
    rw [le_div_iff₀ hDpos]
    calc 32 * t^5 * ((2:ℝ)^12 * (Nat.factorial 12 : ℝ))
        = t^5 * (32 * ((2:ℝ)^12 * (Nat.factorial 12 : ℝ))) := by ring
      _ ≤ t^5 * t := mul_le_mul_of_nonneg_left htA (by positivity)
      _ = t^6 := by ring
  linarith [hpoly, hfac, hexp_le]

theorem S16_exp_arith :
    (0 < Work.FITop4.nuU) ∧
    (1 ≤ Work.FITop4.nuU) ∧
    (∀ c : ℝ, 0 < c → ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, t0 ≤ t →
      (t + 2) ^ (5 : ℕ) ≤ Real.exp (Real.sqrt t - c * t ^ ((1 : ℝ) / 4))) ∧
    (∀ (d X : ℕ) (L : ℝ), 1 ≤ d → d ≤ X → 0 < L → (X : ℝ) ≤ L ^ Work.FITop4.nuU →
      L ^ ((1 : ℝ) / 4) * ((4 : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) / 2)
        ≤ ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) * Real.sqrt L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
    norm_num
  · exact nuU_ge_one
  · exact exp_growth
  · intro d X L hd hdX hL hX
    have hnu : 0 < Work.FITop4.nuU := by
      unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
      norm_num
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hdX' : (d:ℝ) ≤ (X:ℝ) := by exact_mod_cast hdX
    have h4d : ((4 * d : ℕ) : ℝ) = 4 * (d:ℝ) := by push_cast; ring
    have h4dpos : (0:ℝ) < ((4 * d : ℕ) : ℝ) := by rw [h4d]; linarith
    have hlnnu_pos : 0 < L ^ Work.FITop4.nuU := Real.rpow_pos_of_pos hL _
    have hle : ((4 * d : ℕ) : ℝ) ≤ 4 * L ^ Work.FITop4.nuU := by
      rw [h4d]
      have : (d:ℝ) ≤ L ^ Work.FITop4.nuU := le_trans hdX' hX
      linarith
    have hstep := Real.rpow_le_rpow_of_nonpos h4dpos hle
      (show -(1/(4*Work.FITop4.nuU)) ≤ 0 by
        have : 0 < 1/(4*Work.FITop4.nuU) := by positivity
        linarith)
    have hexp : Work.FITop4.nuU * (-(1/(4*Work.FITop4.nuU))) = -(1:ℝ)/4 := by
      field_simp
    have hExp : (4 * L ^ Work.FITop4.nuU) ^ (-(1/(4*Work.FITop4.nuU)))
        = (4:ℝ) ^ (-(1/(4*Work.FITop4.nuU))) * L ^ (-(1:ℝ)/4) := by
      rw [Real.mul_rpow (by norm_num) hlnnu_pos.le, ← Real.rpow_mul hL.le, hexp]
    rw [hExp] at hstep
    have hLexp : L ^ (-(1:ℝ)/4) * Real.sqrt L = L ^ ((1:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
      norm_num
    calc L ^ ((1:ℝ)/4) * ((4:ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) / 2)
        ≤ (4:ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) * L ^ ((1:ℝ)/4) := by
          have h2 : (0:ℝ) < (4:ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) :=
            Real.rpow_pos_of_pos (by norm_num) _
          have h4 : (0:ℝ) ≤ L ^ ((1:ℝ)/4) := Real.rpow_nonneg hL.le _
          nlinarith [h2, h4]
      _ = (4:ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) * (L ^ (-(1:ℝ)/4) * Real.sqrt L) := by
          rw [hLexp]
      _ = ((4:ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) * L ^ (-(1:ℝ)/4)) * Real.sqrt L := by ring
      _ ≤ ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU))) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg L)

end Work.FIArea6
