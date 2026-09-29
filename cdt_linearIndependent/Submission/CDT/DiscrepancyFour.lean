import Submission.CDT.Discrepancy

/-!
# The paper's shape of the discrepancy concentration estimate

`Submission.CDT.Discrepancy.disc_concentration` gives
`(muP n).real {t | ε ≤ disc t} ≤ min 1 (100·ε⁻²·exp(−n·ε²/8))`.
Splitting on which branch of the `min` is attained and clearing the resulting logarithmic
inequalities (`ε² log(1/ε) ≤ 1`, `log 100 ≥ 4`) turns this into the shape stated in the paper's
§"Concentration of measure", with the exponent `ε⁴`:

* `log_100_ge_four`, `sq_mul_log_inv_le_one`, `log_100_mul_inv_sq` — the elementary estimates;
* `disc_concentration_four` — **`vol{D ≥ ε} ≤ 100·exp(−n·ε⁴/100)`** for `n ≥ 1`, `ε > 0`
  (for `ε > 1` the event is empty because `disc ≤ 1`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Submission.CDT.Discrepancy

lemma log_100_ge_four : (4:ℝ) ≤ Real.log 100 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 100)]
  have h : Real.exp 4 = (Real.exp 1)^4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have h3 : (Real.exp 1)^4 ≤ (2.72:ℝ)^4 := pow_le_pow_left₀ (le_of_lt h2) (le_of_lt h1) 4
  have h4 : (2.72:ℝ)^4 ≤ 100 := by norm_num
  linarith [h, h3, h4]

lemma sq_mul_log_inv_le_one {ε : ℝ} (hε : 0 < ε) : ε^2 * Real.log (1/ε) ≤ 1 := by
  have hlog : Real.log (1/ε) ≤ 1/ε - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hmul : ε^2 * Real.log (1/ε) ≤ ε^2 * (1/ε - 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have heq : ε^2 * (1/ε - 1) = ε - ε^2 := by field_simp
  have hle : ε - ε^2 ≤ 1 := by nlinarith [sq_nonneg (2*ε - 1)]
  linarith [hmul, heq, hle]

lemma log_100_mul_inv_sq {ε : ℝ} (hε : 0 < ε) :
    Real.log (100 * (ε⁻¹)^2) = Real.log 100 + 2 * Real.log (1/ε) := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  simp only [one_div, Real.log_inv]
  ring

/-- The paper's shape of the concentration estimate: exponent `ε⁴`. -/
theorem disc_concentration_four {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (muP n).real {t : Fin n → ℝ | ε ≤ disc t}
      ≤ 100 * Real.exp (-(n:ℝ) * ε^4 / 100) := by
  rcases lt_or_ge (1:ℝ) ε with hbig | hsmall
  · have hempty : {t : Fin n → ℝ | ε ≤ disc t} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt (disc_le_one t) hbig
    rw [hempty, measureReal_empty]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · have hsharp := disc_concentration hn hε
    have hM : (0:ℝ) ≤ Real.log (1/ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have hL : (4:ℝ) ≤ Real.log 100 := log_100_ge_four
    have hsq : ε^2 * Real.log (1/ε) ≤ 1 := sq_mul_log_inv_le_one hε
    have hesq1 : ε^2 ≤ 1 := by nlinarith
    refine hsharp.trans ?_
    rcases lt_or_ge (100 * (ε⁻¹)^2 * Real.exp (-(n:ℝ) * ε^2 / 8)) 1 with hA | hA
    · -- `A < 1`: the `min` is `A`
      rw [min_eq_right (le_of_lt hA)]
      have hD : 100 * (ε⁻¹)^2 ≤ Real.exp ((n:ℝ) * ε^2 / 8) := by
        have hmul := mul_lt_mul_of_pos_right hA (Real.exp_pos ((n:ℝ) * ε^2 / 8))
        rw [mul_assoc, ← Real.exp_add, show -↑n * ε^2/8 + ↑n * ε^2/8 = (0:ℝ) by ring,
          Real.exp_zero, mul_one, one_mul] at hmul
        exact hmul.le
      have hlogineq : Real.log 100 + 2 * Real.log (1/ε) ≤ (n:ℝ) * ε^2 / 8 := by
        have h2 := Real.log_le_log (by positivity : (0:ℝ) < 100 * (ε⁻¹)^2) hD
        rw [log_100_mul_inv_sq hε, Real.log_exp] at h2
        exact h2
      have hδ : (0:ℝ) < 1 - 8*ε^2/100 := by nlinarith
      have hkey : 2 * Real.log (1/ε)
          ≤ (Real.log 100 + 2 * Real.log (1/ε)) * (1 - 8*ε^2/100) := by
        have h1 : (16 * ε^2 / 100) * Real.log (1/ε) ≤ 16/100 := by nlinarith
        have h2 : (4:ℝ) * (1 - 8/100) ≤ Real.log 100 * (1 - 8*ε^2/100) := by nlinarith
        nlinarith [h1, h2, hM, hδ]
      have hstep : 2 * Real.log (1/ε) ≤ (n:ℝ)*ε^2/8 - (n:ℝ)*ε^4/100 := by
        have h3 : (Real.log 100 + 2*Real.log (1/ε)) * (1 - 8*ε^2/100)
            ≤ ((n:ℝ)*ε^2/8) * (1 - 8*ε^2/100) :=
          mul_le_mul_of_nonneg_right hlogineq (le_of_lt hδ)
        have h4 : ((n:ℝ)*ε^2/8) * (1 - 8*ε^2/100) = (n:ℝ)*ε^2/8 - (n:ℝ)*ε^4/100 := by
          ring
        linarith [hkey, h3, h4]
      have hexp : Real.exp (2 * Real.log (1/ε))
          ≤ Real.exp ((n:ℝ)*ε^2/8 - (n:ℝ)*ε^4/100) := Real.exp_le_exp.mpr hstep
      have hεinv : Real.exp (2 * Real.log (1/ε)) = (ε⁻¹)^2 := by
        rw [show (2:ℝ) * Real.log (1/ε) = ((2:ℕ):ℝ) * Real.log (1/ε) by norm_num,
          Real.exp_nat_mul, Real.exp_log (by positivity : (0:ℝ) < 1/ε), one_div]
      have hmain : (ε⁻¹)^2 ≤ Real.exp ((n:ℝ)*ε^2/8 - (n:ℝ)*ε^4/100) := by
        rw [← hεinv]; exact hexp
      calc 100 * (ε⁻¹)^2 * Real.exp (-(n:ℝ) * ε^2 / 8)
          ≤ 100 * Real.exp ((n:ℝ)*ε^2/8 - (n:ℝ)*ε^4/100)
              * Real.exp (-(n:ℝ) * ε^2 / 8) := by gcongr
        _ = 100 * Real.exp (-(n:ℝ) * ε^4 / 100) := by
            rw [mul_assoc, ← Real.exp_add]
            norm_num
            ring_nf
    · -- `1 ≤ A`: the `min` is `1`
      have hD : Real.exp ((n:ℝ) * ε^2 / 8) ≤ 100 * (ε⁻¹)^2 := by
        have hmul := mul_le_mul_of_nonneg_right hA
          (le_of_lt (Real.exp_pos ((n:ℝ) * ε^2 / 8)))
        rw [mul_assoc, ← Real.exp_add, show -↑n * ε^2/8 + ↑n * ε^2/8 = (0:ℝ) by ring,
          Real.exp_zero, mul_one, one_mul] at hmul
        exact hmul
      have hlogineq : (n:ℝ) * ε^2 / 8 ≤ Real.log 100 + 2 * Real.log (1/ε) := by
        have h2 := Real.log_le_log (Real.exp_pos _) hD
        rw [Real.log_exp, log_100_mul_inv_sq hε] at h2
        exact h2
      have hbound : (n:ℝ)*ε^4 ≤ 100 * Real.log 100 := by
        have h3 : (n:ℝ)*ε^2 ≤ 8 * (Real.log 100 + 2 * Real.log (1/ε)) := by linarith
        have h4 : (n:ℝ)*ε^4 = ((n:ℝ)*ε^2) * ε^2 := by ring
        have h5 : (8 * (Real.log 100 + 2 * Real.log (1/ε))) * ε^2
            ≤ (8 * (Real.log 100 + 2)) * 1 := by
          have h6 : (Real.log 100 + 2 * Real.log (1/ε)) * ε^2 ≤ (Real.log 100 + 2) * 1 := by
            nlinarith [hsq, hM, hL, hesq1]
          linarith
        have h7 : 8 * (Real.log 100 + 2) ≤ 100 * Real.log 100 := by nlinarith
        nlinarith [h3, h4, h5, h7]
      have hge : (1:ℝ) ≤ 100 * Real.exp (-(n:ℝ) * ε^4 / 100) := by
        have hc' : (n:ℝ)*ε^4/100 ≤ Real.log 100 := by linarith [hbound]
        have hexp : Real.exp ((n:ℝ)*ε^4/100) ≤ 100 := by
          calc Real.exp ((n:ℝ)*ε^4/100) ≤ Real.exp (Real.log 100) := Real.exp_le_exp.mpr hc'
            _ = 100 := Real.exp_log (by norm_num)
        have hinv : (100:ℝ)⁻¹ ≤ (Real.exp ((n:ℝ)*ε^4/100))⁻¹ :=
          (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr hexp
        have harg : Real.exp (-(n:ℝ) * ε^4 / 100) = (Real.exp ((n:ℝ)*ε^4/100))⁻¹ := by
          rw [show -(n:ℝ) * ε^4 / 100 = -((n:ℝ) * ε^4 / 100) by ring, Real.exp_neg]
        rw [harg]
        nlinarith [hinv]
      rw [min_eq_left hA]
      exact hge

end Submission.CDT.Discrepancy
