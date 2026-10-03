import Mathlib
import Submission.Work.FIArea6V.CleanVDefs
import Submission.Work.FIArea6Road.TailFreqLBound
import Submission.Work.FIArea6.TauCore.params_caseB_bounds
import Submission.Work.FIArea6V.S16WinTauSqBound
import Submission.Work.FIArea6V.S16TailFreqArith

namespace Work.FIArea6V

/-- Arithmetic of the tail in the complementary regime `exp(-(√log N)/4)(log N)^3 ≤ θ`: now the
sharp frequency-tail bound `Σ_{|ℓ|>L}|q̂(ℓ)| ≤ 2·10^7/(πθL)`, `L = freqL Pa ≥ exp(√log N)/2`,
supplies the factor `1/L ≤ 2exp(-√log N)`, which cancels the growth of the norm-window mass
(`θ^{-1} ≤ exp((√log N)/4)(log N)^{-3}` from the hypothesis, and `winTauSq ≤ C·N·(log N)^3` from
`Commons.NumberTheory.DivisorSum.sum_tau_pow_le 2` since `winTauSq` is a sub-sum of
`Σ_{n ≤ ⌊(1+θ)N⌋} τ(n)²` and `θ ≤ 1`), so the product is dominated by the target's
`exp(-(√log N)/4)·N·(log N)^6` for large `N` (uniformly in the other parameters of `Pa`). -/
theorem S16CleanTailArithLargeTheta :
    ∃ CT x0 : ℝ, 0 < CT ∧ 0 < x0 ∧ ∀ Pa : Work.FITop.Params, x0 ≤ (Pa.x : ℝ) →
      Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * (Real.log Pa.N) ^ (3 : ℕ) ≤ Pa.θ →
      (4 * Work.FIArea6V.winTauSq Pa)
          * (20000000 / (Real.pi * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ)))
        ≤ CT * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
            * (Real.log Pa.N) ^ (6 : ℕ) := by
  obtain ⟨Cw, hCwpos, hCwb⟩ := Work.FIArea6V.S16WinTauSqBound
  refine ⟨16 * (10 : ℝ) ^ 7 * Cw / Real.pi, Real.exp 64, by positivity, Real.exp_pos 64, ?_⟩
  intro Pa hx hθ
  have hx8 : Real.exp 8 ≤ (Pa.x : ℝ) := by
    have h1 : Real.exp 8 ≤ Real.exp 64 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  obtain ⟨hL1, hN3, hθ1⟩ := Work.FIArea6.TauCore.params_caseB_bounds Pa hx8
  have hFle : Real.exp (Real.sqrt (Real.log Pa.N)) / 2
      ≤ (Work.FIArea6Hecke.freqL Pa : ℝ) :=
    Work.FIArea6Road.half_le_freqL Pa hL1
  have hFpos : (0 : ℝ) < (Work.FIArea6Hecke.freqL Pa : ℝ) := by
    have h := Real.exp_pos (Real.sqrt (Real.log Pa.N))
    linarith
  have hS : Work.FIArea6V.winTauSq Pa ≤ Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := hCwb Pa hx8
  have hrecip : (Real.log Pa.N) ^ (3 : ℕ) / (Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ))
      ≤ 2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * (Real.log Pa.N) ^ (6 : ℕ) :=
    Work.FIArea6V.S16TailFreqArith (L := Real.log Pa.N) (θ := Pa.θ)
      (F := (Work.FIArea6Hecke.freqL Pa : ℝ)) hL1 Pa.hθ0 hFpos hθ hFle
  have hLpos : (0 : ℝ) < Real.log Pa.N := by linarith
  have hL3pos : (0 : ℝ) < (Real.log Pa.N) ^ (3 : ℕ) := pow_pos hLpos 3
  have hθF : (0 : ℝ) < Real.pi * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) :=
    mul_pos (mul_pos Real.pi_pos Pa.hθ0) hFpos
  have hkey : (1 : ℝ) ≤ 2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
      * (Real.log Pa.N) ^ (3 : ℕ) * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) := by
    have hcoef : (0 : ℝ) ≤ Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) / (Real.log Pa.N) ^ (3 : ℕ) :=
      div_nonneg (mul_nonneg (le_of_lt Pa.hθ0) (le_of_lt hFpos)) (le_of_lt hL3pos)
    have h1 := mul_le_mul_of_nonneg_right hrecip hcoef
    have hleft : ((Real.log Pa.N) ^ (3 : ℕ) / (Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ)))
        * (Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) / (Real.log Pa.N) ^ (3 : ℕ)) = 1 := by
      field_simp [ne_of_gt hLpos, ne_of_gt Pa.hθ0, ne_of_gt hFpos]
    have hright : (2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * (Real.log Pa.N) ^ (6 : ℕ))
        * (Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) / (Real.log Pa.N) ^ (3 : ℕ))
        = 2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ) * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ) := by
      field_simp
    linarith [h1, hleft.le, hright.le]
  rw [← mul_div_assoc, div_le_iff₀ hθF]
  have hS8 : 4 * Work.FIArea6V.winTauSq Pa * 20000000
      ≤ 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ)) := by
    have h1 : (4 : ℝ) * Work.FIArea6V.winTauSq Pa * 20000000
        = 80000000 * Work.FIArea6V.winTauSq Pa := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hS (by norm_num)
  have hstep : 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ))
      ≤ 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ))
        * (2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ) * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ)) := by
    have ha : (0 : ℝ) ≤ 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ)) := by positivity
    calc 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ))
        = 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ)) * 1 := by ring
      _ ≤ 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ))
          * (2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
            * (Real.log Pa.N) ^ (3 : ℕ) * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey ha
  have hfin : 80000000 * (Cw * Pa.N * (Real.log Pa.N) ^ (3 : ℕ))
        * (2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ) * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ))
      = (16 * (10 : ℝ) ^ 7 * Cw / Real.pi) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
          * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
        * (Real.pi * Pa.θ * (Work.FIArea6Hecke.freqL Pa : ℝ)) := by
    field_simp
    ring
  linarith [hS8, hstep, hfin.le, hfin.ge]

end Work.FIArea6V
