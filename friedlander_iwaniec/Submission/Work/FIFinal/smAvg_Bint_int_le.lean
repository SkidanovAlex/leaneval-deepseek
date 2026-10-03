import Mathlib
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.ASP.Defs
import Submission.ASP.S3v
import Submission.ASP.S7b
import Submission.ASP.S7c
import Submission.ASP.S7d
import Submission.ASP.S7e
import Submission.ASP.S8
import Submission.ASP.S8b

namespace Work.FIFinal

open MeasureTheory
open scoped Interval

/-- The `(B′)`-integrand `Bint a N w` is nonnegative whenever the weights `w` are. -/
lemma Bint_nonneg (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (hw0 : ∀ ℓ, 0 ≤ w ℓ) (v : ℝ) :
    0 ≤ Submission.ASP.Bint a N w v := by
  simp only [Submission.ASP.Bint]
  exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (hw0 ℓ) (abs_nonneg _))

/-- The `BprimeWindowInt` hypothesis, in terms of `Bint`. -/
lemma BprimeWindowInt_iff_Bint_integral (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E lo hi : ℝ) :
    Work.FIChain.BprimeWindowInt a N w E lo hi
      ↔ (∫ t in lo..hi, Submission.ASP.Bint a N w t / t) ≤ E := Iff.rfl

/-- **Dyadic smearing of the integrated `(B′)`-window.**
The average over `u ∈ [Y/Δ, eY]` of `Bint a N w (2^j u) / u` is at most the window average `E`,
because the substitution `v = 2^j u` only shrinks the range: `[2^j Y/Δ, 2^j eY] ⊆ [Y/Δ, 2^J eY]`
(`j < J`) and the integrand `Bint a N w v / v` is nonnegative there. -/
lemma smAvg_Bint_int_le (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) {E Y : ℝ} {J j : ℕ} {Δ : ℕ}
    (hj : j < J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hB : Work.FIChain.BprimeWindowInt a N w E (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y))) :
    (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
        Submission.ASP.Bint a N w ((2 : ℝ) ^ j * u) / u) ≤ E := by
  -- the window hypothesis, phrased through `Bint`
  have hB' : (∫ t in Y / (Δ : ℝ)..(2 : ℝ) ^ J * (Real.exp 1 * Y),
      Submission.ASP.Bint a N w t / t) ≤ E :=
    hB
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hlo_pos : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have heY_pos : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  -- `Y/Δ ≤ e·Y` and hence `Y/Δ ≤ 2^J·(e·Y)`
  have hlo_eY : Y / (Δ : ℝ) ≤ Real.exp 1 * Y :=
    (div_le_self hY.le hΔ1).trans
      (le_mul_of_one_le_left hY.le (Real.one_le_exp_iff.mpr (by norm_num)))
  have hc : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  -- the three endpoint inequalities for the submersion of the range
  have hca : Y / (Δ : ℝ) ≤ (2 : ℝ) ^ j * (Y / (Δ : ℝ)) := by
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hlo_pos.le
  have hab : (2 : ℝ) ^ j * (Y / (Δ : ℝ)) ≤ (2 : ℝ) ^ j * (Real.exp 1 * Y) :=
    mul_le_mul_of_nonneg_left hlo_eY hc.le
  have hbd : (2 : ℝ) ^ j * (Real.exp 1 * Y) ≤ (2 : ℝ) ^ J * (Real.exp 1 * Y) :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj.le) heY_pos.le
  -- nonnegativity of the integrand on the window
  have hf : 0 ≤ᵐ[volume.restrict (Set.Ioc (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y)))]
      (fun v => Submission.ASP.Bint a N w v / v) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun v hv =>
        div_nonneg (Bint_nonneg a N w hw0 v) (le_of_lt (lt_trans hlo_pos hv.1))))
  have hfi : IntervalIntegrable (fun v => Submission.ASP.Bint a N w v / v) volume
      (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y)) := by
    simpa using Submission.ASP.intervalIntegrable_Bint_div a N w (c := 1) hlo_pos
      (hlo_eY.trans (le_mul_of_one_le_left heY_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))))
  -- substitute `v = 2^j u` and compare with the (larger) window average
  rw [Submission.ASP.integral_comp_mul_div (Φ := Submission.ASP.Bint a N w) hc
    (Y / (Δ : ℝ)) (Real.exp 1 * Y)]
  exact (intervalIntegral.integral_mono_interval hca hab hbd hf hfi).trans hB'

end Work.FIFinal
