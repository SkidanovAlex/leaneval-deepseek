import Mathlib
import Submission.Work.FatouCH.Ends.Basic

namespace Work.FatouCH.Ends

open Set Metric Filter
open scoped Topology

/-- The pointwise bound `psi K κ T = 2K/T² + 2K exp(-κT/8)` is nonnegative, decreasing on `(0,∞)`
and tends to `0` at `+∞`. -/
theorem endsPsiSmall {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 < κ) :
    (∀ T : ℝ, 0 < T → 0 ≤ psi K κ T) ∧
      AntitoneOn (fun T : ℝ => psi K κ T) (Set.Ioi 0) ∧
      Tendsto (fun T : ℝ => psi K κ T) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Nonnegativity: both summands are nonnegative for `T > 0`.
    intro T hT
    have h1 : 0 ≤ 2 * K / T ^ 2 := div_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ 2 * K * Real.exp (-(κ * T / 8)) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    simp only [psi]
    linarith
  · -- Antitonicity on `(0,∞)`: `2K/T²` and `2K exp(-κT/8)` are both antitone there.
    intro a ha b hb hab
    have h2K : 0 ≤ 2 * K := by linarith
    have hsq : a ^ 2 ≤ b ^ 2 := by
      rw [sq_le_sq, abs_of_pos ha, abs_of_pos hb]; exact hab
    have hdiv : 2 * K / b ^ 2 ≤ 2 * K / a ^ 2 :=
      div_le_div_of_nonneg_left h2K (pow_pos ha 2) hsq
    have hexp : Real.exp (-(κ * b / 8)) ≤ Real.exp (-(κ * a / 8)) :=
      Real.exp_le_exp.mpr (by nlinarith [hκ, hab])
    have hexpm : 2 * K * Real.exp (-(κ * b / 8)) ≤ 2 * K * Real.exp (-(κ * a / 8)) :=
      mul_le_mul_of_nonneg_left hexp h2K
    simp only [psi]
    linarith
  · -- Limit `0` at `+∞`: `2K/T² → 0` and the exponential tail decays.
    have h1 : Tendsto (fun T : ℝ => 2 * K / T ^ 2) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop (f := fun _ : ℝ => 2 * K) (g := fun T : ℝ => T ^ 2)
        tendsto_const_nhds (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
    have harg : Tendsto (fun T : ℝ => κ * T / 8) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num)
        (Filter.Tendsto.const_mul_atTop hκ tendsto_id)
    have hneg : Tendsto (fun T : ℝ => -(κ * T / 8)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp harg
    have hexp : Tendsto (fun T : ℝ => Real.exp (-(κ * T / 8))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have h2 : Tendsto (fun T : ℝ => 2 * K * Real.exp (-(κ * T / 8))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * K)).mul hexp
    simp only [psi]
    simpa using h1.add h2

end Work.FatouCH.Ends
