import Mathlib

namespace Work.FatouCH.Ends

open Set Metric Filter
open scoped Topology

/-- The tail bound `Ψ T = 2K/T + (16K/κ) exp(-κT/8)` is nonnegative, decreasing on `(0,∞)` and
tends to `0` at `+∞`. -/
theorem endsPsiFacts {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 < κ) :
    (∀ T : ℝ, 0 < T → 0 ≤ 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8))) ∧
      AntitoneOn (fun T : ℝ => 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)))
        (Set.Ioi 0) ∧
      Tendsto (fun T : ℝ => 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8)))
        atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Nonnegativity: `2K/T ≥ 0` and `(16K/κ) * exp(-κT/8) ≥ 0` for `T > 0`.
    intro T hT
    have h1 : 0 ≤ 2 * K / T := div_nonneg (by linarith) (le_of_lt hT)
    have h2 : 0 ≤ 16 * K / κ * Real.exp (-(κ * T / 8)) :=
      mul_nonneg (div_nonneg (by linarith) (le_of_lt hκ)) (Real.exp_pos _).le
    linarith
  · -- Antitonicity on `(0,∞)`: both summands are antitone there.
    intro a ha b hb hab
    have h2K : 0 ≤ 2 * K := by linarith
    have h1 : 2 * K / b ≤ 2 * K / a := div_le_div_of_nonneg_left h2K ha hab
    have hcoef : 0 ≤ 16 * K / κ := div_nonneg (by linarith) (le_of_lt hκ)
    have hexp : Real.exp (-(κ * b / 8)) ≤ Real.exp (-(κ * a / 8)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hκ, hab]
    have h2 : 16 * K / κ * Real.exp (-(κ * b / 8)) ≤
        16 * K / κ * Real.exp (-(κ * a / 8)) :=
      mul_le_mul_of_nonneg_left hexp hcoef
    linarith
  · -- Limit `0` at `+∞`: `2K/T → 0` and the exponential tail decays.
    have h1 : Tendsto (fun T : ℝ => 2 * K / T) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop (f := fun _ : ℝ => 2 * K) (g := id)
        tendsto_const_nhds tendsto_id
    have harg : Tendsto (fun T : ℝ => κ * T / 8) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num)
        (Filter.Tendsto.const_mul_atTop hκ tendsto_id)
    have hneg : Tendsto (fun T : ℝ => -(κ * T / 8)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp harg
    have hexp : Tendsto (fun T : ℝ => Real.exp (-(κ * T / 8))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have h2 : Tendsto (fun T : ℝ => 16 * K / κ * Real.exp (-(κ * T / 8))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 16 * K / κ)).mul hexp
    simpa using h1.add h2

end Work.FatouCH.Ends
