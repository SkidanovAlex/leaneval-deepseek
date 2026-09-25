import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace Commons.Analysis.Real

open Filter
open scoped Topology

/-- Upper bound for the Euler–Mascheroni constant, obtained from the sequence
`n ↦ H_n - log (n + 1/2)`, which decreases to `γ`: `γ < 49/20 - log (13/2) < 0.5782`. -/
lemma eulerMascheroniConstant_lt_log_thirteen_half :
    Real.eulerMascheroniConstant < 49 / 20 - Real.log (13 / 2) := by
  let d : ℕ → ℝ := fun n => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2)
  have hanti : StrictAnti d := by
    refine strictAnti_nat_of_succ_lt fun n => ?_
    have hsucc : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
      rw [harmonic_succ]
      push_cast
      ring
    have key : 1 / ((n : ℝ) + 1)
        < Real.log ((n : ℝ) + 3 / 2) - Real.log ((n : ℝ) + 1 / 2) := by
      have hy : 0 < 2 / (2 * (n : ℝ) + 1) := by positivity
      have h := Real.lt_log_one_add_of_pos hy
      have hkey : Real.log (1 + 2 / (2 * (n : ℝ) + 1))
          = Real.log ((n : ℝ) + 3 / 2) - Real.log ((n : ℝ) + 1 / 2) := by
        rw [show (1 + 2 / (2 * (n : ℝ) + 1)) = ((n : ℝ) + 3 / 2) / ((n : ℝ) + 1 / 2) by
          field_simp; ring]
        rw [Real.log_div (by positivity) (by positivity)]
      have hval : 2 * (2 / (2 * (n : ℝ) + 1)) / (2 / (2 * (n : ℝ) + 1) + 2)
          = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      rw [hkey, hval] at h
      exact h
    simp only [d]
    push_cast
    rw [hsucc]
    rw [show ((n : ℝ) + 1 + 1 / 2) = (n : ℝ) + 3 / 2 by ring]
    linarith
  have hlim : Tendsto d atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hbase : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
        (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
    have hlog0 : Tendsto (fun n : ℕ => Real.log (1 + 1 / (2 * (n : ℝ)))) atTop (𝓝 0) := by
      have h2n : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
      have hinner : Tendsto (fun n : ℕ => 1 + 1 / (2 * (n : ℝ))) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add h2n
      have hcomp := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinner
      rw [Real.log_one] at hcomp
      exact hcomp
    have hsub := hbase.sub hlog0
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hfactor : (n : ℝ) + 1 / 2 = (n : ℝ) * (1 + 1 / (2 * (n : ℝ))) := by
      field_simp
    simp only [d]
    rw [hfactor, Real.log_mul hne (by positivity)]
    ring
  have hle : Real.eulerMascheroniConstant ≤ d 7 := hanti.antitone.le_of_tendsto hlim 7
  have hlt : d 7 < d 6 := hanti (by norm_num : (6 : ℕ) < 7)
  have hd6 : d 6 = 49 / 20 - Real.log (13 / 2) := by
    simp only [d]
    norm_num [harmonic]
  rw [hd6] at hlt
  exact lt_of_le_of_lt hle hlt

/-- `log (26 * π) > 4.4`, proved from `e^{22/5} = e^4 · e^{2/5} < 26 π`. -/
lemma log_26_pi_ge : (22 : ℝ) / 5 ≤ Real.log (26 * Real.pi) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  rw [show (22 : ℝ) / 5 = 4 + 2 / 5 by norm_num, Real.exp_add]
  have he4 : Real.exp 4 < 54.59816 := by
    have heq : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    calc (Real.exp 1) ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
          gcongr
          exact Real.exp_one_lt_d9
      _ < 54.59816 := by norm_num
  have he25 : Real.exp (2 / 5) ≤ 1119 / 750 := by
    have h := Real.exp_bound' (x := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    refine h.trans (le_of_eq ?_)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hprod : Real.exp 4 * Real.exp (2 / 5) ≤ (54.59816 : ℝ) * (1119 / 750) :=
    mul_le_mul he4.le he25 (by positivity) (by norm_num)
  have hlt : (54.59816 : ℝ) * (1119 / 750) < 26 * Real.pi := by nlinarith [hpi]
  linarith

theorem eulerMascheroni_sub_log_four_pi_le_twentieth :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 1 / 20 := by
  have hγ : Real.eulerMascheroniConstant < 49 / 20 - Real.log (13 / 2) :=
    eulerMascheroniConstant_lt_log_thirteen_half
  have hlog : (22 : ℝ) / 5 ≤ Real.log (26 * Real.pi) := log_26_pi_ge
  have hlogmul : Real.log (26 * Real.pi) = Real.log (13 / 2) + Real.log (4 * Real.pi) := by
    rw [← Real.log_mul (by norm_num : (13 / 2 : ℝ) ≠ 0) (by positivity : (4 * Real.pi) ≠ 0)]
    congr 1
    ring
  have hmain : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)
      < 89 / 20 - Real.log (26 * Real.pi) := by
    rw [hlogmul]
    linarith [hγ]
  linarith [hmain, hlog]

end Commons.Analysis.Real