import Mathlib
import Submission.Commons.NumberTheory.Lagarias.harmonic_add_exp_mul_log_le
import Submission.Commons.Analysis.Asymptotics.seven_div_log_le_const_mul_log_log_div_log_pow

namespace Commons.NumberTheory.Lagarias

private lemma seven_div_log_lt_const_mul_log_log_div_log_pow
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop,
      7 * (n : ℝ) / Real.log (n : ℝ) <
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
  let α : ℝ := 1 - β
  have hα : 0 < α := by
    dsimp [α]
    linarith
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlogpow : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ α) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hα).comp Real.tendsto_log_atTop
  have hloglogC : Filter.Tendsto (fun x : ℝ => C * Real.log (Real.log x)) Filter.atTop Filter.atTop :=
    hloglog.const_mul_atTop hC
  have hmul : Filter.Tendsto
      (fun x : ℝ => (C * Real.log (Real.log x)) * (Real.log x) ^ α)
      Filter.atTop Filter.atTop :=
    hloglogC.atTop_mul_atTop₀ hlogpow
  have hnat : Filter.Tendsto
      (fun n : ℕ => (C * Real.log (Real.log (n : ℝ))) * (Real.log (n : ℝ)) ^ α)
      Filter.atTop Filter.atTop :=
    hmul.comp tendsto_natCast_atTop_atTop
  have hmain_ev : ∀ᶠ n : ℕ in Filter.atTop,
      7 < (C * Real.log (Real.log (n : ℝ))) * (Real.log (n : ℝ)) ^ α :=
    hnat.eventually_gt_atTop 7
  have hpos_ev : ∀ᶠ n : ℕ in Filter.atTop, 1 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 1
  filter_upwards [hmain_ev, hpos_ev] with n hmain hn1
  let L : ℝ := Real.log (n : ℝ)
  let M : ℝ := Real.log L
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hn1
  have hLβ : 0 < L ^ β := Real.rpow_pos_of_pos hL β
  have hn0 : 0 < (n : ℝ) := by linarith
  have hmain' : 7 < (C * M) * L ^ α := by
    simpa [L, M] using hmain
  have hstep1 : 7 * (n : ℝ) < (C * M) * L ^ α * (n : ℝ) :=
    mul_lt_mul_of_pos_right hmain' hn0
  have hstep2 : 7 * (n : ℝ) * L ^ β < ((C * M) * L ^ α * (n : ℝ)) * L ^ β :=
    mul_lt_mul_of_pos_right hstep1 hLβ
  have hαβ : α + β = 1 := by
    dsimp [α]
    ring
  have hcomb : L ^ α * L ^ β = L := by
    rw [← Real.rpow_add hL α β, hαβ, Real.rpow_one]
  have hR : ((C * M) * L ^ α * (n : ℝ)) * L ^ β = C * (n : ℝ) * M * L := by
    calc
      ((C * M) * L ^ α * (n : ℝ)) * L ^ β = (C * M) * (L ^ α * L ^ β) * (n : ℝ) := by ring
      _ = (C * M) * L * (n : ℝ) := by rw [hcomb]
      _ = C * (n : ℝ) * M * L := by ring
  have hmain'' : 7 * (n : ℝ) * L ^ β < C * (n : ℝ) * M * L := by
    simpa [hR] using hstep2
  have hfrac : 7 * (n : ℝ) / L < C * (n : ℝ) * M / L ^ β := by
    rw [div_lt_div_iff₀ hL hLβ]
    simpa [mul_assoc] using hmain''
  simpa [L, M] using hfrac

theorem eventually_upper_lt_robin_lower
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
          C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
  have h20 : ∀ᶠ n : ℕ in Filter.atTop, 20 ≤ n := Filter.eventually_ge_atTop 20
  have hlt := seven_div_log_lt_const_mul_log_log_div_log_pow hβ0 hβ hC
  filter_upwards [h20, hlt] with n hn20 hltn
  have hle := harmonic_add_exp_mul_log_le n hn20
  exact lt_of_le_of_lt hle
    (add_lt_add_right hltn
      (Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))))

end Commons.NumberTheory.Lagarias
