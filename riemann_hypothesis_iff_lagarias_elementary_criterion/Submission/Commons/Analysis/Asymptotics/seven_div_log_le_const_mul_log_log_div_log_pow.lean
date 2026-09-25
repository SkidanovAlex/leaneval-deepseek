import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Asymptotics

theorem seven_div_log_le_const_mul_log_log_div_log_pow
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop,
      7 * (n : ℝ) / Real.log (n : ℝ) ≤
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
  have hL : 0 < L := Real.log_pos hn1
  have hLβ : 0 < L ^ β := Real.rpow_pos_of_pos hL β
  have hmain' : 7 ≤ (C * M) * L ^ α := by
    simpa [L, M] using le_of_lt hmain
  have h1 : 7 * L ^ β ≤ ((C * M) * L ^ α) * L ^ β :=
    mul_le_mul_of_nonneg_right hmain' (le_of_lt hLβ)
  have hαβ : α + β = 1 := by
    dsimp [α]
    ring
  have h2 : ((C * M) * L ^ α) * L ^ β = (C * M) * L := by
    rw [mul_assoc, ← Real.rpow_add hL α β, hαβ, Real.rpow_one]
  have h1' : 7 * L ^ β ≤ (C * M) * L := by
    simpa [h2] using h1
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h3 : (7 * (n : ℝ)) * L ^ β ≤ (C * (n : ℝ) * M) * L := by
    calc
      (7 * (n : ℝ)) * L ^ β = (n : ℝ) * (7 * L ^ β) := by ring
      _ ≤ (n : ℝ) * ((C * M) * L) := mul_le_mul_of_nonneg_left h1' hn
      _ = (C * (n : ℝ) * M) * L := by ring
  exact (div_le_div_iff₀ hL hLβ).2 h3

end Commons.Analysis.Asymptotics