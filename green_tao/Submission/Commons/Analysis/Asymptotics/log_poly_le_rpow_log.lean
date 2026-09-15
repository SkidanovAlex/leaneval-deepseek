import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.Asymptotics

open scoped Topology

/-- For fixed `C, B, δ, ε > 0`, `q ≥ 1` and `m ≥ 1` the (polynomial in `log R`) error term
`C^m B (1 + (log R)^{m-1}) + C^m B exp(-δ √(log R))` is dominated by `(ε/4) (q log R)^m` for all
sufficiently large `R`; explicitly there is `R₀ ≥ 3` with this property.

Suggested proof. For `R ≥ 3`, `log R ≥ 1`, so `(log R)^{m-1} ≤ (log R)^m`, `1 ≤ (log R)^m` and
`exp(-δ√(log R)) ≤ 1 ≤ (log R)^m`; hence the left-hand side is at most `3 C^m B (log R)^m`.
Since `q ≥ 1` and `log R ≥ 1`, `(log R)^m ≤ (q log R)^m`, and it remains to have
`3 C^m B ≤ (ε/4) (log R)^m`, i.e. `log R ≥ t` where `t := (12 C^m B / ε)^{1/m}`.  Take
`R₀ := max 3 (exp t)` and use `Real.log_le_log`, `Real.exp_le_exp`, `Real.le_log_iff_exp_le`,
`Real.rpow_natCast`, `Real.rpow_le_rpow`, `Real.exp_pos`, `Real.log_pos`. -/
theorem log_poly_le_rpow_log {C B δ q ε : ℝ} (hC : 0 < C) (hB : 0 < B)
    (hδ : 0 < δ) (hq : 1 ≤ q) (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) :
    ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      C ^ m * B * (1 + (Real.log R) ^ (m - 1)) + C ^ m * B * Real.exp (-(δ * Real.sqrt (Real.log R)))
        ≤ (ε / 4) * (q * Real.log R) ^ m := by
  refine ⟨max 3 (Real.exp (12 * C ^ m * B / ε)), le_max_left _ _, ?_⟩
  intro R hR
  have hR3 : (3 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRx : Real.exp (12 * C ^ m * B / ε) ≤ R := le_trans (le_max_right _ _) hR
  set s : ℝ := Real.log R with hs_def
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs_def]
    have h1 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    have h2 : Real.log 3 ≤ Real.log R := Real.log_le_log (by norm_num) hR3
    linarith
  have hxs : 12 * C ^ m * B / ε ≤ s := by
    rw [hs_def]
    have h := Real.log_le_log (Real.exp_pos _) hRx
    rwa [Real.log_exp] at h
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hsp : (1 : ℝ) ≤ s ^ (m - 1) := one_le_pow₀ hs1
  have he : Real.exp (-(δ * Real.sqrt s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ δ * Real.sqrt s := mul_nonneg hδ.le (Real.sqrt_nonneg s)
    linarith
  have hA : (0 : ℝ) < C ^ m * B := mul_pos (pow_pos hC m) hB
  have hstep1 : C ^ m * B * (1 + s ^ (m - 1)) + C ^ m * B * Real.exp (-(δ * Real.sqrt s))
      ≤ 3 * (C ^ m * B) * s ^ (m - 1) := by
    nlinarith [hA, hsp, he]
  have hge : 3 * (C ^ m * B) ≤ (ε / 4) * s := by
    have h0 : (ε / 4) * (12 * C ^ m * B / ε) = 3 * (C ^ m * B) := by
      field_simp
      ring
    calc 3 * (C ^ m * B) = (ε / 4) * (12 * C ^ m * B / ε) := h0.symm
      _ ≤ (ε / 4) * s := mul_le_mul_of_nonneg_left hxs (by linarith)
  have hstep2 : 3 * (C ^ m * B) * s ^ (m - 1) ≤ (ε / 4) * s ^ m := by
    have hsp0 : (0 : ℝ) ≤ s ^ (m - 1) := pow_nonneg hs0 _
    have h2 := mul_le_mul_of_nonneg_right hge hsp0
    have hsm : s ^ m = s * s ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm).symm, pow_succ']
    calc 3 * (C ^ m * B) * s ^ (m - 1) ≤ ((ε / 4) * s) * s ^ (m - 1) := h2
      _ = (ε / 4) * (s * s ^ (m - 1)) := by ring
      _ = (ε / 4) * s ^ m := by rw [hsm]
  have hstep3 : (ε / 4) * s ^ m ≤ (ε / 4) * (q * s) ^ m := by
    have hqs : s ≤ q * s := le_mul_of_one_le_left hs0 hq
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hqs m) (by linarith)
  linarith [hstep1, hstep2, hstep3]

end Commons.Analysis.Asymptotics