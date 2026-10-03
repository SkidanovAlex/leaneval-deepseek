import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# PERT-U: the asymptotic error budget

`Work.PertU.asymp` extracts, from the asymptotic expansion
`τ₀(ψ w) = w + a·log(-w) + b + o(1)` valid on the sector `QLeft ξ`, a quantitative
error bound on the annulus `η/2 ≤ |z| ≤ 2η`, together with the two elementary
inequalities that let the caller absorb the correction `‖a‖·log(2η) + ‖a‖·π + ‖b‖ + 1`
into `η/80` (and a fortiori into `(2/5)η/10`).
-/

namespace Work.PertU

open Complex

/-- `‖log z‖ ≤ |log ‖z‖| + π` for every `z : ℂ` (the principal branch of the logarithm). -/
private lemma norm_log_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have hdec : Complex.log z = (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  calc ‖Complex.log z‖ = ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I‖ := by rw [hdec]
    _ ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp
    _ ≤ |Real.log ‖z‖| + Real.pi := by
        have := Complex.abs_arg_le_pi z
        linarith

theorem asymp {ψ : ℂ → ℂ} {ξ : ℝ} {a b : ℂ}
    (h : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ MandelDim.QLeft ξ, R < ‖w‖ →
      ‖MandelDim.tau0 (ψ w) - (w + a * Complex.log (-w) + b)‖ < ε) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
      (∀ z : ℂ, z ∈ MandelDim.QLeft ξ → η / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * η →
        ‖MandelDim.tau0 (ψ z) - z‖ ≤ ‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1) ∧
      10 * (‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1) < (2 / 5) * η ∧
      ‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1 ≤ η / 80 := by
  obtain ⟨R, hR⟩ := h 1 one_pos
  -- The threshold is the maximum of: `2R+1` (so that `R < |z|` on the annulus),
  -- `1` (so that `η > 0`), `2(320‖a‖)²+1` (so that `‖a‖ log(2η) ≤ η/160`)
  -- and `160B+1` with `B = ‖a‖π + ‖b‖ + 1` (so that `B ≤ η/160`).
  let η₁ : ℝ := max (2 * R + 1) (max 1 (max (2 * (320 * ‖a‖) ^ 2 + 1) (160 * (‖a‖ * Real.pi + ‖b‖ + 1) + 1)))
  refine ⟨η₁, ?_, ?_⟩
  · have h1 : (1:ℝ) ≤ η₁ := by
      simp only [η₁]
      exact le_trans (le_max_left 1 _) (le_max_right (2 * R + 1) _)
    linarith
  · intro η hη
    have hηR : 2 * R + 1 ≤ η := le_trans (le_max_left _ _) hη
    have hη1 : (1:ℝ) ≤ η := le_trans (le_trans (le_max_left 1 _) (le_max_right (2 * R + 1) _)) hη
    have hηA : 2 * (320 * ‖a‖) ^ 2 + 1 ≤ η :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right (1:ℝ) _) (le_max_right (2 * R + 1) _))) hη
    have hηB : 160 * (‖a‖ * Real.pi + ‖b‖ + 1) + 1 ≤ η :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right (1:ℝ) _) (le_max_right (2 * R + 1) _))) hη
    have hηpos : 0 < η := lt_of_lt_of_le zero_lt_one hη1
    -- ## The elementary inequality `‖a‖ log(2η) + B ≤ η/80`
    have h3 : ‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1 ≤ η / 80 := by
      have hA : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
      -- `log x ≤ 2√x`
      have hlog : Real.log (2 * η) ≤ 2 * Real.sqrt (2 * η) := by
        have h := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 * η by positivity) (show (0:ℝ) < 1 / 2 by norm_num)
        have h2' : (2 * η) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt (2 * η) := by
          rw [Real.sqrt_eq_rpow]; ring
        linarith
      have hsq : Real.sqrt ((320 * ‖a‖) ^ 2 * (2 * η)) = 320 * ‖a‖ * Real.sqrt (2 * η) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      -- `320‖a‖√(2η) ≤ η` because `2(320‖a‖)² < η`
      have key : 320 * ‖a‖ * Real.sqrt (2 * η) ≤ η := by
        rw [← hsq, Real.sqrt_le_left (le_of_lt hηpos)]
        have h320 : 2 * (320 * ‖a‖) ^ 2 < η := by linarith
        have h2 := mul_le_mul_of_nonneg_right (le_of_lt h320) (le_of_lt hηpos)
        nlinarith [h2]
      have hs : ‖a‖ * (2 * Real.sqrt (2 * η)) ≤ η / 160 := by linarith
      have hAlog : ‖a‖ * Real.log (2 * η) ≤ ‖a‖ * (2 * Real.sqrt (2 * η)) :=
        mul_le_mul_of_nonneg_left hlog hA
      have hB : ‖a‖ * Real.pi + ‖b‖ + 1 ≤ η / 160 := by linarith
      linarith
    have h2 : 10 * (‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1) < (2 / 5) * η := by
      have := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ 10 by norm_num)
      linarith
    refine ⟨?_, h2, h3⟩
    -- ## The quantitative bound on the annulus
    intro z hzmem hz1 hz2
    have hRz : R < ‖z‖ := by linarith
    have hclose : ‖MandelDim.tau0 (ψ z) - (z + a * Complex.log (-z) + b)‖ < 1 := hR z hzmem hRz
    have hzpos : 0 < ‖z‖ := by linarith
    have hlogz : |Real.log ‖z‖| ≤ Real.log (2 * η) := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have hmul : Real.log (‖z‖ * (2 * η)) = Real.log ‖z‖ + Real.log (2 * η) :=
          Real.log_mul (ne_of_gt hzpos) (by positivity)
        have hge : 0 ≤ Real.log (‖z‖ * (2 * η)) := by
          apply Real.log_nonneg; nlinarith [hz1, hη1]
        linarith
      · exact Real.log_le_log hzpos hz2
    have hlogb : ‖Complex.log (-z)‖ ≤ Real.log (2 * η) + Real.pi := by
      calc ‖Complex.log (-z)‖ ≤ |Real.log ‖-z‖| + Real.pi := norm_log_le (-z)
        _ = |Real.log ‖z‖| + Real.pi := by rw [norm_neg]
        _ ≤ Real.log (2 * η) + Real.pi := by linarith
    calc ‖MandelDim.tau0 (ψ z) - z‖
        = ‖(MandelDim.tau0 (ψ z) - (z + a * Complex.log (-z) + b)) + ((z + a * Complex.log (-z) + b) - z)‖ := by congr 1; ring
      _ ≤ ‖MandelDim.tau0 (ψ z) - (z + a * Complex.log (-z) + b)‖ + ‖(z + a * Complex.log (-z) + b) - z‖ := norm_add_le _ _
      _ ≤ 1 + (‖a‖ * ‖Complex.log (-z)‖ + ‖b‖) := by
          have h1 := le_of_lt hclose
          have h2 : ‖(z + a * Complex.log (-z) + b) - z‖ ≤ ‖a‖ * ‖Complex.log (-z)‖ + ‖b‖ := by
            rw [show (z + a * Complex.log (-z) + b) - z = a * Complex.log (-z) + b by ring]
            calc ‖a * Complex.log (-z) + b‖ ≤ ‖a * Complex.log (-z)‖ + ‖b‖ := norm_add_le _ _
              _ = ‖a‖ * ‖Complex.log (-z)‖ + ‖b‖ := by rw [norm_mul]
          linarith
      _ ≤ 1 + (‖a‖ * (Real.log (2 * η) + Real.pi) + ‖b‖) := by
          have := mul_le_mul_of_nonneg_left hlogb (norm_nonneg a)
          linarith
      _ = ‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1 := by ring

end Work.PertU
