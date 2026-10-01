import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.divisorsCardLeTwoSqrt
import Submission.Work.ZeroDensity.Ingham.tsumIteExpNegDivTail
import Submission.Work.ZeroDensity.Ingham.expNegLogSqLeInvPow
import Submission.Work.ZeroDensity.Ingham.farTailNumericBound

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- Norm bound for a single term of the far tail of the detector sum: for `1 ≤ n`, `1/2 ≤ Re ρ`,
`‖a_K(n) n^{-ρ} e^{-n/Y}‖ ≤ 2 e^{-n/Y}`.  Uses `‖a_K(n)‖ ≤ τ(n) ≤ 2√n` and `√n · n^{-Re ρ} ≤ 1`. -/
lemma norm_term_le (K n : ℕ) (Y : ℝ) (ρ : ℂ) (hn : 1 ≤ n) (hρ : 1 / 2 ≤ ρ.re) :
    ‖mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖
      ≤ 2 * Real.exp (-(n : ℝ) / Y) := by
  have hn0 : (0 : ℕ) < n := hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hτ : ‖mCoef K n‖ ≤ 2 * Real.sqrt (n : ℝ) :=
    le_trans (norm_mCoef_le_tau K n) (divisorsCardLeTwoSqrt n)
  have hcpow : ‖(n : ℂ) ^ (-ρ)‖ = (n : ℝ) ^ (-ρ.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have hexp : ‖Complex.exp (-(n : ℂ) / Y)‖ = Real.exp (-(n : ℝ) / Y) := by
    rw [Complex.norm_exp]
    congr 1
    rw [show (-(n : ℂ) / Y) = (((-(n : ℝ) / Y)) : ℝ) from by
          rw [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast]]
    simp
  have hsqrt : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-ρ.re) ≤ 1 := by
    have hsq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
    rw [hsq]
    have h1 : (n : ℝ) ^ (-ρ.re) ≤ (n : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have h2 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← Real.rpow_add hnRpos]
      norm_num
    calc (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-ρ.re)
        ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by linarith) _)
      _ = 1 := h2
  calc ‖mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖
      = ‖mCoef K n‖ * ‖(n : ℂ) ^ (-ρ)‖ * ‖Complex.exp (-(n : ℂ) / Y)‖ := by
        rw [norm_mul, norm_mul]
    _ = ‖mCoef K n‖ * (n : ℝ) ^ (-ρ.re) * Real.exp (-(n : ℝ) / Y) := by
        rw [hcpow, hexp]
    _ ≤ (2 * Real.sqrt (n : ℝ)) * (n : ℝ) ^ (-ρ.re) * Real.exp (-(n : ℝ) / Y) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right hτ
          exact Real.rpow_nonneg (by linarith) _
        · exact Real.exp_nonneg _
    _ = 2 * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-ρ.re)) * Real.exp (-(n : ℝ) / Y) := by ring
    _ ≤ 2 * 1 * Real.exp (-(n : ℝ) / Y) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        · exact Real.exp_nonneg _
    _ = 2 * Real.exp (-(n : ℝ) / Y) := by ring

/-- The discarded far tail of the detector sum is small. -/
theorem detFarTailSmall : ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
    ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T → 1 ≤ Y → Y ≤ T ^ 2 →
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ ≤ 1 / 20 := by
  refine ⟨Real.exp 6, ?_, ?_⟩
  · have h : (6 : ℝ) + 1 ≤ Real.exp 6 := Real.add_one_le_exp 6
    linarith
  · intro A hA T hT K Y hK1 hKT hY1 hYT2 ρ hρ1 hρ2 hρim
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (A * T) := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = Y * L ^ 2 := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Z⌋₊ := ⟨_, rfl⟩
    have hZL : Y * (Real.log (A * T)) ^ 2 = Z := by rw [hZ, hL]
    have hApos : (0 : ℝ) < A := lt_of_lt_of_le (Real.exp_pos 6) hA
    have hTpos : (0 : ℝ) < T := by linarith
    have hYpos : (0 : ℝ) < Y := by linarith
    have hfar : ‖detFarTail K Y Z ρ‖ ≤ 2 * (Y + 1) * Real.exp (-(M : ℝ) / Y) := by
      rw [detFarTail, ← hM]
      have hexpr : (fun n : ℕ => Real.exp (-(n : ℝ) / Y))
          = (fun n : ℕ => Real.exp (-(1 / Y)) ^ n) := by
        funext n
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hnorm_lt : ‖Real.exp (-(1 / Y))‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
        have : (0 : ℝ) < 1 / Y := by positivity
        linarith
      have hexpsum : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / Y)) := by
        rw [hexpr]
        exact summable_geometric_iff_norm_lt_one.mpr hnorm_lt
      have h2sum : Summable (fun n : ℕ => 2 * Real.exp (-(n : ℝ) / Y)) :=
        hexpsum.mul_left 2
      have hf_le_g : ∀ n : ℕ,
          ‖(if M < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)
              else 0)‖
            ≤ (if M < n then 2 * Real.exp (-(n : ℝ) / Y) else 0) := by
        intro n
        by_cases h : M < n
        · rw [if_pos h, if_pos h]
          exact norm_term_le K n Y ρ (by omega) hρ1
        · rw [if_neg h, if_neg h]
          simp
      have hf_le_full : ∀ n : ℕ,
          ‖(if M < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)
              else 0)‖
            ≤ 2 * Real.exp (-(n : ℝ) / Y) := by
        intro n
        by_cases h : M < n
        · rw [if_pos h]
          exact norm_term_le K n Y ρ (by omega) hρ1
        · rw [if_neg h]
          simp only [norm_zero]
          positivity
      have hgsum : Summable (fun n : ℕ => (if M < n then 2 * Real.exp (-(n : ℝ) / Y) else 0)) := by
        refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h2sum
        · by_cases h : M < n
          · rw [if_pos h]; positivity
          · rw [if_neg h]
        · by_cases h : M < n
          · rw [if_pos h]
          · rw [if_neg h]; positivity
      have hfsum : Summable
          (fun n : ℕ => (if M < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y) else 0)) :=
        Summable.of_norm_bounded h2sum hf_le_full
      calc ‖∑' n, (if M < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y) else 0)‖
          ≤ ∑' n, ‖(if M < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y) else 0)‖ :=
            norm_tsum_le_tsum_norm hfsum.norm
        _ ≤ ∑' n, (if M < n then 2 * Real.exp (-(n : ℝ) / Y) else 0) :=
            Summable.tsum_le_tsum hf_le_g hfsum.norm hgsum
        _ ≤ 2 * (Y + 1) * Real.exp (-(M : ℝ) / Y) :=
            tsumIteExpNegDivTail Y hYpos M 2 (by norm_num)
    have hlogA : 6 ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos 6) hA
      rwa [Real.log_exp] at h
    have hLmul : L = Real.log A + Real.log T := by
      rw [hL, Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)]
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hLge : 6 + Real.log T ≤ L := by rw [hLmul]; linarith
    have hL2 : 12 * Real.log T ≤ L ^ 2 := by
      have hnn : (0 : ℝ) ≤ 6 + Real.log T := by linarith
      have hsq : (6 + Real.log T) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hnn hLge 2
      have h36 : 12 * Real.log T ≤ (6 + Real.log T) ^ 2 := by
        nlinarith [sq_nonneg (Real.log T)]
      linarith
    have hYinv : 1 / Y ≤ 1 := by
      rw [div_le_iff₀ hYpos]; linarith
    have hML : L ^ 2 - 1 ≤ (M : ℝ) / Y := by
      have h1 : Z - 1 < (M : ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor Z
      have h2 : (Z - 1) / Y < (M : ℝ) / Y := div_lt_div_of_pos_right h1 hYpos
      have h3 : (Z - 1) / Y = L ^ 2 - 1 / Y := by
        rw [hZ, sub_div, mul_div_cancel_left₀ (L ^ 2) (ne_of_gt hYpos)]
      have h4 : L ^ 2 - 1 ≤ (Z - 1) / Y := by rw [h3]; linarith
      linarith
    have hexpM : Real.exp (-(M : ℝ) / Y) ≤ Real.exp 1 * Real.exp (-(L ^ 2)) := by
      have h : -(M : ℝ) / Y ≤ 1 - L ^ 2 := by
        have h2 := neg_le_neg hML
        simp only [neg_sub] at h2
        rwa [neg_div]
      calc Real.exp (-(M : ℝ) / Y) ≤ Real.exp (1 - L ^ 2) := Real.exp_le_exp.mpr h
        _ = Real.exp 1 * Real.exp (-(L ^ 2)) := by
              rw [show (1 : ℝ) - L ^ 2 = 1 + (-(L ^ 2)) by ring, Real.exp_add]
    have hfinal : 2 * (Y + 1) * Real.exp (-(M : ℝ) / Y)
        ≤ 2 * (Y + 1) * Real.exp 1 * Real.exp (-(L ^ 2)) := by
      have h1 : (0 : ℝ) ≤ 2 * (Y + 1) := by positivity
      calc 2 * (Y + 1) * Real.exp (-(M : ℝ) / Y)
          ≤ 2 * (Y + 1) * (Real.exp 1 * Real.exp (-(L ^ 2))) :=
            mul_le_mul_of_nonneg_left hexpM h1
        _ = 2 * (Y + 1) * Real.exp 1 * Real.exp (-(L ^ 2)) := by ring
    have hexpL : Real.exp (-(L ^ 2)) ≤ 1 / T ^ 12 := by
      rw [hL]
      exact expNegLogSqLeInvPow hA hT
    calc ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
        = ‖detFarTail K Y Z ρ‖ := by rw [hZL]
      _ ≤ 2 * (Y + 1) * Real.exp (-(M : ℝ) / Y) := hfar
      _ ≤ 2 * (Y + 1) * Real.exp 1 * Real.exp (-(L ^ 2)) := hfinal
      _ ≤ 2 * (Y + 1) * Real.exp 1 * (1 / T ^ 12) := by
            have h1 : (0 : ℝ) ≤ 2 * (Y + 1) * Real.exp 1 := by positivity
            exact mul_le_mul_of_nonneg_left hexpL h1
      _ ≤ 1 / 20 := farTailNumericBound hY1 hT hYT2

end Work.ZeroDensity.Ingham
