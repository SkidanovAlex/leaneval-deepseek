import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs

namespace Work.FIArea6Hecke.R

/-- Elementary lower bound for a single Euler factor of `axisBadPoly` on the half-strip
`1 ≤ σ ≤ 2`: each of the two sub-factors has norm at least `1/2`. -/
private lemma axisBadPoly_factor_lower_bound {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    (1/4 : ℝ) ≤
      ‖((1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ))) * (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)))‖ := by
  have hnorm : ‖(p : ℂ) ^ (-(σ : ℂ))‖ ≤ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < p), Complex.neg_re,
      Complex.ofReal_re]
    have h2 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ p))
      linarith
    rw [Real.rpow_neg_one] at h2
    have h3 : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp'
      simpa [one_div] using this
    linarith
  have h1' : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ))‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-(σ : ℂ)))
    simp only [norm_one] at this
    linarith
  have h2' : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))‖ := by
    have hb : ‖axisChi4 p * (p : ℂ) ^ (-(σ : ℂ))‖ ≤ (1 / 2 : ℝ) := by
      rw [norm_mul]
      calc ‖axisChi4 p‖ * ‖(p : ℂ) ^ (-(σ : ℂ))‖
            ≤ 1 * ‖(p : ℂ) ^ (-(σ : ℂ))‖ :=
              mul_le_mul_of_nonneg_right (axisChi4_norm_le_one p) (norm_nonneg _)
        _ = ‖(p : ℂ) ^ (-(σ : ℂ))‖ := one_mul _
        _ ≤ 1 / 2 := hnorm
    have := norm_sub_norm_le (1 : ℂ) (axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)))
    simp only [norm_one] at this
    linarith
  rw [norm_mul]
  nlinarith [h1', h2']

theorem axisBadPoly_lower_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      c ≤ ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖ := by
  refine ⟨(1 / 4) ^ (4 * d).primeFactors.card, by positivity, ?_⟩
  intro σ h1 h2
  have hσ : (1 : ℝ) ≤ σ := le_of_lt h1
  have hfac : ∀ p ∈ (4 * d).primeFactors,
      (1 / 4 : ℝ) ≤
        ‖((1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ))) * (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)))‖ :=
    fun p hp => axisBadPoly_factor_lower_bound
      (by have := (Nat.prime_of_mem_primeFactors hp).one_lt; omega) hσ
  rw [axisBadPoly, norm_prod]
  calc (1 / 4) ^ (4 * d).primeFactors.card
      = ∏ _p ∈ (4 * d).primeFactors, (1 / 4 : ℝ) := (Finset.prod_const (1 / 4)).symm
    _ ≤ ∏ p ∈ (4 * d).primeFactors,
          ‖((1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ))) * (1 - axisChi4 p * (p : ℂ) ^ (-(σ : ℂ)))‖ :=
        Finset.prod_le_prod₀ (fun _ _ => by norm_num) hfac

end Work.FIArea6Hecke.R
