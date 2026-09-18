import ChallengeDeps
import Mathlib.Data.Nat.Totient
open scoped Nat ENNReal NNReal
open Set
open DuffinSchaefferConjecture

namespace Submission.DS

/-- `rad ψ q = sup {ψ(n)/n : n ∈ ℕ+, q ∣ n}` in `ℝ≥0∞` (mirrors `ψ_star`'s internal sup). -/
noncomputable def rad (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

lemma psiStar_eq_phi_mul_rad (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    ψ_star ψ q = (φ q : ℝ≥0∞) * rad ψ q := by
  rfl

lemma coe_div_ne_zero (a : ℝ≥0) (b : ℝ≥0) (hb : b ≠ 0) :
    ((a / b : ℝ≥0) : ℝ≥0∞) = (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
  exact ENNReal.coe_div hb

lemma rad_mem (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    (ψ q / q : ℝ≥0∞) ∈ {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n} := by
  refine ⟨q, dvd_rfl, ?_⟩
  -- ψ q / q as ENNReal division with q coerced
  rfl

lemma rad_ge_self (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ((ψ q / q : ℝ≥0) : ℝ≥0∞) ≤ rad ψ q := by
  unfold rad
  calc
    ((ψ q / q : ℝ≥0) : ℝ≥0∞) = (ψ q / q : ℝ≥0∞) := by
      exact ENNReal.coe_div (show (q : ℝ≥0) ≠ 0 by exact_mod_cast (show (q : ℕ) ≠ 0 from PNat.ne_zero q))
    _ ≤ sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n} := le_sSup (rad_mem ψ q)

lemma phi_ge_one (q : ℕ+) : (1 : ℝ≥0∞) ≤ (φ q : ℝ≥0∞) := by
  have h : 1 ≤ φ (q : ℕ) := by
    have h0 : 0 < φ (q : ℕ) := (Nat.totient_pos).mpr (by exact_mod_cast q.2 : 0 < (q : ℕ))
    omega
  exact_mod_cast h

lemma rad_le_psiStar (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : rad ψ q ≤ ψ_star ψ q := by
  rw [psiStar_eq_phi_mul_rad]
  have h1 : (1 : ℝ≥0∞) ≤ (φ q : ℝ≥0∞) := phi_ge_one q
  calc
    rad ψ q = (1 : ℝ≥0∞) * rad ψ q := by simp
    _ ≤ (φ q : ℝ≥0∞) * rad ψ q := by
      exact mul_le_mul' h1 le_rfl
    _ = ψ_star ψ q := by rw [psiStar_eq_phi_mul_rad]

end Submission.DS
