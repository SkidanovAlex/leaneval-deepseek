import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- Elementary arithmetic gain: if `X ≥ lmax + R·2^{ρ·lmax} + 2 ≥ 2^{ρ·lmax}` (with `R ≥ 1`),
then `X^{-c/ρ} ≤ 2^{-(c/2)·lmax}`.  Indeed `X^{-c/ρ} ≤ (2^{ρ·lmax})^{-c/ρ} = 2^{-c·lmax}`,
and `2^{-c·lmax} ≤ 2^{-(c/2)·lmax}`. -/
theorem logTerm_le_gain (ρ : ℝ) (hρ : 0 < ρ) (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 1 ≤ R) :
    ∀ (lmax : ℕ) (X : ℝ), 1 ≤ X →
      (lmax : ℝ) + R * (2 : ℝ) ^ (ρ * (lmax : ℝ)) + 2 ≤ X →
      X ^ (-(c / ρ)) ≤ (2 : ℝ) ^ (-(c / 2 * (lmax : ℝ))) := by
  intro lmax X hX hXle
  have hlmax : (0 : ℝ) ≤ (lmax : ℝ) := Nat.cast_nonneg lmax
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (lmax : ℝ)) := Real.rpow_pos_of_pos h2pos _
  have hRpow : (2 : ℝ) ^ (ρ * (lmax : ℝ)) ≤ R * (2 : ℝ) ^ (ρ * (lmax : ℝ)) :=
    le_mul_of_one_le_left hpow_pos.le hR
  have hbase : (2 : ℝ) ^ (ρ * (lmax : ℝ)) ≤ X := by linarith
  have hexp : -(c / ρ) ≤ 0 := by
    have : 0 < c / ρ := div_pos hc hρ
    linarith
  have h1 : X ^ (-(c / ρ)) ≤ ((2 : ℝ) ^ (ρ * (lmax : ℝ))) ^ (-(c / ρ)) :=
    Real.rpow_le_rpow_of_nonpos hpow_pos hbase hexp
  have h2 : ((2 : ℝ) ^ (ρ * (lmax : ℝ))) ^ (-(c / ρ)) = (2 : ℝ) ^ (-(c * (lmax : ℝ))) := by
    rw [← Real.rpow_mul h2pos.le]
    congr 1
    field_simp
  have h3 : (2 : ℝ) ^ (-(c * (lmax : ℝ))) ≤ (2 : ℝ) ^ (-(c / 2 * (lmax : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have : c / 2 * (lmax : ℝ) ≤ c * (lmax : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith : c / 2 ≤ c) hlmax
    linarith
  calc X ^ (-(c / ρ)) ≤ ((2 : ℝ) ^ (ρ * (lmax : ℝ))) ^ (-(c / ρ)) := h1
    _ = (2 : ℝ) ^ (-(c * (lmax : ℝ))) := h2
    _ ≤ (2 : ℝ) ^ (-(c / 2 * (lmax : ℝ))) := h3

end Work.KMTPlan.A6
