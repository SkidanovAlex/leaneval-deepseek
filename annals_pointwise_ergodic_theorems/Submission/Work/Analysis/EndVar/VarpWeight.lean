import Mathlib
import Submission.Work.Analysis.EndVar.Varp

/-!
# Finiteness of the geometric weight of the §5 summation

The §5 assembly of the major arc part (`majorArcVarEstimate_of_varp`) has to sum the gains
`2^{-c·lmax(l₁,l₂,k₁,k₂)}` of Theorem `varp` over the four indices `l₁,l₂,k₁,k₂ ∈ ℕ`.  This
module proves that the resulting weight is finite: the level `lmax` dominates a quarter of the sum
of the four indices, so the quadruple sum of the gains is bounded by a fourth power of the
geometric series `∑_n (2^{-c/4})^n`, hence finite for every `c > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems

/-- `2^{-(c/4)m} = (2^{-c/4})^m`, in the form used for the geometric weights. -/
private lemma rpow_quarter_eq (c : ℝ) (m : ℕ) :
    (2 : ℝ) ^ (-(c / 4) * (m : ℝ)) = ((2 : ℝ) ^ (-(c / 4))) ^ m := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(c / 4))) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The level `lmax` dominates a quarter of the sum of the four indices. -/
private lemma lmax_ge_quarter (l₁ l₂ k₁ k₂ : ℕ) :
    ((l₁ : ℝ) + l₂ + k₁ + k₂)
      ≤ 4 * (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ) := by
  have h1 : (l₁ : ℝ) ≤ (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ) := by
    have h : (l₁ : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      simp only [lmax]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast h
  have h2 : (l₂ : ℝ) ≤ (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ) := by
    have h : (l₂ : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      simp only [lmax]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast h
  have h3 : (k₁ : ℝ) ≤ (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ) := by
    have h : (k₁ : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      simp only [lmax]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact_mod_cast h
  have h4 : (k₂ : ℝ) ≤ (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ) := by
    have h : (k₂ : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      simp only [lmax]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact_mod_cast h
  linarith

/-- Pointwise comparison of the §5 weight with the product of four geometric weights. -/
private lemma ofReal_lmax_le {c : ℝ} (hc : 0 < c) (l₁ l₂ k₁ k₂ : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(c * (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ))))
      ≤ (ENNReal.ofReal (((2 : ℝ) ^ (-(c / 4))) ^ l₁)
          * ENNReal.ofReal (((2 : ℝ) ^ (-(c / 4))) ^ l₂))
        * (ENNReal.ofReal (((2 : ℝ) ^ (-(c / 4))) ^ k₁)
            * ENNReal.ofReal (((2 : ℝ) ^ (-(c / 4))) ^ k₂)) := by
  set ρ : ℝ := (2 : ℝ) ^ (-(c / 4)) with hρdef
  have hquarter := lmax_ge_quarter l₁ l₂ k₁ k₂
  have hexp : -(c * (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ))
      ≤ -(c / 4) * ((l₁ : ℝ) + l₂ + k₁ + k₂) := by nlinarith [hquarter, hc]
  have hsplit : (2 : ℝ) ^ (-(c / 4) * ((l₁ : ℝ) + l₂ + k₁ + k₂))
      = ρ ^ l₁ * ρ ^ l₂ * ρ ^ k₁ * ρ ^ k₂ := by
    have hcast : ((l₁ : ℝ) + l₂ + k₁ + k₂) = ((l₁ + l₂ + k₁ + k₂ : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, rpow_quarter_eq c (l₁ + l₂ + k₁ + k₂), pow_add, pow_add, pow_add]
  have hstep : (2 : ℝ) ^ (-(c * (((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ)))
      ≤ ρ ^ l₁ * ρ ^ l₂ * ρ ^ k₁ * ρ ^ k₂ :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp).trans (le_of_eq hsplit)
  refine (ENNReal.ofReal_le_ofReal hstep).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  simp only [mul_assoc]

/-- **Finiteness of the §5 geometric weight.**  For every `c > 0` the quadruple sum of the gains
`2^{-c·lmax(l₁,l₂,k₁,k₂)}` is finite. -/
theorem tsum_rpow_lmax_lt_top {c : ℝ} (hc : 0 < c) :
    (∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
      ENNReal.ofReal
        ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ))))) < ⊤ := by
  set ρ : ℝ := (2 : ℝ) ^ (-(c / 4)) with hρdef
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρlt : ρ < 1 := by
    rw [hρdef, Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hsum : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρpos.le hρlt
  have hGtop : (∑' n : ℕ, ENNReal.ofReal (ρ ^ n)) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hρpos.le n) hsum]
    exact ENNReal.ofReal_lt_top
  calc (∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ)))))
      ≤ ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
          (ENNReal.ofReal (ρ ^ l₁) * ENNReal.ofReal (ρ ^ l₂))
            * (ENNReal.ofReal (ρ ^ k₁) * ENNReal.ofReal (ρ ^ k₂)) :=
        ENNReal.tsum_le_tsum (fun l₁ =>
          ENNReal.tsum_le_tsum (fun l₂ =>
            ENNReal.tsum_le_tsum (fun k₁ =>
              ENNReal.tsum_le_tsum (fun k₂ => ofReal_lmax_le hc l₁ l₂ k₁ k₂))))
    _ = ((∑' n : ℕ, ENNReal.ofReal (ρ ^ n)) * (∑' n : ℕ, ENNReal.ofReal (ρ ^ n)))
          * ((∑' n : ℕ, ENNReal.ofReal (ρ ^ n)) * (∑' n : ℕ, ENNReal.ofReal (ρ ^ n))) := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hGtop hGtop)
        (ENNReal.mul_lt_top hGtop hGtop)

end

end Work.Analysis.EndVar
