/-
# `Submission.Work.FIArea7.PiPairSum` — the `(b,e)`-summation of the pair-mass assembly

The assembly of `uniMode_pairMass_le` sums `(1/b)·ρ(ρ/(4be)+1)` over `b ≤ uniB Pa`, `e ≤ X`.  The
classical evaluation is

  `Σ_{b,e} (1/b)·ρ(ρ/(4be)+1) = (ρ²/4)(Σ_b 1/b²)(Σ_e 1/e) + ρ·X·Σ_b 1/b
     ≤ ρ²(1+log X)/2 + ρ(1+log B)X`,

using `Σ_{b≤B} 1/b² ≤ 2` (`Work.FIArea7.sum_Icc_one_div_sq_le_two`) and `Σ_{b≤B} 1/b ≤ 1+log B`.
-/
import Mathlib
import Submission.Work.FIArea7.pairTheta_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `∑_{b ≤ B} 1/b ≤ 1 + log B`. -/
lemma harmonic_Icc_le (B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, ((b : ℝ))⁻¹) ≤ 1 + Real.log B := by
  have h := harmonic_le_one_add_log B
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- The `(b,e)`-summation of the pair mass: `Σ_{b ≤ B}Σ_{e ≤ X}(1/b)·ρ(ρ/(4be)+1)`. -/
lemma sum_be_bound (B X : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (r * (r / (4 * (b : ℝ) * (e : ℝ)) + 1)))
      ≤ r ^ 2 * (1 + Real.log X) / 2 + r * (1 + Real.log B) * X := by
  have key : ∀ b ∈ Finset.Icc 1 B, ∀ e ∈ Finset.Icc 1 X,
      (1 / (b : ℝ)) * (r * (r / (4 * (b : ℝ) * (e : ℝ)) + 1))
        = r ^ 2 * ((1 / (b : ℝ) ^ 2) * (1 / (e : ℝ))) / 4 + r * (1 / (b : ℝ)) := by
    intro b hb e he
    have hb0 : (b : ℝ) ≠ 0 := by
      have : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      positivity
    have he0 : (e : ℝ) ≠ 0 := by
      have : 1 ≤ e := (Finset.mem_Icc.mp he).1
      positivity
    field_simp
  have hsplit : (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (r * (r / (4 * (b : ℝ) * (e : ℝ)) + 1)))
      = (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X,
          r ^ 2 * ((1 / (b : ℝ) ^ 2) * (1 / (e : ℝ))) / 4)
        + (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X, r * (1 / (b : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e he => key b hb e he)
  have h1 : (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X,
        r ^ 2 * ((1 / (b : ℝ) ^ 2) * (1 / (e : ℝ))) / 4)
      = r ^ 2 / 4 * ((∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ) ^ 2)
          * (∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ))) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have h2 : (∑ b ∈ Finset.Icc 1 B, ∑ e ∈ Finset.Icc 1 X, r * (1 / (b : ℝ)))
      = r * ((∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ)) * X) := by
    have hX : (X : ℝ) = ∑ _e ∈ Finset.Icc 1 X, (1 : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have : X + 1 - 1 = X := by omega
      rw [this, mul_one]
    conv_rhs => rw [hX]
    rw [Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have hb2 : (∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ) ^ 2) ≤ 2 := sum_Icc_one_div_sq_le_two B
  have he1 : (∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ)) ≤ 1 + Real.log X := by
    simpa only [one_div] using harmonic_Icc_le X
  have hb1 : (∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ)) ≤ 1 + Real.log B := by
    simpa only [one_div] using harmonic_Icc_le B
  rw [hsplit, h1, h2]
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hlogX0 : 0 ≤ 1 + Real.log X := by
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX; simp
    · have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
      linarith
  have hlogB0 : 0 ≤ 1 + Real.log B := by
    rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB; simp
    · have : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
      linarith
  have hstep1 : r ^ 2 / 4 * ((∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ) ^ 2)
        * (∑ e ∈ Finset.Icc 1 X, 1 / (e : ℝ)))
      ≤ r ^ 2 / 4 * (2 * (1 + Real.log X)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hb2 he1 (by positivity) (by norm_num)
  have hstep2 : r * ((∑ b ∈ Finset.Icc 1 B, 1 / (b : ℝ)) * X)
      ≤ r * ((1 + Real.log B) * X) := by
    apply mul_le_mul_of_nonneg_left _ hr
    exact mul_le_mul_of_nonneg_right hb1 hX0
  linarith

end

end Work.FIArea7
