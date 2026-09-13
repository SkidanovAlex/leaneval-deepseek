import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Inequalities

open scoped BigOperators

/-- Hölder's inequality with conjugate exponents `4` and `4/3`, in the form needed by the
pseudorandom Grassmann project: the fourth power of `∑ ‖g i‖ * ‖h i‖` is bounded by the product of
`∑ ‖g i‖ ^ 4` and the cube of `∑ ‖h i‖ ^ (4/3)`. -/
theorem sum_norm_mul_pow_four_le {ι : Type*} (s : Finset ι) (g h : ι → ℂ) :
    (∑ i ∈ s, ‖g i‖ * ‖h i‖) ^ 4
      ≤ (∑ i ∈ s, ‖g i‖ ^ 4) * (∑ i ∈ s, ‖h i‖ ^ ((4 : ℝ) / 3)) ^ 3 := by
  have hpq : Real.HolderConjugate (4 : ℝ) ((4 : ℝ) / 3) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => ‖g i‖)
      (g := fun i => ‖h i‖) hpq (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
  set A := ∑ i ∈ s, ‖g i‖ * ‖h i‖ with hA
  set B := ∑ i ∈ s, ‖g i‖ ^ 4 with hB
  set C := ∑ i ∈ s, ‖h i‖ ^ ((4 : ℝ) / 3) with hC
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (norm_nonneg _) 4
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hholder' : A ≤ B ^ ((4 : ℝ)⁻¹) * C ^ ((3 : ℝ) / 4) := by
    have hB' : (∑ i ∈ s, ‖g i‖ ^ (4 : ℝ)) = B := by
      rw [hB]
      exact Finset.sum_congr rfl fun i _ => Real.rpow_natCast _ 4
    have hC' : (∑ i ∈ s, ‖h i‖ ^ ((4 : ℝ) / 3)) = C := hC.symm
    calc A = ∑ i ∈ s, ‖g i‖ * ‖h i‖ := hA
      _ ≤ (∑ i ∈ s, ‖g i‖ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) *
            (∑ i ∈ s, ‖h i‖ ^ ((4 : ℝ) / 3)) ^ (1 / ((4 : ℝ) / 3)) := hholder
      _ = B ^ ((4 : ℝ)⁻¹) * C ^ ((3 : ℝ) / 4) := by
            rw [hB', hC', show (1 : ℝ) / (4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
              show (1 : ℝ) / ((4 : ℝ) / 3) = (3 : ℝ) / 4 by norm_num]
  have hb : (B ^ ((4 : ℝ)⁻¹)) ^ 4 = B := Real.rpow_inv_natCast_pow hB0 (by norm_num)
  have hc : (C ^ ((3 : ℝ) / 4)) ^ 4 = C ^ (3 : ℝ) := by
    have h1 : C ^ ((3 : ℝ) / 4) = (C ^ (3 : ℝ)) ^ ((4 : ℝ)⁻¹) := by
      rw [show (3 : ℝ) / 4 = 3 * (4 : ℝ)⁻¹ by norm_num, Real.rpow_mul hC0]
    rw [h1]
    exact Real.rpow_inv_natCast_pow (x := C ^ (3 : ℝ)) (n := 4) (Real.rpow_nonneg hC0 3)
      (by norm_num)
  have hD : (B ^ ((4 : ℝ)⁻¹) * C ^ ((3 : ℝ) / 4)) ^ 4 = B * C ^ 3 := by
    rw [mul_pow, hb, hc]
    simp
  calc A ^ 4 ≤ (B ^ ((4 : ℝ)⁻¹) * C ^ ((3 : ℝ) / 4)) ^ 4 :=
        pow_le_pow_left₀ hA0 hholder' 4
    _ = B * C ^ 3 := hD

end Commons.Analysis.Inequalities