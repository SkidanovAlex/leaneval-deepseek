import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Interp.support_sum_degree_le

namespace Work.WilkiesH.Interp

theorem v2_support_sum_le {μ d Q : ℕ} (P : MvPolynomial (Fin (μ + 1)) ℤ)
    (hdeg : P.totalDegree ≤ d) (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (Q : ℤ)) :
    (∑ m ∈ (P.map (Int.castRingHom ℝ)).support, |(P.map (Int.castRingHom ℝ)).coeff m|)
      ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) := by
  classical
  -- Write `P'` for the real polynomial obtained by casting the integer coefficients.
  set P' : MvPolynomial (Fin (μ + 1)) ℝ := P.map (Int.castRingHom ℝ) with hP'
  -- The support does not grow under `map`, and the coefficients are the casts of those of `P`.
  have hsub : P'.support ⊆ P.support := by
    rw [hP']; exact MvPolynomial.support_map_subset _ _
  have hterm : ∀ m ∈ P'.support, |P'.coeff m| ≤ (Q : ℝ) := by
    intro m hm
    have hm' : m ∈ P.support := hsub hm
    rw [hP', MvPolynomial.coeff_map]
    change |((P.coeff m : ℤ) : ℝ)| ≤ (Q : ℝ)
    rw [← Int.cast_abs]
    exact_mod_cast hcoef m hm'
  calc ∑ m ∈ P'.support, |P'.coeff m|
      ≤ ∑ _m ∈ P'.support, (Q : ℝ) := Finset.sum_le_sum hterm
    _ = (P'.support.card : ℝ) * (Q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (Q : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg Q)
        exact_mod_cast le_trans (Finset.card_le_card hsub)
          (Work.WilkiesH.Interp.card_support_le P hdeg)

end Work.WilkiesH.Interp
