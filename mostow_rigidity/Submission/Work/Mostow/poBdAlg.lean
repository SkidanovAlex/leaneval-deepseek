import Mathlib
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

/-- The boundary action `bdO` is a group action of `O(n,1)` on the boundary sphere:
it maps `Sph n` into itself, is insensitive to `A ↦ -A`, is multiplicative on the sphere,
and the identity acts trivially. -/
theorem poBdAlg (n : ℕ) :
    (∀ (A : O1 n) (ξ : E n), ξ ∈ Sph n → bdO A ξ ∈ Sph n) ∧
    (∀ (A : O1 n) (ξ : E n), bdO (-A) ξ = bdO A ξ) ∧
    (∀ (A B : O1 n) (ξ : E n), ξ ∈ Sph n → bdO (A * B) ξ = bdO A (bdO B ξ)) ∧
    (∀ ξ : E n, bdO (1 : O1 n) ξ = ξ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `bdO A` maps the sphere into itself
    intro A ξ hξ
    rw [mem_Sph_iff]
    have ht : (mat A *ᵥ theta ξ) (Sum.inr 0) ≠ 0 := mat_mulVec_theta_ne_zero A hξ
    have hnn : (∑ i, (mat A *ᵥ theta ξ) (Sum.inl i) ^ 2) =
        (mat A *ᵥ theta ξ) (Sum.inr 0) ^ 2 := by
      have h := mat_mulVec_theta_mform A ξ
      rw [theta_mform_self hξ, mform_self_apply] at h
      linarith
    have hsum : ∑ i, (bdO A ξ i) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [bdO_apply, div_pow])]
      rw [← Finset.sum_div, hnn]
      exact div_self (pow_ne_zero 2 ht)
    have h1 : ‖bdO A ξ‖ ^ 2 = 1 := by rw [norm_sq_eq_sum, hsum]
    nlinarith [norm_nonneg (bdO A ξ)]
  · -- `bdO` only depends on the class of `A` in `PO(n,1)`
    intro A ξ
    simp only [bdO, mat_neg, Matrix.neg_mulVec, Pi.neg_apply, neg_div_neg_eq]
  · -- multiplicativity of `bdO` on the boundary sphere
    intro A B ξ hξ
    have hne : (mat B *ᵥ theta ξ) (Sum.inr 0) ≠ 0 := mat_mulVec_theta_ne_zero B hξ
    have hw : mat B *ᵥ theta ξ = (mat B *ᵥ theta ξ) (Sum.inr 0) • theta (bdO B ξ) :=
      smul_theta_of_time_ne_zero _ hne
    ext i
    rw [bdO_apply, bdO_apply, mat_mul, ← Matrix.mulVec_mulVec (theta ξ) (mat A) (mat B),
      hw, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hne]
  · -- the identity acts trivially
    intro ξ
    simp [bdO, mat_one, Matrix.one_mulVec]

end Work.Mostow
