import Mathlib
import Submission.Work.SG.arithDefs

namespace Work.SG

/-- Conjugating an integer matrix by an invertible (unimodular) one preserves its trace. -/
theorem trace_conj_of_isUnit_det {U A : IMat} (hU : IsUnit U.det) :
    (U * A * U⁻¹).trace = A.trace := by
  rw [Matrix.trace_mul_comm (U * A) U⁻¹, ← mul_assoc, Matrix.nonsing_inv_mul U hU, one_mul]

/-- Conjugation `A ↦ U * A * U⁻¹` by a matrix with invertible determinant is injective. -/
theorem conj_injective_of_isUnit_det {U : IMat} (hU : IsUnit U.det) :
    Function.Injective (fun A : IMat => U * A * U⁻¹) := by
  have hcan : ∀ X : IMat, U⁻¹ * (U * X * U⁻¹) * U = X := by
    intro X
    rw [← mul_assoc U⁻¹ (U * X) U⁻¹, mul_assoc (U⁻¹ * (U * X)) U⁻¹ U,
      Matrix.nonsing_inv_mul_cancel_left U X hU, Matrix.nonsing_inv_mul U hU, mul_one]
  intro A B hAB
  have h2 := congrArg (fun X : IMat => U⁻¹ * X * U) hAB
  rwa [hcan A, hcan B] at h2

/-- Cardinality and trace power sums are invariant under conjugation by a unimodular integer
matrix.

`trPow P k = ∑ A ∈ P, A.trace ^ k` (defined in `Submission.Work.SG.arithRep_conj_eq`,
namespace `Work.SG`), and `A.trace` is Mathlib's `Matrix.trace`.

Suggested route: from `hU : IsUnit U.det` get `Matrix.nonsing_inv_mul U hU : U⁻¹ * U = 1` (and
`Matrix.mul_nonsing_inv`), show that `φ A := U * A * U⁻¹` is injective
(`U⁻¹ * (U * A * U⁻¹) * U = A`, via `Matrix.nonsing_inv_mul_cancel_left/right`), deduce
`P' = P.image φ` with `Finset.ext`, then use `Finset.card_image_of_injective` and
`Finset.sum_image` plus cyclicity of the trace (`Matrix.trace_mul_comm`) to conclude. -/
theorem trPow_card_conj {P P' : Finset IMat} {U : IMat} (hU : IsUnit U.det)
    (h : ∀ A, A ∈ P' ↔ ∃ B ∈ P, A = U * B * U⁻¹) (k : ℕ) :
    P'.card = P.card ∧ trPow P' k = trPow P k := by
  have hinj := conj_injective_of_isUnit_det hU
  have hP' : P' = P.image (fun A => U * A * U⁻¹) := by
    ext A
    rw [Finset.mem_image]
    constructor
    · intro hA
      obtain ⟨B, hB, hBA⟩ := (h A).mp hA
      exact ⟨B, hB, hBA.symm⟩
    · rintro ⟨B, hB, hBA⟩
      rw [← hBA]
      exact (h (U * B * U⁻¹)).mpr ⟨B, hB, rfl⟩
  have hcard : P'.card = P.card := by
    rw [hP', Finset.card_image_of_injective _ hinj]
  have hsum : trPow P' k = trPow P k := by
    rw [trPow, trPow, hP', Finset.sum_image (fun a _ b _ hab => hinj hab)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    exact trace_conj_of_isUnit_det (U := U) (A := x) hU
  exact ⟨hcard, hsum⟩

end Work.SG
