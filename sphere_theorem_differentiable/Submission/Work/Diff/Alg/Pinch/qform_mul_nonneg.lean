import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Frobenius pairing of two positive semidefinite quadratic forms is nonnegative

For two symmetric `(0,2)`-tensors `M`, `B` on `ℝⁿ` whose quadratic forms
`w ↦ qform M w = ∑ᵢⱼ Mᵢⱼ wᵢwⱼ` and `w ↦ qform B w` are nonnegative, the entrywise
(Frobenius) pairing `∑ᵢⱼ Mᵢⱼ Bᵢⱼ = tr(M · B)` is nonnegative.

The proof recognises `M` and `B` as positive semidefinite matrices
(`Matrix.PosSemidef`, via `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` and the
identity `star w ⬝ᵥ (M *ᵥ w) = qform M w`) and applies the Schur product theorem
(`Matrix.PosSemidef.hadamard`): the Hadamard product `M ⊙ B` is positive semidefinite,
and pairing it with the all-ones vector `w = 1` gives `∑ᵢⱼ MᵢⱼBᵢⱼ ≥ 0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Matrix

variable {n : ℕ}

/-- The quadratic form of a `(0,2)`-tensor is the `dotProduct` against `M *ᵥ v`. -/
lemma star_dotProduct_mulVec_eq_qform (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    star v ⬝ᵥ (M *ᵥ v) = qform M v := by
  simp only [star_trivial, dotProduct, mulVec, qform]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- A symmetric `(0,2)`-tensor with nonnegative quadratic form is positive semidefinite. -/
lemma posSemidef_of_qform_nonneg {M : Fin n → Fin n → ℝ} (hMsym : ∀ i j, M i j = M j i)
    (hM : ∀ w : Fin n → ℝ, 0 ≤ qform M w) : Matrix.PosSemidef M := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial]
    exact hMsym j i
  · intro x
    rw [star_dotProduct_mulVec_eq_qform]
    exact hM x

theorem qform_mul_nonneg (n : ℕ) {M B : Fin n → Fin n → ℝ} (hMsym : ∀ i j, M i j = M j i)
    (hBsym : ∀ i j, B i j = B j i) (hM : ∀ w : Fin n → ℝ, 0 ≤ Work.Diff.Alg.Pinch.qform M w)
    (hB : ∀ w : Fin n → ℝ, 0 ≤ Work.Diff.Alg.Pinch.qform B w) :
    0 ≤ ∑ i, ∑ j, M i j * B i j := by
  have hMpsd := posSemidef_of_qform_nonneg hMsym hM
  have hBpsd := posSemidef_of_qform_nonneg hBsym hB
  have h := (Matrix.PosSemidef.hadamard hMpsd hBpsd).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard, star_trivial] using h

end Work.Diff.Alg.Pinch
