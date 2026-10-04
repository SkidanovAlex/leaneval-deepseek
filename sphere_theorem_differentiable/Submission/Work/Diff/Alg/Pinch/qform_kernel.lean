import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The kernel of a positive semidefinite quadratic form

`qform M v = ∑ᵢⱼ M i j vᵢ vⱼ` is the quadratic form of a `(0,2)`-tensor `M`.  If `M` is symmetric
and this form is nonnegative everywhere, then its zero set is exactly the kernel of `M`:

`qform M v = 0 → M v = 0`  (componentwise: `∑ⱼ M i j vⱼ = 0` for every `i`).

This is the elementary fact behind every "tensor is zero on the null directions of its quadratic
form" argument; the proof goes through Mathlib's `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`.
-/

namespace Work.Diff.Alg.Pinch

open Finset

/-- `qform M v = ∑ᵢⱼ M i j vᵢ vⱼ` is the matrix quadratic form `v ⬝ᵥ (M *ᵥ v)`. -/
lemma qform_eq_dotProduct_mulVec (n : ℕ) (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform M v = dotProduct v (Matrix.mulVec M v) := by
  simp only [qform, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem qform_kernel (n : ℕ) {M : Fin n → Fin n → ℝ} (hMsym : ∀ i j, M i j = M j i)
    (hM : ∀ w : Fin n → ℝ, 0 ≤ Work.Diff.Alg.Pinch.qform M w) {v : Fin n → ℝ}
    (hv : Work.Diff.Alg.Pinch.qform M v = 0) : ∀ i, ∑ j, M i j * v j = 0 := by
  have hbridge : ∀ w : Fin n → ℝ, qform M w = dotProduct w (Matrix.mulVec M w) :=
    fun w => qform_eq_dotProduct_mulVec n M w
  have hHerm : Matrix.IsHermitian M := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simpa using (hMsym i j).symm
  have hPsd : Matrix.PosSemidef M := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun x => ?_)
    rw [star_trivial, ← hbridge x]
    exact hM x
  have hzero : Matrix.mulVec M v = 0 := by
    have hv' : star v ⬝ᵥ (Matrix.mulVec M v) = 0 := by
      rw [star_trivial, ← hbridge v]
      exact hv
    exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hPsd).mp hv'
  intro i
  have h := congrFun hzero i
  simp only [Pi.zero_apply] at h
  simpa [Matrix.mulVec, dotProduct] using h

end Work.Diff.Alg.Pinch
