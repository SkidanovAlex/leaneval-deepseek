import Mathlib
import Submission.Grassmann.Homogeneous
import Submission.Grassmann.DictatorDual

/-!
# The dual combinatorial Laplacians `𝓔_{W'}` (arXiv:2209.04243, §5.6)

For a codimension-one subspace `W' ≤ W` (represented here by a nonzero vector
`w ∈ W`, with `W' = ker ⟨·, w⟩`) the paper defines the dual operator
`𝓔_{W'}[f] = (𝓔_φ[f*])*` where `f*` is the transpose of `f` and `φ` the functional
vanishing on `W'`.

We implement it as `eOpW w f = transposeFun (eOpV w (transposeFun f))` and derive its Fourier
formula: `𝓔_{W'}` keeps exactly the characters `X` with `w ∉ range (mulVecLin Xᵀ)` (equivalently
`ker X + W' = W`) and multiplies them by `2^{-rank X}`.
-/

open Matrix Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-- The dual combinatorial Laplacian `𝓔_{W'}`: the transpose of `𝓔_w` acting on the transpose
of `f`. -/
def eOpW {m n : ℕ} (w : Fin m → ZMod 2)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  transposeFun (eOpV w (transposeFun f))

/-- **The Fourier multiplier of the dual Laplacian** (Lemma 5.3, dual form): the character
`mchar X` is kept, with multiplier `2^{-rank X}`, unless `w ∈ range (mulVecLin Xᵀ)`,
equivalently unless `ker X + W' = W`. -/
theorem fhat_eOpW {m n : ℕ} (w : Fin m → ZMod 2) (hw : w ≠ 0)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (eOpW w f) X =
      (if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 0 else ((2 : ℂ) ^ X.rank)⁻¹) *
        fhat f X := by
  rw [eOpW, fhat_transposeFun, fhat_eOpV w hw (transposeFun f) Xᵀ, fhat_transposeFun,
    Matrix.rank_transpose, Matrix.transpose_transpose]

end

end Submission.Grassmann
