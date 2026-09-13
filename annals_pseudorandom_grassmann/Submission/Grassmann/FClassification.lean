import Submission.Grassmann.XNormSum
import Submission.Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint

/-!
# The F₁/F₂ classification of pairs `Y + Z = X` (arXiv:2209.04243, `lem:F1`)

The Fourier expansion of `f²` is `\widehat{f²}(X) = Σ_{Y + Z = X} f̂(Y)f̂(Z)` (see
`Submission.Grassmann.Convolution`).  The paper's §4 splits the pairs `(Y,Z)` with `Y + Z = X`
into two classes:

* **`𝓕₁(X)`** (`IsF1`): pairs that split as `Y = Y' ⊕ X'`, `Z = Z' ⊕ (-X')` with `Y' ⊕ Z' = X`.
  For these the contribution behaves like a Fourier coefficient on the Boolean cube, and it is
  bounded by Bonami's lemma (`lem:F1helper`).
* **`𝓕₂(X)`** (`IsF2`): the remaining pairs, namely those for which
  `Im X ∩ Im Y ∩ Im Z ≠ 0` or `ker X + ker Y + ker Z ≠ W`.  These appear when expanding
  `\widehat{(L_{V₁} ∘ L_{W₁}[f])²}(X)` (`lem:F2helper`).

The main result of this file is `IsF1_or_IsF2`: the two classes cover everything, which is the
paper's `lem:F1`.  It is a direct corollary of the commons lemma
`Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint` (the linear-algebraic content of the
paper's proof).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The paper's `𝓕₁(X)`: pairs `(Y,Z)` with `Y + Z = X` that split as a direct sum of two maps
below `Y` and `Z` respectively. -/
def IsF1 {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Prop :=
  Y + Z = X ∧ ∃ Y' Z' : Matrix (Fin n) (Fin m) 𝔽₂,
    plLE Y' Y ∧ plLE Z' Z ∧ Y' + Z' = X

/-- The paper's `𝓕₂(X)`: pairs `(Y,Z)` with `Y + Z = X` whose images meet nontrivially or whose
kernels do not span `W`. -/
def IsF2 {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Prop :=
  Y + Z = X ∧
    (LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin ⊓
        LinearMap.range X.mulVecLin ≠ ⊥ ∨
      LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin ⊔
        LinearMap.ker X.mulVecLin ≠ ⊤)

/-- **`lem:F1` of arXiv:2209.04243**: every pair `(Y,Z)` with `Y + Z = X` lies in `𝓕₁(X)` or in
`𝓕₂(X)`.  This is the classification of the pairs appearing in the Fourier expansion
`\widehat{f²}(X) = Σ_{Y + Z = X} f̂(Y) f̂(Z)`. -/
theorem IsF1_or_IsF2 {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) (h : Y + Z = X) :
    IsF1 X Y Z ∨ IsF2 X Y Z := by
  by_cases h1 : LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin ⊓
      LinearMap.range X.mulVecLin = ⊥
  · by_cases h2 : LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin ⊔
        LinearMap.ker X.mulVecLin = ⊤
    · left
      obtain ⟨Y', Z', hY', hZ', hX⟩ :=
        Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint X Y Z h h1 h2
      exact ⟨h, Y', Z', hY', hZ', hX⟩
    · right; exact ⟨h, Or.inr h2⟩
  · right; exact ⟨h, Or.inl h1⟩



end

end Submission.Grassmann
