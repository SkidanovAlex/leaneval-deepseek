import Submission.Grassmann.Laplacian
import Submission.Commons.LinearAlgebra.Matrix.rank_sandwich_eq

/-!
# The hybrid Laplacians `L_{V₁,W₁}` and their derivatives

Fixing a subspace `V₁ ≤ V` (presented through a "quotient" matrix `Q`, `V₁ = ker Q`) and a
subspace `W₁ ≤ W` (presented through an "inclusion" matrix `ι`, `W₁ = range ι`), the paper's
*hybrid Laplacian* keeps the characters `u_X` with

  `Im X ⊇ V₁`  and  `X⁻¹(V₁) ⊆ W₁`,

and the corresponding *derivative* is `D_{V₁,W₁,T} = (Δ_T ∘ L_{V₁,W₁})` restricted to
`L(V/V₁, W₁)`, where `Δ_T` is the shift by `T`.

The main result is the **degree-reduction lemma** (arXiv:2209.04243, Lemma 3.6): if `f` has
degree at most `d` then `D_{V₁,W₁,T}[f]` has degree at most `d - i`, where
`i = dim V₁ + codim W₁` is the *order* of the Laplacian.  This is what drives the induction
on the degree in the proof of the conditional hypercontractive inequality.
-/

open Matrix Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-- The Fourier-multiplier predicate of the hybrid Laplacian `L_{V₁,W₁}`: keep `u_X` when
`Im X ⊇ V₁ = ker Q` and `X⁻¹(V₁) ⊆ W₁ = range ι`. -/
def hybridPred {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (X : Matrix (Fin n) (Fin m) (ZMod 2)) : Prop :=
  LinearMap.ker Q.mulVecLin ≤ LinearMap.range X.mulVecLin ∧
    ∀ w : Fin m → ZMod 2,
      X.mulVec w ∈ LinearMap.ker Q.mulVecLin → w ∈ LinearMap.range inj.mulVecLin

/-- The *order* `dim V₁ + codim W₁` of the hybrid Laplacian. -/
def hybridOrder {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker Q.mulVecLin) +
    (m - Module.finrank (ZMod 2) ↥(LinearMap.range inj.mulVecLin))

/-- The rank drop of a character kept by the hybrid Laplacian is exactly its order
(the paper's `Lem:Linear algebraic`). -/
theorem hybridPred_rank {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (hX : hybridPred Q inj X) :
    (Q * X * inj).rank = X.rank - hybridOrder Q inj := by
  rw [Commons.LinearAlgebra.Matrix.rank_sandwich_eq Q inj X hX.1 hX.2, hybridOrder]

/-- **Degree reduction for the hybrid derivative** (arXiv:2209.04243, Lemma 3.6): if `f` has
degree at most `d`, then its derivative of order `i = dim V₁ + codim W₁` has degree at most
`d - i`. -/
theorem degLe_hybrid_derivative {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) :
    DegLe (d - hybridOrder Q inj)
      (restr Q inj (shift T (lapMul (hybridPred Q inj) f))) := by
  refine degLe_restr_shift_lapMul (k := hybridOrder Q inj) Q inj T (hybridPred Q inj) hf ?_
  intro X hX
  rw [hybridPred_rank Q inj X hX]

/-- The unshifted version: `D_{V₁,W₁,0}` is the restriction of `L_{V₁,W₁}`. -/
theorem degLe_hybrid_derivative_zero {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2))
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) :
    DegLe (d - hybridOrder Q inj) (restr Q inj (lapMul (hybridPred Q inj) f)) := by
  refine degLe_restr_lapMul (k := hybridOrder Q inj) Q inj (hybridPred Q inj) hf ?_
  intro X hX
  rw [hybridPred_rank Q inj X hX]

end

end Submission.Grassmann
