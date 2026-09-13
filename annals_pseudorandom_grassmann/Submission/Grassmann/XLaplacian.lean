import Submission.Grassmann.HybridLaplacian
import Submission.Commons.LinearAlgebra.Matrix.rank_sandwich_poset
import Submission.Commons.LinearAlgebra.Matrix.rank_le_of_sub
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_antisymm
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_trans

/-!
# The `X`-Laplacians `L_X` and their derivatives

The paper (arXiv:2209.04243, Section 3.9) puts a partial order on the dual space
`L(W,V) = L(𝔽₂ᵐ, 𝔽₂ⁿ)` by

  `X ≤ Y  ⟺  rank Y = rank X + rank (Y - X)`,

i.e. `Im X` and `Im (Y - X)` are complementary subspaces of `Im Y`.  The `X`-*Laplacian*
`L_X` keeps exactly the characters `u_Y` with `Y ≥ X`, and the corresponding *derivative*
`D_{X,T}` is obtained by restricting `L_X` to `L(V/Im X, ker X)`.

The main result here is Lemma 3.8 of the paper: the derivative `D_{X,T}` of a function of
degree at most `d` has degree at most `d - rank X` (one degree per unit of rank, as opposed
to the hybrid case where the drop is `dim V₁ + codim W₁`).
-/

open Matrix Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-- The partial order on `L(𝔽₂ᵐ, 𝔽₂ⁿ)`: `X ≤ Y` iff `Im X` and `Im (Y - X)` are
complementary in `Im Y`. -/
def plLE {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2)) : Prop :=
  Y.rank = X.rank + (Y - X).rank

lemma plLE_refl {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) : plLE X X := by
  simp [plLE]

lemma plLE_antisymm {m n : ℕ} {X Y : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hXY : plLE X Y) (hYX : plLE Y X) : X = Y :=
  Commons.LinearAlgebra.Matrix.rank_poset_antisymm X Y hXY hYX

lemma plLE_trans {m n : ℕ} {X Y Z : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hXY : plLE X Y) (hYZ : plLE Y Z) : plLE X Z :=
  Commons.LinearAlgebra.Matrix.rank_poset_trans X Y Z hXY hYZ

lemma plLE_rank_le {m n : ℕ} {X Y : Matrix (Fin n) (Fin m) (ZMod 2)} (h : plLE X Y) :
    X.rank ≤ Y.rank :=
  Commons.LinearAlgebra.Matrix.rank_le_of_sub X Y h

/-- **Degree reduction for the `X`-derivative** (arXiv:2209.04243, Lemma 3.8): if `f` has
degree at most `d`, then `D_{X,T}[f]` has degree at most `d - rank X`. -/
theorem degLe_x_derivative {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (X0 : Matrix (Fin n) (Fin m) (ZMod 2))
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range X0.mulVecLin)
    (hinj : LinearMap.range inj.mulVecLin = LinearMap.ker X0.mulVecLin)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) :
    DegLe (d - X0.rank) (restr Q inj (shift T (lapMul (plLE X0) f))) := by
  refine degLe_restr_shift_lapMul (k := X0.rank) Q inj T (plLE X0) hf ?_
  intro Y hY
  rw [Commons.LinearAlgebra.Matrix.rank_sandwich_poset Q inj X0 Y hQ hinj hY]

/-- The same with the normalised Laplacian. -/
theorem degLe_x_derivative_N {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (inj : Matrix (Fin m) (Fin m') (ZMod 2)) (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (X0 : Matrix (Fin n) (Fin m) (ZMod 2))
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range X0.mulVecLin)
    (hinj : LinearMap.range inj.mulVecLin = LinearMap.ker X0.mulVecLin)
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) :
    DegLe (d - X0.rank) (restr Q inj (shift T (lapMulN (plLE X0) f))) := by
  refine degLe_restr_shift_lapMulN (k := X0.rank) Q inj T (plLE X0) hf ?_
  intro Y hY
  rw [Commons.LinearAlgebra.Matrix.rank_sandwich_poset Q inj X0 Y hQ hinj hY]

end

end Submission.Grassmann
