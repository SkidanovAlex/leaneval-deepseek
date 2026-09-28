import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HPgram
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# The covolume of an integral lattice in `ℤ^ι` is at least `1`

For every submodule `L ⊆ ℤ^ι` (an integral lattice), the covolume
`Work.HP.detL L = √(det (Gram matrix of a ℤ-basis of L))` satisfies `1 ≤ detL L`.

The proof: the Gram matrix `G` of a `ℤ`-basis of `L` has integer entries, and it is positive
definite.  Positivity comes from linear independence of the basis vectors in `ℝ^ι`: a `ℤ`-basis of
`L` is in particular `ℤ`-linearly independent, and a `ℤ`-linearly independent family of vectors in
`ℤ^ι` stays linearly independent after the coefficient extension `ℤ → ℝ`
(`linearIndependent_algebraMap_comp_iff`).  Writing the real Gram matrix as `Aᵀ A` for the real
coordinate matrix `A` of the basis, `Matrix.PosDef.conjTranspose_mul_self` shows it is positive
definite, hence `det G > 0` (`Matrix.PosDef.det_pos`).  Since `G` is the image of an integer
matrix `M`, `det G = (M.det : ℝ)` is a *positive integer*, so `det G ≥ 1`.  Taking square roots
gives `detL L ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Lat

open Matrix

/-- The Gram matrix of a `ℤ`-basis of an integral lattice `L ⊆ ℤ^ι` has positive determinant.
This is the positivity input for `detL_ge_one`: the basis is linearly independent over `ℝ`, so the
Gram matrix (which is `Aᵀ A` for the real coordinate matrix `A`) is positive definite. -/
lemma gramMat_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    0 < (Work.HP.gramMat k L b).det := by
  classical
  -- The real coordinate matrix of the basis: column `i` is the vector `b i`, cast to `ℝ`.
  let A : Matrix ι (Fin k) ℝ := Matrix.of fun x i => (((b i : ι → ℤ) x : ℤ) : ℝ)
  -- The coordinate vectors are `ℤ`-linearly independent (they are a basis of `L`).
  have hLIℤ : LinearIndependent ℤ (fun i => (b i : ι → ℤ)) :=
    b.linearIndependent.map' (Submodule.subtype L) (Submodule.ker_subtype L)
  -- ... hence `ℝ`-linearly independent after extending scalars `ℤ → ℝ`.
  have hLIℝ : LinearIndependent ℝ A.col := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)
      (v := fun i : Fin k => (b i : ι → ℤ))).mpr hLIℤ
    convert h using 2
    ext x
    simp [A, Matrix.col, Function.comp]
  -- So `A` has injective `mulVec` and `Aᴴ A` is positive definite.
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff.mpr hLIℝ
  have hpd : (A.conjTranspose * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hinj
  -- `Aᴴ A` is exactly the real Gram matrix of the basis.
  have hEq : A.conjTranspose * A = Work.HP.gramMat k L b := by
    ext i j
    simp [A, Work.HP.gramMat, Matrix.mul_apply]
  rw [← hEq]
  exact hpd.det_pos

/-- **`detL` is at least `1`.**  Every integral lattice `L ⊆ ℤ^ι` has covolume `detL L ≥ 1`. -/
theorem detL_ge_one {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) :
    1 ≤ Work.HP.detL L := by
  -- Unfold `detL` as the square root of the Gram determinant and reduce to `1 ≤ det (Gram)`.
  rw [Work.HP.detL_eq_sqrt_gramMat L, Real.one_le_sqrt]
  set k := (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).1
  set b := (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2
  -- The underlying integer Gram matrix.
  let M : Matrix (Fin k) (Fin k) ℤ :=
    Matrix.of fun i j => ∑ x, (b i : ι → ℤ) x * (b j : ι → ℤ) x
  have hmap : Work.HP.gramMat k L b = M.map (fun z : ℤ => (z : ℝ)) := by
    ext i j
    simp [M, Work.HP.gramMat, Int.cast_sum, Int.cast_mul]
  -- The real Gram determinant is the cast of the integer determinant.
  have hdet_eq : (Work.HP.gramMat k L b).det = ((M.det : ℤ) : ℝ) := by
    rw [hmap, ← Int.cast_det]
  -- It is positive, hence the integer determinant is positive, hence at least `1`.
  have hpos : 0 < M.det := by
    have h := gramMat_det_pos k L b
    rw [hdet_eq] at h
    exact_mod_cast h
  rw [hdet_eq]
  exact_mod_cast (by omega : (1 : ℤ) ≤ M.det)

end Work.HP.Lat
