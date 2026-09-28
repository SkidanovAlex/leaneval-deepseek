import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs

namespace Work.HP.Sig2

/-- The real Gram matrix `gramOf b` of a `ℤ`-basis `b` of an integral lattice `Λ ⊆ ℤ^ι`
(`gramOf b i j = ∑ x, (b i x : ℝ) * (b j x : ℝ)`) is positive definite; in particular its
determinant is nonzero.

The imports are `Mathlib` and `Submission.Work.HP.Sig2.GamTwoDefs`; the file should live in
namespace `Work.HP.Sig2`.

Route: for `x : κ →₀ ℝ`, the quadratic form
`x.sum (fun i xi => x.sum (fun j xj => xi * gramOf b i j * xj))` equals
`∑ x, ((∑ i, x i * (b i x : ℝ)) ^ 2)`, i.e. the square of the Euclidean norm of the real vector
`∑ i, (x i) • toR ((b i : Λ) : ι → ℤ)`; this is positive for `x ≠ 0` because the realifications
`toR (b i)` of the `ℤ`-basis `b` are `ℝ`-linearly independent (`Work.HP.Vero.linInd_intCastPi`
applied to `LinearIndependent ℤ (fun i => ((b i : Λ) : ι → ℤ))`, which comes from
`b.linearIndependent` by `LinearIndependent.map'` along the injective inclusion `Λ ↪ ℤ^ι`).
Hermitian-ness of `gramOf b` is its symmetry (`Finset.sum_congr` swapping `i j` and `mul_comm`).
NOTE: a very similar lemma `gram_posDef` for a general `LinearIndependent ℝ w` is proved in
`Submission/Work/HP/MDEstimates/detL_one_le.lean` (do NOT import that file: it is in a family
that clashes with `Submission.Work.HP.Vero` on the name `Work.HP.orthLat`; copy the proof
technique instead). -/
theorem GramOfPosDef {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    [DecidableEq κ] {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    (gramOf b).PosDef := by
  classical
  -- The realified basis vectors, and their coordinate matrix `C y i = (intCastPi (b i)) y`.
  let v : κ → (ι → ℝ) := fun i => intCastPi (((b i : Λ) : ι → ℤ))
  let C : Matrix κ ι ℝ := Matrix.of fun i x => v i x
  -- The realifications of the basis vectors are `ℝ`-linearly independent.
  have hli : LinearIndependent ℝ v :=
    Vero.linInd_intCastPi (b.linearIndependent.map' (Submodule.subtype Λ) (by
      rw [LinearMap.ker_eq_bot]; exact Subtype.coe_injective))
  -- Hence the rows of `C` are independent, i.e. `C.vecMul` is injective.
  have hCrow : LinearIndependent ℝ C.row := by
    have h : C.row = v := by ext i x; simp [C, v, Matrix.row]
    rw [h]; exact hli
  have hinj : Function.Injective (fun x => Matrix.vecMul x C) :=
    Matrix.vecMul_injective_iff.mpr hCrow
  -- `gramOf b = C * Cᵀ`, and `C * Cᵀ` is positive definite by `mul_conjTranspose_self`.
  have hpd := Matrix.PosDef.mul_conjTranspose_self C hinj
  have hEq : gramOf b = C * C.conjTranspose := by
    ext i j
    simp [gramOf, C, v, Matrix.mul_apply, intCastPi]
  rw [hEq]
  exact hpd

end Work.HP.Sig2
