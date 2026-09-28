import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs

namespace Work.HP.Sig2

/-!
# The Gram matrix `gramOf b` of a `ℤ`-basis is invertible over `ℝ`

Let `Λ ⊆ ℤ^ι` be a sublattice and `b : Basis κ ℤ Λ` a `ℤ`-basis.  Its real Gram matrix
`gramOf b` (`G i j = ∑ x, (b i) x * (b j) x`, all entries cast to `ℝ`) is invertible, and its
nonsingular inverse `(gramOf b)⁻¹` is a two-sided inverse.

Proof.
* The realifications `v i = intCastPi (b i)` of the basis vectors are `ℝ`-linearly independent:
  the family `i ↦ ↑(b i) : ℤ^ι` is `ℤ`-linearly independent (`b.linearIndependent`, transported
  along the injective `Λ → ℤ^ι`), and `ℤ`-independent integer vectors stay independent after
  casting to `ℝ` (`Work.HP.Vero.linInd_intCastPi`); this is the realified-sublattice fact that
  `Λ ⊗ ℤ ℝ → ℝ^ι` is injective.
* `gramOf b = Aᵀ * A` where `A : Matrix ι κ ℝ` is the coordinate matrix `A y i = v i y`
  (`gramOf_eq_transpose_mul`).
* Hence for every `x : κ → ℝ`,
  `x ⬝ᵥ ((gramOf b) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (A *ᵥ x)`, a sum of squares: it vanishes only for
  `A *ᵥ x = 0`, which by linear independence forces `x = 0`
  (`A *ᵥ x = Fintype.linearCombination ℝ v x`).  So `(gramOf b).mulVec` is injective, and an
  injective `mulVec` of a square matrix over a field is a unit (`Matrix.mulVec_injective_iff_isUnit`).
* The two-sided inverse statements then follow from `IsUnit` and the general facts
  `Matrix.nonsing_inv_mul` / `Matrix.mul_nonsing_inv` for nonsingular matrices.
-/

/-- The realifications of the vectors of a `ℤ`-basis of a sublattice `Λ ⊆ ℤ^ι` are `ℝ`-linearly
independent (the realification `Λ ⊗[ℤ] ℝ → ℝ^ι` is injective, since `Λ` is torsion free). -/
theorem linearIndependent_intCastPi_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    LinearIndependent ℝ (fun i : κ => intCastPi (((b i : Λ) : ι → ℤ))) :=
  Vero.linInd_intCastPi (b.linearIndependent.map' (Submodule.subtype Λ) (by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.coe_injective))

/-- `gramOf b` is the product `Aᵀ * A` of the coordinate matrix `A` of the realified basis vectors
(`A y i = (b i) y`). -/
theorem gramOf_eq_transpose_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    gramOf b =
      Matrix.transpose (Matrix.of fun (y : ι) (i : κ) => intCastPi (((b i : Λ) : ι → ℤ)) y) *
        (Matrix.of fun (y : ι) (i : κ) => intCastPi (((b i : Λ) : ι → ℤ)) y) := by
  ext i j
  simp [gramOf, Matrix.mul_apply, Matrix.transpose_apply, intCastPi]

/-- The real Gram matrix `gramOf b` of a `ℤ`-basis `b` of a sublattice `Λ ⊆ ℤ^ι` is invertible
(equivalently, the realified basis vectors are `ℝ`-linearly independent), so its nonsingular
inverse is a two-sided inverse. -/
theorem gramOf_isUnit_inv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) :
    IsUnit (gramOf b) ∧ (gramOf b)⁻¹ * gramOf b = 1 ∧ (gramOf b) * (gramOf b)⁻¹ = 1 := by
  classical
  -- the realified basis vectors, and their coordinate matrix
  let v : κ → (ι → ℝ) := fun i => intCastPi (((b i : Λ) : ι → ℤ))
  let A : Matrix ι κ ℝ := Matrix.of fun y i => v i y
  have hli : LinearIndependent ℝ v := linearIndependent_intCastPi_basis b
  have hG : gramOf b = Matrix.transpose A * A := by
    rw [gramOf_eq_transpose_mul b]
  -- `A.mulVec` is `Fintype.linearCombination ℝ v`, hence injective by linear independence
  have hmul (x : κ → ℝ) : A.mulVec x = Fintype.linearCombination ℝ v x := by
    ext y
    rw [Matrix.mulVec_apply_eq_sum, Fintype.linearCombination_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [A]
    rw [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_comm (v i y) (x i)
  have hAinj : Function.Injective A.mulVec := by
    have hv_inj : Function.Injective (Fintype.linearCombination ℝ v) :=
      hli.fintypeLinearCombination_injective
    intro x y hxy
    exact hv_inj (by rw [← hmul x, ← hmul y, hxy])
  -- the associated quadratic form is a sum of squares
  have hquad (x : κ → ℝ) : x ⬝ᵥ ((gramOf b).mulVec x) = (A.mulVec x) ⬝ᵥ (A.mulVec x) := by
    rw [hG, ← Matrix.mulVec_mulVec x (Matrix.transpose A) A]
    exact Matrix.dotProduct_transpose_mulVec A x (A.mulVec x)
  have hinj : Function.Injective (gramOf b).mulVec := by
    intro x y hxy
    have hz : (gramOf b).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hq := hquad (x - y)
    rw [hz, dotProduct_zero] at hq
    have h0 : A.mulVec (x - y) = 0 := dotProduct_self_eq_zero.mp hq.symm
    have hsub : x - y = 0 := hAinj (by rw [h0, Matrix.mulVec_zero])
    exact sub_eq_zero.mp hsub
  have hU : IsUnit (gramOf b) := (Matrix.mulVec_injective_iff_isUnit).mp hinj
  have hdet : IsUnit (gramOf b).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  exact ⟨hU, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

end Work.HP.Sig2
