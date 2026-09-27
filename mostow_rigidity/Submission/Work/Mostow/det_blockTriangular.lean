import Mathlib

/-!
# Determinant of a block upper triangular endomorphism

For a commutative ring `R` and finite free `R`-modules `M`, `M'`, the endomorphism of `M × M'`
given by `(x, y) ↦ (f x + g y, h y)` (block upper triangular with blocks `f`, `g`, `0`, `h`) has
determinant `det f * det h`.

This is the linear-algebraic input used to compute the determinant of the block maps
`(x, y) ↦ (x + A y, B y)` appearing in the BCG / Prasad chapter of Mostow rigidity.

## Proof

Choose explicit bases `bM` of `M` and `bM'` of `M'`; then `bM.prod bM'` is a basis of `M × M'`
indexed by `ι ⊕ ι'`.  In this basis the matrix of the block map is literally
`Matrix.fromBlocks (toMatrix f) (toMatrix g) 0 (toMatrix h)`, so the claim follows from
`Matrix.det_fromBlocks_zero₂₁` and `LinearMap.det_toMatrix`.
-/

namespace Work.Mostow

theorem det_blockTriangular {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Free R M] [Module.Finite R M]
    [Module.Free R M'] [Module.Finite R M']
    (f : M →ₗ[R] M) (g : M' →ₗ[R] M) (h : M' →ₗ[R] M') :
    LinearMap.det (LinearMap.prod
        (f.comp (LinearMap.fst R M M') + g.comp (LinearMap.snd R M M'))
        (h.comp (LinearMap.snd R M M'))) = LinearMap.det f * LinearMap.det h := by
  classical
  let bM := Module.Free.chooseBasis R M
  let bM' := Module.Free.chooseBasis R M'
  let b := bM.prod bM'
  -- In the basis `bM.prod bM'` the endomorphism has the desired block form.
  have hmat : LinearMap.toMatrix b b (LinearMap.prod
        (f.comp (LinearMap.fst R M M') + g.comp (LinearMap.snd R M M'))
        (h.comp (LinearMap.snd R M M')))
      = Matrix.fromBlocks (LinearMap.toMatrix bM bM f) (LinearMap.toMatrix bM' bM g) 0
          (LinearMap.toMatrix bM' bM' h) := by
    ext i j
    simp only [LinearMap.toMatrix_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [b, Module.Basis.prod_apply, LinearMap.prod_apply,
        Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr, LinearMap.toMatrix_apply]
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_fromBlocks_zero₂₁,
    ← LinearMap.det_toMatrix bM, ← LinearMap.det_toMatrix bM']

end Work.Mostow
