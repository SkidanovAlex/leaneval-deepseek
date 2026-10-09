import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the algebra norm over a complete normed field

Let `𝕜` be a complete nontrivially normed field and let `A` be a finite-dimensional normed
`𝕜`-algebra (with continuous scalar multiplication).  Then the algebra norm

`Algebra.norm 𝕜 : A → 𝕜`

is **continuous**.

The proof is the classical one: fix a `𝕜`-basis `b` of `A`.  Then

`Algebra.norm 𝕜 x = (LinearMap.toMatrix b b (Algebra.lmul 𝕜 A x)).det`

(`Algebra.norm_apply`, `LinearMap.det_toMatrix`), and every matrix entry
`(LinearMap.toMatrix b b (Algebra.lmul 𝕜 A x)) i j = (b.repr (x * b j)) i`
(`LinearMap.toMatrix_apply`) is continuous in `x`: the coordinate functionals of a
finite-dimensional normed space over a complete field are continuous
(`LinearMap.continuous_of_finiteDimensional`), and `x ↦ x * b j` is continuous.  A determinant is a
polynomial in the entries, hence continuous (`Continuous.matrix_det`).

This is the analytic input used in `NK.NUV2.ArtinBridge` for the continuity of the local norm
maps `N_{L_w/K_v}` on the local fields, which are finite-dimensional normed algebras over a
complete (indeed local) field.
-/

namespace NK.NUV2.ArtinBridge

/-- **The algebra norm of a finite-dimensional algebra over a complete normed field is
continuous.** -/
theorem continuous_algebraNorm {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedField A]
    [Algebra 𝕜 A] [FiniteDimensional 𝕜 A] [ContinuousSMul 𝕜 A] [CompleteSpace 𝕜] :
    Continuous (Algebra.norm 𝕜 : A → 𝕜) := by
  classical
  set b := Module.finBasis 𝕜 A
  have hcoord (i : Fin (Module.finrank 𝕜 A)) : Continuous fun x : A => (b.repr x) i :=
    LinearMap.continuous_of_finiteDimensional
      ((Finsupp.lapply i : (Fin (Module.finrank 𝕜 A) →₀ 𝕜) →ₗ[𝕜] 𝕜).comp
        (b.repr : A →ₗ[𝕜] (Fin (Module.finrank 𝕜 A) →₀ 𝕜)))
  have hmat : Continuous fun x : A => LinearMap.toMatrix b b (Algebra.lmul 𝕜 A x) := by
    refine continuous_matrix fun i j => ?_
    exact (hcoord i).comp (continuous_id.mul continuous_const)
  have hdet := hmat.matrix_det
  convert hdet using 2 with x
  rw [Algebra.norm_apply, LinearMap.det_toMatrix]

end NK.NUV2.ArtinBridge
