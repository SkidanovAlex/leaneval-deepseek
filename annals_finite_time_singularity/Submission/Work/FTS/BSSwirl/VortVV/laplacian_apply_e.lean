import Mathlib.Analysis.InnerProductSpace.Laplacian
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

open scoped Topology

/-- The standard orthonormal basis `EuclideanSpace.basisFun (Fin 3) ℝ` of `ℝ³` agrees with the
workspace basis `FiniteTimeSingularity.e`.  (A local copy of `Work.FTS.BSSwirl.basisFun_eq_e`, so
that this module needs nothing from the pressure area; the two live in different namespaces, so
importing both is harmless.) -/
theorem basisFun_eq_e_ (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ) i = FiniteTimeSingularity.e i := by
  rw [EuclideanSpace.basisFun_apply, FiniteTimeSingularity.e]
  rfl

/-- **The Laplacian in the orthonormal basis `e`.**  For an arbitrary (not assumed differentiable)
`Ψ : ℝ³ → ℝ³`, Mathlib's `Laplacian.laplacian` — the second derivative paired with the canonical
covariant tensor, i.e. the sum of the diagonal entries of the Hessian in an orthonormal basis — is
the sum `∑ᵢ ∂ᵢ∂ᵢΨ(x)` in the workspace basis `e` of `ChallengeDeps.lean`.

No regularity hypothesis is needed: `Laplacian.laplacian Ψ` is by definition
`tensorIteratedFDerivTwo ℝ Ψ · (canonicalCovariantTensor ℝ³)`, and
`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` rewrites it as the plain sum of
`iteratedFDeriv ℝ 2 Ψ x ![v i, v i]` over any orthonormal basis `v`, for *every* `Ψ`; the
instances of `fderiv` occurring there are total functions, so the identity is an algebraic
identity about `fderiv`, not a regularity statement.  Finally
`iteratedFDeriv_two_apply` identifies `iteratedFDeriv ℝ 2 Ψ x ![u, u]` with
`fderiv ℝ (fderiv ℝ Ψ) x u u`. -/
theorem laplacian_apply_e (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (x : Work.FTS.BSSwirl.R3) :
    Laplacian.laplacian Ψ x
      = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ Ψ) x (FiniteTimeSingularity.e i)
          (FiniteTimeSingularity.e i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis Ψ
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [basisFun_eq_e_ i, iteratedFDeriv_two_apply]
  simp

end Work.FTS.BSSwirl.VortVV
