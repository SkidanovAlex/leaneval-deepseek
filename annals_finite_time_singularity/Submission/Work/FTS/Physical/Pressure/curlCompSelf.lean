import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.CrossProduct

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Pressure

/-- **Coordinate core** of the curl product rule, for an abstract linear map `B` on `Fin 3 → ℝ`.

With `e i := Pi.single i 1` the standard basis of `Fin 3 → ℝ`, this is
`∑ i, e i × (B (B (e i))) = (∑ i, (B (e i)) i) • (∑ i, e i × (B (e i))) - B (∑ i, e i × (B (e i)))`.

The proof writes `M r s := (B (e s)) r` for the matrix of `B`, proves the expansion
`B f r = ∑ s, M r s * f s` (from `f = ∑ s, f s • e s` and linearity), and then checks the
`Fin 3` coordinates one by one with `ring`. -/
theorem curlCore (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :
    (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (B (Pi.single i (1:ℝ)))))
      = (∑ i : Fin 3, B (Pi.single i (1:ℝ)) i) •
          (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ))))
        - B (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ)))) := by
  set M : Fin 3 → Fin 3 → ℝ := fun r s => B (Pi.single s (1:ℝ)) r with hM
  have hbasis : ∀ f : Fin 3 → ℝ, f = ∑ s, f s • Pi.single s (1:ℝ) := fun f => by
    ext r; simp [Pi.single_apply, Finset.sum_ite_eq]
  have hBvec : ∀ f : Fin 3 → ℝ, B f = ∑ s, f s • B (Pi.single s (1:ℝ)) := by
    intro f
    conv_lhs => rw [hbasis f]
    rw [map_sum]
    simp only [map_smul]
  have hB : ∀ (f : Fin 3 → ℝ) (r : Fin 3), B f r = ∑ s, M r s * f s := by
    intro f r
    rw [hBvec f, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun s _ => by rw [hM]; ring
  funext r
  fin_cases r <;>
    simp [hB, Finset.sum_apply, Fin.sum_univ_three, cross_apply] <;>
    ring

/-- **Trace against the standard basis of `ℝ³`.**  The trace of `A : ℝ³ →L[ℝ] ℝ³` is the sum of
the diagonal entries of its matrix in the standard basis `WithLp.toLp 2 (Pi.single i 1)`. -/
theorem traceBasis (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    A.trace ℝ (EuclideanSpace ℝ (Fin 3))
      = ∑ i : Fin 3, (A (WithLp.toLp 2 (Pi.single i (1:ℝ)))).ofLp i := by
  rw [LinearMap.trace_eq_sum_inner A (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp

/-- **Linear-algebra core of the curl product rule.**

Write `e i := WithLp.toLp 2 (Pi.single i 1)` for the standard basis of `ℝ³` and let `curl A` denote
`∑ i, e i × (A (e i))`, the curl of the linear field `x ↦ A x`.  The claim is the classical identity
`curl (A ∘ A) = (tr A) • curl A - A (curl A)` for the linear field `x ↦ A (A x)`, written without
any local definitions.

A coordinate proof: put `m r s := (A (e s)) r` (the matrix of `A` in the standard basis), expand
`curl` componentwise with `crossProduct`/`Matrix.cross_apply` and `Fin.sum_univ_three`, expand
`A x = ∑ s, (A (e s)) · x` for `x : ℝ³` using `OrthonormalBasis.sum_repr` with
`EuclideanSpace.basisFun (Fin 3) ℝ` (whose `i`-th vector is `WithLp.toLp 2 (Pi.single i 1)`) and
`EuclideanSpace.basisFun_repr`, rewrite `A.trace ℝ (EuclideanSpace ℝ (Fin 3)) = ∑ i, m i i` with
`LinearMap.trace_eq_sum_inner`, and finish with `ring`.  A purely numeric check in coordinates can
also be done with `fin_cases` + `simp [Matrix.cross_apply, Fin.sum_univ_three]` + `ring`. -/
theorem curlCompSelf (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (∑ i : Fin 3, crossProduct (WithLp.toLp 2 (Pi.single i (1:ℝ)))
          (A (A (WithLp.toLp 2 (Pi.single i (1:ℝ))))))
      = (A.trace ℝ (EuclideanSpace ℝ (Fin 3))) •
          (EuclideanSpace.equiv (Fin 3) ℝ).symm
            (∑ i : Fin 3, crossProduct (WithLp.toLp 2 (Pi.single i (1:ℝ)))
              (A (WithLp.toLp 2 (Pi.single i (1:ℝ)))))
        - A ((EuclideanSpace.equiv (Fin 3) ℝ).symm
            (∑ i : Fin 3, crossProduct (WithLp.toLp 2 (Pi.single i (1:ℝ)))
              (A (WithLp.toLp 2 (Pi.single i (1:ℝ)))))) := by
  -- Conjugate `A` by the linear isometry `Φ : ℝ³ ≃ₗ ℝ³` given by `ofLp`, to get a linear map
  -- `B` on `Fin 3 → ℝ` whose matrix entries are those of `A` in the standard basis.
  let B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.comp
      (A.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)
  have hB : ∀ y : EuclideanSpace ℝ (Fin 3),
      B ((EuclideanSpace.equiv (Fin 3) ℝ) y) = (EuclideanSpace.equiv (Fin 3) ℝ) (A y) :=
    fun y => rfl
  have hBP : ∀ f : Fin 3 → ℝ, B f = (A (WithLp.toLp 2 f)).ofLp := fun f => rfl
  have htr : A.trace ℝ (EuclideanSpace ℝ (Fin 3))
      = ∑ i : Fin 3, B (Pi.single i (1:ℝ)) i := by
    rw [traceBasis A]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBP (Pi.single i (1:ℝ))]
  have hcore := curlCore B
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_sub, map_smul, ← hB, htr]
  exact hcore

end Work.FTS.Physical.Pressure
