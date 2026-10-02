import Mathlib
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two elementary facts about rank-`k` orthogonal projections in `ℝⁿ`

Prerequisites for the chart-family construction `Work.PTGeometric.AmbCharts`
(see `Submission/Work/PTGeometric/README.md`): the plane `im Q` of a rank-`k` orthogonal projection
`Q ∈ Gr n k` has dimension `k`, and the standard-basis expansion of a vector of `ℝᵏ` in terms of the
vectors `EuclideanSpace.single j 1`.

Both are used to build the `ℓ`-adapted frame of the moving planes: for `Q ∈ Gr n k` and a linear
`ℓ : ℝⁿ → ℝᵏ` injective on `im Q`, the map `S = ℓ ∘ Q ∘ ℓ†` is invertible, so
`e j := Q (ℓ† (S⁻¹ (single j 1)))` is a frame of `im Q` with `ℓ (∑ j, t j • e j) = t`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace Work.PTGeometric

open scoped Manifold ContDiff

/-- **The plane of a rank-`k` orthogonal projection is `k`-dimensional.**  `Gr n k` is the set of
orthogonal projections of trace `k`, and the trace of a projection is the dimension of its range. -/
theorem finrank_range_mem_Gr {n k : ℕ} {Q : EndOp n} (hQ : Q ∈ Gr n k) :
    Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) = k := by
  have hQidem : Q * Q = Q := hQ.2.1
  have hQidem_lin : (Q : Amb n →ₗ[ℝ] Amb n) * (Q : Amb n →ₗ[ℝ] Amb n)
      = (Q : Amb n →ₗ[ℝ] Amb n) := by
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
    have h : (Q * Q : EndOp n) y = Q y := by rw [hQidem]
    simpa using h
  have hproj : LinearMap.IsProj (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n))
      (Q : Amb n →ₗ[ℝ] Amb n) :=
    (LinearMap.isProj_range_iff_isIdempotentElem (Q : Amb n →ₗ[ℝ] Amb n)).mpr hQidem_lin
  have h1 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n)
      = (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hproj.trace
  have h2 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hQ.2.2
  have h3 : (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
    rw [← h1, h2]
  exact Nat.cast_injective h3

/-- The idempotence of a projection, as a statement about its action on vectors. -/
theorem mem_Gr_apply_apply {n k : ℕ} {Q : EndOp n} (hQ : Q ∈ Gr n k) (z : Amb n) :
    Q (Q z) = Q z := by
  have h : (Q * Q : EndOp n) z = Q z := by rw [hQ.2.1]
  simpa using h

/-- **The standard-basis expansion of `ℝᵏ`**: `∑ j, t j • single j 1 = t`. -/
theorem sum_smul_single_eq {k : ℕ} (t : Amb k) :
    (Finset.univ.sum fun j : Fin k => t j • EuclideanSpace.single j (1 : ℝ)) = t := by
  have h : (Finset.univ.sum fun j : Fin k => t j • EuclideanSpace.single j (1 : ℝ))
      = Finset.univ.sum fun j : Fin k =>
          (EuclideanSpace.basisFun (Fin k) ℝ).repr t j • (EuclideanSpace.basisFun (Fin k) ℝ) j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  rw [h, OrthonormalBasis.sum_repr]

end Work.PTGeometric
