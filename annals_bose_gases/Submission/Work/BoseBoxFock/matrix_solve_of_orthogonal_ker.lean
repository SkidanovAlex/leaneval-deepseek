import Mathlib.Tactic.Have
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Archimedean.Real.Hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Solvability of a symmetric linear system from orthogonality to the kernel

For a real symmetric matrix `A` on a finite index type `ι`, the range of the linear map
`x ↦ A *ᵥ x` is exactly the orthogonal complement of the kernel: over `ℝ` a symmetric matrix
is self-adjoint, hence `range = kerᗮ`. Consequently, any `c` which is orthogonal to every
solution of the homogeneous system `A x = 0` lies in the range of `A`, i.e. `A x = c` is
solvable. This is the finite-dimensional Fredholm alternative for symmetric real matrices.
-/

open scoped RealInnerProductSpace

namespace Work.BoseBoxFock

theorem matrix_solve_of_orthogonal_ker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (c : ι → ℝ)
    (h : ∀ x : ι → ℝ, (∀ i, ∑ j, A i j * x j = 0) → ∑ i, c i * x i = 0) :
    ∃ x : ι → ℝ, ∀ i, ∑ j, A i j * x j = c i := by
  classical
  -- Lift `A *ᵥ ·` to a linear operator on `EuclideanSpace ℝ ι`, where an inner product is available.
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := LinearMap.withLpMap 2 (Matrix.mulVecLin A)
  -- `T` acts as `A *ᵥ ·` on the underlying coordinates.
  have hT_apply : ∀ z : EuclideanSpace ℝ ι, (T z).ofLp = A.mulVec z.ofLp := by
    intro z
    simp [T]
  -- The inner product on `EuclideanSpace ℝ ι` is the dot product of the coordinate functions.
  have hinner : ∀ u v : EuclideanSpace ℝ ι, ⟪u, v⟫ = dotProduct v.ofLp u.ofLp := by
    intro u v
    rw [PiLp.inner_apply, dotProduct]
    simp
  -- `T` is symmetric because `A` is.
  have hTsym : T.IsSymmetric := by
    intro x y
    rw [hinner, hinner, hT_apply x, hT_apply y]
    rw [dotProduct_comm (A.mulVec y.ofLp) x.ofLp]
    have := Matrix.dotProduct_transpose_mulVec A y.ofLp x.ofLp
    rwa [hA] at this
  -- `c`, seen as a vector of `EuclideanSpace ℝ ι`.
  let c' : EuclideanSpace ℝ ι := WithLp.toLp 2 c
  have hc'_ofLp : c'.ofLp = c := WithLp.ofLp_toLp 2 c
  -- The hypothesis says precisely that `c'` is orthogonal to the kernel of `T`.
  have hc' : c' ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [hinner, hc'_ofLp]
    apply h u.ofLp
    intro i
    have hAu : A.mulVec u.ofLp = 0 := by rw [← hT_apply u, hu]; rfl
    have := congrFun hAu i
    simpa [Matrix.mulVec, dotProduct] using this
  -- For a symmetric operator, `kerᗮ = range`.
  have hrange : c' ∈ T.range := by
    have h1 : T.kerᗮ = T.range := by
      rw [← hTsym.orthogonal_range]
      exact Submodule.orthogonal_orthogonal T.range
    rw [h1] at hc'
    exact hc'
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hrange
  refine ⟨y.ofLp, fun i => ?_⟩
  have hAy : A.mulVec y.ofLp = c := by
    rw [← hT_apply y, hy, hc'_ofLp]
  have := congrFun hAy i
  simpa [Matrix.mulVec, dotProduct] using this

end Work.BoseBoxFock
