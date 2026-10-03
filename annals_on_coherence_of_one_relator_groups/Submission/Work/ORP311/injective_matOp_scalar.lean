import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

/-!
# Injectivity of `matOp` of a scalar matrix

`Work.ORVonNeumann.Rep.matOp A` is the operator `⊕_{j : Fin m} ℓ²(G) → ⊕_{i : Fin n} ℓ²(G)`
induced by a matrix `A` over the group von Neumann algebra `N(G)`.  For the scalar matrix
`Matrix.scalar (Fin n) a` (the diagonal matrix with `a` on the diagonal), the matrix operator
acts coordinatewise: its `i`-th coordinate is `a` applied to the `i`-th coordinate of the
input.  Hence if `a`, viewed as an operator on `ℓ²(G)`, is injective, then so is
`matOp (Matrix.scalar (Fin n) a)`.
-/

namespace Work.ORP311

open Work.ORVonNeumann

/-- The matrix operator of a scalar matrix acts coordinatewise: the `i`-th coordinate of
`matOp (Matrix.scalar (Fin n) a) x` is `a` applied to the `i`-th coordinate of `x`.

This is `Work.ORVonNeumann.Rep.hcoord_matOp_apply` together with the fact that all off-diagonal
entries of the scalar matrix vanish. -/
theorem hcoord_matOp_scalar {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (a : ↥(Work.ORVonNeumann.groupVonNeumann G)) (x : Work.ORVonNeumann.Rep.HSum (G := G) n)
    (i : Fin n) :
    Work.ORVonNeumann.Rep.hcoord (G := G) n i
        (Work.ORVonNeumann.Rep.matOp (G := G) (Matrix.scalar (Fin n) a) x)
      = (a : Work.ORVonNeumann.boundedEnd G)
          (Work.ORVonNeumann.Rep.hcoord (G := G) n i x) := by
  rw [Work.ORVonNeumann.Rep.hcoord_matOp_apply]
  rw [Finset.sum_eq_single i]
  · congr 1
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_pos rfl]
  · intro j _ hj
    have hij : (Matrix.scalar (Fin n) a) i j = 0 := by
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg (Ne.symm hj)]
    rw [hij]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem injective_matOp_scalar {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (a : ↥(Work.ORVonNeumann.groupVonNeumann G)) (ha : Function.Injective (a : Work.ORVonNeumann.boundedEnd G)) : Function.Injective (Work.ORVonNeumann.Rep.matOp (G := G) (Matrix.scalar (Fin n) a)) := by
  intro x y hxy
  -- `matOp` is additive, so it suffices to show that `x - y = 0`.
  have hzero :
      Work.ORVonNeumann.Rep.matOp (G := G) (Matrix.scalar (Fin n) a) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  apply Work.ORVonNeumann.Rep.hsum_ext
  intro i
  -- Project to the `i`-th coordinate: `a ((x - y)_i) = 0`, whence `(x - y)_i = 0` by
  -- injectivity of `a`.
  have hi := congrArg (Work.ORVonNeumann.Rep.hcoord (G := G) n i) hzero
  rw [map_zero, hcoord_matOp_scalar] at hi
  have hxi : (Work.ORVonNeumann.Rep.hcoord (G := G) n i) (x - y) = 0 :=
    ha (show (a : Work.ORVonNeumann.boundedEnd G)
          (Work.ORVonNeumann.Rep.hcoord (G := G) n i (x - y))
        = (a : Work.ORVonNeumann.boundedEnd G) 0 by rw [hi, map_zero])
  simpa using hxi

end Work.ORP311
