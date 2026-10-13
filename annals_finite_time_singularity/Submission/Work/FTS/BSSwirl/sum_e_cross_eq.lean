import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.BSSwirl.sum_e_cross_eq`

The identity expanding the curl-type sum `∑ i, e i × (⟪v, e i⟫ • w)` of the Biot--Savart
computation for a swirl vorticity: the standard basis vectors `e i = Pi.single i 1` of `ℝ³`
resolve every vector `v`, i.e.

  `∑ i, e i × (⟪v, e i⟫ • w) = v × w`

in `Fin 3 → ℝ`.  Indeed `crossProduct` is bilinear, so the left-hand side is
`∑ i, ⟪v, e i⟫ • (e i × w)`, and `v = ∑ i, ⟪v, e i⟫ • e i` expands `v × w` in the same way.
The statement below is the scalar-multiplied form in which the swirl computation consumes it,

  `∑ i, e i × (c • (⟪y - x, e i⟫ • w)) = c • (w × (x - y))`,

the point being that `w × (x - y) = (y - x) × w` by antisymmetry of the cross product.

Both the general identity (`sum_single_cross`) and the requested theorem are proved by the
finite coordinate computation in the standard basis, exactly as Mathlib proves its own
cross-product identities.
-/

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The cross product computed on the standard basis.**  For vectors `a v : Fin 3 → ℝ`,
`∑ i, e i × (a i • v) = a × v`, where `e i = Pi.single i 1`.

This is the identity `a × v = ∑ i, a i • (e i × v)` obtained by expanding `a` in the standard
basis of `ℝ³` and using the bilinearity of the cross product.  It is proved directly in
coordinates (`cross_apply`), the vectors being functions `Fin 3 → ℝ`. -/
theorem sum_single_cross (a v : Fin 3 → ℝ) :
    (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (a i • v)) = crossProduct a v := by
  rw [Fin.sum_univ_three]
  simp only [cross_apply]
  ext j
  fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk,
      smul_eq_mul] <;> ring

theorem sum_e_cross_eq (x y w : Work.FTS.BSSwirl.R3) (c : ℝ) :
    (∑ i : Fin 3, crossProduct ((FiniteTimeSingularity.e i).ofLp)
        (c • (inner ℝ (y - x) (FiniteTimeSingularity.e i) • w.ofLp)))
      = c • crossProduct w.ofLp (x - y).ofLp := by
  -- `⟪y - x, e i⟫ = (y - x).ofLp i`: the coordinates of `y - x` are the pairings against `e i`.
  have hinner : ∀ i : Fin 3, inner ℝ (y - x) (FiniteTimeSingularity.e i) = (y - x).ofLp i := by
    intro i
    rw [show FiniteTimeSingularity.e i = EuclideanSpace.single i 1 from rfl]
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [hinner]
  -- `(e i).ofLp = Pi.single i 1`, i.e. `e i` is the `i`-th standard basis vector of `ℝ³`.
  simp only [FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  -- Bilinearity of `crossProduct` moves the scalar out of the summand and the sum out of the
  -- scalar multiplication; the remaining sum is `sum_single_cross`.
  have hsum : (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (c • ((y - x).ofLp i • w.ofLp)))
      = c • crossProduct (y - x).ofLp w.ofLp := by
    calc (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (c • ((y - x).ofLp i • w.ofLp)))
        = ∑ i : Fin 3, c • crossProduct (Pi.single i (1 : ℝ)) ((y - x).ofLp i • w.ofLp) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, map_smul]
      _ = c • ∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) ((y - x).ofLp i • w.ofLp) := by
          rw [← Finset.smul_sum]
      _ = c • crossProduct (y - x).ofLp w.ofLp := by rw [sum_single_cross]
  rw [hsum]
  -- Antisymmetry of the cross product turns `(y - x) × w` into `w × (x - y)`.
  have hsign : crossProduct (y - x).ofLp w.ofLp = crossProduct w.ofLp (x - y).ofLp := by
    have h1 : (x - y).ofLp = -((y - x).ofLp) := by
      rw [WithLp.ofLp_sub, WithLp.ofLp_sub, neg_sub]
    rw [h1, map_neg, cross_anticomm]
  rw [hsign]

end

end Work.FTS.BSSwirl
