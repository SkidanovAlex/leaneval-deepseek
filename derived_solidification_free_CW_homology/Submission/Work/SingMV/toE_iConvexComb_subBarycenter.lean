import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# Coordinates of a convex combination weighted by a sub-barycenter

If `q : Fin m → Δⁿ` is a finite family of points of the standard `n`-simplex and `A ⊆ {0,…,m-1}`
is nonempty, then the convex combination of the `q i` with weights the barycenter of `A` has
`j`-th coordinate the average of the `j`-th coordinates of the `q i`, `i ∈ A`:

`toE (iConvexComb (subBarycenter A hA) q) j = (A.card : ℝ)⁻¹ * ∑ i ∈ A, toE (q i) j`.

Equivalently, the barycenter of a set of vertices of `Δ^{m-1}` maps to the average of the
corresponding points of `Δⁿ` under the affine map with vertex tuple `q`. This is the elementary
computation behind the metric estimates on the mesh of the barycentric subdivision
(`Work.SingMV.bary_dist_le`, `Work.SingMV.subBarycenter_dist_le`): it turns the `j`-th coordinate
of `iConvexComb (subBarycenter A hA) q` into an ordinary average of real numbers.
-/

open Convexity
open scoped BigOperators

noncomputable section

namespace Work.SingMV

/-- The weights of the sub-barycenter of a finite set `A` of vertices: they equal `1/|A|` on `A`
and `0` off `A`. -/
lemma weights_subBarycenter_apply {m : ℕ} (A : Finset (Fin m)) (hA : A.Nonempty) (i : Fin m) :
    (Convexity.StdSimplex.subBarycenter A hA).weights i
      = if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  rw [Convexity.StdSimplex.weights_subBarycenter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem toE_iConvexComb_subBarycenter {m n : ℕ} (q : Fin m → Convexity.StdSimplex ℝ (Fin (n+1)))
    (A : Finset (Fin m)) (hA : A.Nonempty) (j : Fin (n+1)) :
    Work.SingMV.toE (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q) j
      = (A.card : ℝ)⁻¹ * ∑ i ∈ A, Work.SingMV.toE (q i) j := by
  -- The weights of `subBarycenter A hA` are the uniform distribution on `A`.
  have hw := fun i => weights_subBarycenter_apply A hA i
  -- Coordinatewise, a convex combination is the weighted average of the coordinates.
  have h : Work.SingMV.toE (Convexity.iConvexComb (R := ℝ)
        (Convexity.StdSimplex.subBarycenter A hA) q) j
      = ∑ i : Fin m, (if i ∈ A then (A.card : ℝ)⁻¹ else 0) * Work.SingMV.toE (q i) j := by
    show (Convexity.iConvexComb (R := ℝ) (Convexity.StdSimplex.subBarycenter A hA) q).weights j = _
    rw [Work.SingMV.weights_iConvexComb_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw i]
    rfl
  rw [h]
  -- Only the terms with `i ∈ A` contribute, and `1/|A|` factors out of the sum.
  have h2 : ∑ i : Fin m, (if i ∈ A then (A.card : ℝ)⁻¹ else 0) * Work.SingMV.toE (q i) j
      = ∑ i ∈ A, (A.card : ℝ)⁻¹ * Work.SingMV.toE (q i) j := by
    rw [← Finset.sum_subset (Finset.subset_univ A) (fun x _ hx => by simp [hx])]
    exact Finset.sum_congr rfl fun i hi => by simp [hi]
  rw [h2, Finset.mul_sum]

end Work.SingMV
