import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.Chain

/-- An affine self-map of `PL.E N` which fixes every vertex of a finite vertex set `t` fixes the
whole simplex `PL.simp t = convexHull ℝ t` pointwise.  (Barycentric coordinates: if
`x = ∑ c v • v` with `∑ c v = 1` and `A v = v` for `v ∈ t`, then
`A x = A.linear x + A 0 = ∑ c v • (v - A 0) + A 0 = x`.) -/
theorem affineMap_fix_simp {N : ℕ} (A : PL.E N →ᵃ[ℝ] PL.E N) {t : Finset (PL.E N)}
    (h : ∀ v ∈ t, A v = v) : ∀ x ∈ PL.simp t, A x = x := by
  -- `A` and the identity agree on the vertex set `t`, hence on its affine span.
  have h_agree : Set.EqOn A (AffineMap.id ℝ (PL.E N)) (t : Set (PL.E N)) := by
    intro v hv
    simpa using h v hv
  have key : Set.EqOn A (AffineMap.id ℝ (PL.E N)) (affineSpan ℝ (t : Set (PL.E N))) :=
    AffineMap.eqOn_affineSpan h_agree
  -- The simplex is contained in the affine span of its vertices.
  intro x hx
  have hx' : x ∈ (affineSpan ℝ (t : Set (PL.E N)) : Set (PL.E N)) :=
    convexHull_subset_affineSpan (t : Set (PL.E N)) hx
  simpa using key hx'

end Work.Engulf.Chain
