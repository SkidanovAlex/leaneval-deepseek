import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Near

open Set Metric

/-- If `ℓ` is affine on every simplex of a subdivision `K'` of `K`, agrees with `f` at the
vertices of `K'`, and `f` oscillates by less than `ε'` on every simplex of `K'`, then `ℓ` and `f`
are uniformly within `ε'` on the whole space of `K`. -/
lemma dist_lt_of_linOn {N n : ℕ} (K K' : PL.Cx N) (hsub : PL.Subdivides K' K) {ε' : ℝ} (hε' : 0 < ε')
    (f ℓ : PL.E N → PL.E n) (hlin : PL.LinOn K' ℓ)
    (hvert : ∀ s ∈ K'.faces, ∀ v ∈ s, ℓ v = f v)
    (hosc : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε') :
    ∀ x ∈ K.space, dist (ℓ x) (f x) < ε' := by
  intro x hx
  have hx' : x ∈ K'.space := by rw [hsub.1]; exact hx
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx'
  obtain ⟨s, hs, hxs⟩ := hx'
  obtain ⟨A, hA⟩ := hlin s hs
  have hℓx : ℓ x = A x := hA hxs
  -- the affine map `A` sends the simplex `s` into the convex hull of the images of its vertices
  have himg : A '' (s : Set (PL.E N)) = f '' (s : Set (PL.E N)) := by
    refine Set.image_congr fun v hv => ?_
    exact (hA (subset_convexHull ℝ (s : Set (PL.E N)) hv)).symm.trans (hvert s hs v hv)
  have hAconv : A x ∈ convexHull ℝ (f '' (s : Set (PL.E N))) := by
    rw [← himg, ← AffineMap.image_convexHull A (s : Set (PL.E N))]
    exact mem_image_of_mem A hxs
  -- `f` maps the vertices of `s` into the open ball of radius `ε'` around `f x`
  have hball : f '' (s : Set (PL.E N)) ⊆ ball (f x) ε' := by
    rintro y ⟨v, hv, rfl⟩
    rw [mem_ball]
    exact hosc s hs v (subset_convexHull ℝ (s : Set (PL.E N)) hv) x hxs
  have hmem : A x ∈ ball (f x) ε' :=
    convexHull_min hball (convex_ball _ _) hAconv
  rw [mem_ball] at hmem
  rw [hℓx]
  exact hmem

end Work.PL.Approx.Near
