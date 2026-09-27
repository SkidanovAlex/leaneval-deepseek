import Mathlib

namespace Work.Sphere

/-- The complement of an arbitrary point `c` in a product of two Euclidean spaces is
homeomorphic to the complement of the origin in the Euclidean space of the concatenated
coordinates: both are `ℝ^{a+b}` with one point removed.  Concretely the map is
`(u, v) ↦ WithLp.toLp 2 (Fin.append u v)` after translating `c` to `0`; it is a homeomorphism
because the topology on `EuclideanSpace ℝ (Fin (a+b))` is the coordinate topology
(`Fin.append_left`, `Fin.append_right`). -/
theorem punctedProd_homeo (a b : ℕ) (c : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) :
    Nonempty (({c}ᶜ : Set (EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (a + b))))) := by
  -- The canonical linear homeomorphism `ℝ^a × ℝ^b ≅ ℝ^{a+b}` (`Fin.append` in coordinates).
  let e : (EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) ≃ₜ
      EuclideanSpace ℝ (Fin (a + b)) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := a) (m := b)).symm.toHomeomorph
  -- Translate by `-e c`, so that `c` goes to `0`.
  let g : (EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) ≃ₜ
      EuclideanSpace ℝ (Fin (a + b)) :=
    e.trans (Homeomorph.addRight (-(e c)))
  have hg : g c = 0 := by simp [g]
  -- A homeomorphism maps the complement of a point to the complement of its image.
  exact ⟨(Homeomorph.image g {c}ᶜ).trans (Homeomorph.setCongr (by
    rw [Set.image_compl_eq g.bijective, Set.image_singleton, hg]))⟩

end Work.Sphere
