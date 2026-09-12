import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_exposedFace_conv_vertices

open scoped BigOperators
open Set

namespace Commons.Geometry.Convex.Hadwiger

theorem finite_exposedFaces_convexHull (m : ℕ)
    (u : Finset (EuclideanSpace ℝ (Fin m)))
    (P : Set (EuclideanSpace ℝ (Fin m)))
    (hP : P = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m)))) :
    {F : Set (EuclideanSpace ℝ (Fin m)) | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P}.Finite := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let faceSet : Set (Set E) := {F : Set E | IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P}
  change faceSet.Finite
  -- every nonempty exposed face of the polytope is the convex hull of a subset of the vertices
  have hface : ∀ F : Set E, IsExposed ℝ P F → F.Nonempty →
      F = convexHull ℝ ((u.filter (fun x : E => x ∈ F) : Finset E) : Set E) := by
    intro F hF hFne
    have hfilter : ((u.filter (fun x : E => x ∈ F) : Finset E) : Set E) = F ∩ (u : Set E) := by
      ext x
      simp
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hfilter]
    exact polytope_exposedFace_conv_vertices m u P hP hF hFne
  let S : Finset (Set E) := u.powerset.image (fun T : Finset E => convexHull ℝ (T : Set E))
  have hSfin : (S : Set (Set E)).Finite := S.finite_toSet
  have hSub : faceSet ⊆ (S : Set (Set E)) := by
    intro F hF
    rcases hF with ⟨hFexp, hFne, hFneP⟩
    change F ∈ S
    dsimp [S]
    refine Finset.mem_image.mpr ?_
    refine ⟨u.filter (fun x : E => x ∈ F), ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.filter_subset (fun x : E => x ∈ F) u)
    · exact (hface F hFexp hFne).symm
  exact hSfin.subset hSub

end Commons.Geometry.Convex.Hadwiger
