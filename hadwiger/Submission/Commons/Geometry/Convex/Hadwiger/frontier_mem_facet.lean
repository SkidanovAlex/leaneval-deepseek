import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallelBody_cellDecomposition
import Submission.Commons.Geometry.Convex.Hadwiger.facet_containing_proper_face

open Set
open scoped BigOperators Convex

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]

/-- For a convex set with nonempty interior (hence full-dimensional), the intrinsic
(relative) interior equals the (ambient) interior. -/
lemma relint_eq_interior_of_nonempty_interior {P : Set V} (hPcvx : Convex ℝ P)
    (hint : (interior P).Nonempty) : intrinsicInterior ℝ P = interior P := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_interior_of_mem_intrinsicInterior hPcvx hint hx
  · exact interior_subset_intrinsicInterior

/-- A point of the frontier of a full-dimensional polytope lies in the intrinsic interior of a
proper (nonempty, exposed) face of the polytope. -/
lemma carrier_proper_face_of_frontier (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty)
    {x : V} (hxP : x ∈ P) (hxint : x ∉ interior P) :
    ∃ F : Set V, F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧ x ∈ intrinsicInterior ℝ F := by
  classical
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set V)
  rcases polytope_faceDecomposition u P hP hint with ⟨faces, h1, h2, h3⟩
  rcases h3 x hxP with ⟨F, hFm, hFun⟩
  refine ⟨F, (h1 F hFm.1).1, (h1 F hFm.1).2, ?_, hFm.2⟩
  intro hFP
  apply hxint
  have hrel : x ∈ intrinsicInterior ℝ P := by
    simpa [hFP] using hFm.2
  exact (relint_eq_interior_of_nonempty_interior hPcvx hint) ▸ hrel

theorem frontier_mem_facet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty)
    {x : V} (hxP : x ∈ P) (hxint : x ∉ interior P) :
    ∃ F : Set V, F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      Module.finrank ℝ (affineSpan ℝ (F : Set V)).direction = Module.finrank ℝ V - 1 ∧ x ∈ F := by
  classical
  rcases carrier_proper_face_of_frontier u P hP hint hxP hxint with
    ⟨F, hFne, hFexp, hFproper, hxFrel⟩
  rcases facet_containing_proper_face u P hP hint hFexp hFne hFproper with
    ⟨G, hGne, hGexp, hGproper, hGdim, hFG⟩
  refine ⟨G, hGne, hGexp, hGproper, hGdim, hFG (intrinsicInterior_subset hxFrel)⟩

end Commons.Geometry.Convex.Hadwiger
