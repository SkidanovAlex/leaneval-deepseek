import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.sphere_quotient_projective
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.LensSpaceContinuity

import Submission.Work.Drive.phiCap_eq_phiConf
import Submission.Work.Drive.lensSpace_t2
import Submission.Work.Drive.quotientMap_fibers
import Submission.Work.Drive.phi_surjective
import Submission.Work.Drive.phi_eq_iff

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
/-- **The map `S³ → ℝP³` given by the unit sphere is a quotient map** (it is a continuous surjection
from a compact space to a Hausdorff space). -/
lemma isQuotientMap_projOfUnitSphere :
    Topology.IsQuotientMap (projOfUnitSphere (n := 3)) :=
  IsClosedMap.isQuotientMap
    (fun _ hs => (hs.isCompact.image continuous_projOfUnitSphere).isClosed)
    continuous_projOfUnitSphere surjective_projOfUnitSphere

/-- **The glueing map `phi : S³ → LensSpace` is a quotient map** (it is a continuous surjection from a
compact space to the Hausdorff space `LensSpace`). -/
lemma isQuotientMap_phi : Topology.IsQuotientMap phi := by
  haveI : T2Space LensSpace := lensSpace_t2
  refine IsClosedMap.isQuotientMap (fun _ hs => ?_) continuous_phi phi_surjective
  exact (hs.isCompact.image continuous_phi).isClosed

/-- The fibres of the projection of the unit sphere to `ℝP³` are the antipodal pairs. -/
lemma projOfUnitSphere_eq_iff (v w : unitSphere 3) :
    projOfUnitSphere v = projOfUnitSphere w ↔ w = v ∨ w = -v := by
  rw [projOfUnitSphere_eq v, projOfUnitSphere_eq w]
  exact (Work.Drive.sphere_quotient_projective.2 v.1 w.1 _ _).trans
    (by constructor
        · rintro (h | h)
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · rintro (h | h)
          · exact Or.inl (congrArg Subtype.val h)
          · exact Or.inr (congrArg Subtype.val h))

/-- Specialisation of `Work.Drive.quotientMap_fibers` to the two maps `S³ → LensSpace` and
`S³ → ℝP³`. -/
lemma quotientMap_fibers_spec {q : unitSphere 3 → LensSpace}
    {f : unitSphere 3 → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hq : Topology.IsQuotientMap q) (hf : Topology.IsQuotientMap f)
    (h : ∀ x y, q x = q y ↔ f x = f y) :
    Nonempty (LensSpace ≃ₜ Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
  quotientMap_fibers (X := unitSphere 3) hq hf h

/-- **The glued space of the capping is `ℝP³`.**  The space `Work.Drive.LensSpace` of
`Submission/Work/Drive/CappingSpace` is the quotient of the disjoint union of the cap solid torus
`S¹ × D²` and the configuration solid torus `D² × S¹` which identifies the boundary point `(θ, φ)` of
the cap with the boundary point `(φ, θ + 2φ)` of the configuration torus (through the parametrisation
`bdy` of the boundary circle).  Equivalently, it is the result of gluing two solid tori so that the
meridian of one becomes the `(2,1)`-curve of the other, i.e. the lens space `L(2,1)`, and
`L(2,1) ≅ ℝP³`.  It follows that `π₁` of the glued space is `ℤ/2`.  This is the three-dimensional half
of Hugelmeyer's Lemma 5 (the capping of the configuration Möbius strip); with it the full capping
space is `(0,∞) × LensSpace ≅ ℝ × ℝP³`, in which the capped configuration Möbius strip and its
rotations are homologically non-trivial projective planes, so that Hugelmeyer's total order on such
planes can be used.  All the linear-algebraic facts needed about `ℝP³` itself
(`Projectivization ℝ (EuclideanSpace ℝ (Fin 4))` is Hausdorff, compact, covered by the unit sphere
with antipodal fibres) are already available in `Submission.Work.Drive.ProjectiveTopology` and
`Submission.Work.Drive.sphere_quotient_projective`. -/
theorem lensSpace_homeomorph_projective :
    Nonempty (Work.Drive.LensSpace ≃ₜ
      Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := by
  let g : unitSphere 3 → LensSpace := phi
  let h' : unitSphere 3 → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) := projOfUnitSphere
  have hg : Topology.IsQuotientMap g := isQuotientMap_phi
  have hh : Topology.IsQuotientMap h' := isQuotientMap_projOfUnitSphere
  have hfib : ∀ x y, g x = g y ↔ h' x = h' y := by
    intro x y
    show phi x = phi y ↔ projOfUnitSphere x = projOfUnitSphere y
    rw [phi_eq_iff, projOfUnitSphere_eq_iff]
  exact quotientMap_fibers_spec hg hh hfib

end Work.Drive
