import Mathlib
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.pathConnected_sph
import Submission.Work.Cohomology.H_zero_connected

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The degree `0` cohomology of the intersection of the two pieces of the Mayer–Vietoris cover
of `S^{a+1} × Y` pulled back from the first factor is one dimensional, when `a ≥ 1` and `Y` is path
connected.  Indeed, the intersection is (the singular complex of) `DPset a × Y`, where the doubly
punctured sphere `DPset a` is homotopy equivalent to `S^a`, and `S^a × Y` is path connected. -/
theorem H_zero_fstAsub_inf_fstBsub (a : ℕ) (ha : 1 ≤ a) (Y : TopCat.{0}) [PathConnectedSpace ↥Y] :
    Nonempty (Submission.Cohomology.H
        (Work.Sphere.fstAsub (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
          (Submission.Sphere.capMinus a) ⊓
         Work.Sphere.fstBsub (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
          (Submission.Sphere.capMinus a) :
          ((Work.Sphere.fstSmall (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
            (Submission.Sphere.capMinus a)) : SSet).Subcomplex) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  haveI hpcS : PathConnectedSpace (Submission.Sphere.Sph a) :=
    Work.Sphere.pathConnected_sph a ha
  haveI hpcProd : PathConnectedSpace ↥(TopProd (Submission.Sphere.Sph a) Y) := by
    show PathConnectedSpace ((↥(Submission.Sphere.Sph a)) × (↥Y))
    infer_instance
  -- the intersection of the two pieces is the subcomplex of the doubly punctured sphere
  obtain ⟨e1⟩ := Submission.Sphere.H_iso_of_iso (SSet.Subcomplex.eqToIso
    (fstAsub_inf_fstBsub (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
      (Submission.Sphere.capMinus a))) 0
  -- that subcomplex is the singular complex of `(capPlus a ∩ capMinus a) × Y`
  obtain ⟨e2⟩ := H_fstCsub_homeo (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
    (Submission.Sphere.capMinus a) 0
  rw [Submission.Sphere.capPlus_inter_capMinus_eq_DPset a] at e2
  -- and `DPset a × Y` may be replaced by `S^a × Y`
  obtain ⟨e3⟩ := H_DPset_prod_iso a Y 0
  -- finally `H⁰` of a path connected space is `ℚ`
  obtain ⟨e4⟩ := Work.Cohomology.H_zero_connected (TopProd (Submission.Sphere.Sph a) Y)
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

end

end Work.Sphere
