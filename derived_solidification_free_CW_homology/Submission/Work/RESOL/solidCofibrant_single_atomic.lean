import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Instances
import Submission.Work.RESOL.SigmaSetup

/-!
AREA RESOL — a single complex concentrated in one degree on a small atomic sum is
solid-cofibrant (B5, the "width 0" base case).

If `M ≅ ∐_j ℤ[S_j]` is a small atomic sum, then applying the single functor `single_n`
(which preserves small coproducts, `HomologicalComplex.single` being a left adjoint-like
colimit-preserving functor) turns this into `single_n M ≅ ∐_j single_n ℤ[S_j]`.  By `AtomProp`
each `single_n ℤ[S_j]` is solid-cofibrant, and by the coproduct closure `CofibrantClosure.sigma`
the coproduct of complexes is, whence `single_n M` is by isomorphism invariance in `K(LCA)`.
-/

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- **A single complex concentrated in one degree on a small atomic sum is solid-cofibrant.**

This is the base case of the induction `solidCofibrant_of_boundedAbove_atomic`: a complex of
atoms which is concentrated in a single degree is a small coproduct of atoms. -/
theorem solidCofibrant_single_atomic (hA : Submission.Blueprint.AtomProp)
    (hC : Work.RESOL.CofibrantClosure) (M : LightCondAb)
    (hM : Work.RESOL.IsAtomicSum M) (n : ℤ) :
    Submission.Blueprint.SolidCofibrant
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) n).obj M) := by
  classical
  obtain ⟨J, S, c, ⟨hc⟩, ⟨eM⟩⟩ := hM
  let F : J → LightCondAb := fun j => (free ℤ).obj (S j).toCondensed
  let Sc : LightCondAb ⥤ Cpx := HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) n
  let q : Cpx ⥤ KCat := HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)
  -- `c.pt` is the coproduct of the atoms, and `Sc` preserves that coproduct.
  have hAe : c.pt ≅ ∐ F := IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)
  have hBe : Sc.obj (∐ F) ≅ ∐ fun j => Sc.obj (F j) := PreservesCoproduct.iso Sc F
  -- the coproduct of the atoms is solid-cofibrant, by `AtomProp` and coproduct closure
  have hsig : Submission.Blueprint.SolidCofibrant (∐ fun j => Sc.obj (F j)) :=
    hC.sigma J (fun j => Sc.obj (F j)) (fun j => hA (S j) n)
  have hsigH : SolidCofibrantH (q.obj (∐ fun j => Sc.obj (F j))) :=
    (solidCofibrant_iff _).mp hsig
  -- transport along the isomorphism `single_n M ≅ ∐_j single_n ℤ[S_j]`
  have e1 : Sc.obj M ≅ ∐ fun j => Sc.obj (F j) := Sc.mapIso (eM ≪≫ hAe) ≪≫ hBe
  have hfinal : SolidCofibrantH (q.obj (Sc.obj M)) :=
    hC.iso (q.mapIso e1.symm) hsigH
  exact (solidCofibrant_iff _).mpr hfinal

end Work.RESOL
