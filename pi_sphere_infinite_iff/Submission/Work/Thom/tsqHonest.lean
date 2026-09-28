import Mathlib
import Submission.Work.Thom.TransgressionSquare
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Work.TangentClasses

namespace Work.Thom

namespace TsqH

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- Restriction of a relative class of `(X,A)` to the overlap `(U∩V, (U∩V)∩A)`. -/
noncomputable def relRestrOvl (X : TopCat) (A U V : Set X) (n : ℕ) :
    Work.Thom.RelCoh ℤ n X A ⟶
      Work.Thom.RelCoh ℤ n ↥(U ∩ V) (Work.Cohomology.interAU A (U ∩ V)) :=
  Work.Thom.relCohMap (Work.Thom.subtypeMap (U ∩ V))
    (Work.Cohomology.interAU A (U ∩ V)) A
    (fun x hx => hx) ℤ n

/-- **The top comparison map of the transgression square**: cup with a fixed relative class
`b ∈ H^n(X,A)`, from the absolute cohomology of `X` to the relative cohomology of `(X,A)`. -/
noncomputable def Ttop (X : TopCat) (A : Set X) (n : ℕ) (b : Work.Thom.RelCoh ℤ n X A) (j : ℕ) :
    Work.Cohomology.pdCoh X (∅ : Set X) j ⟶ Work.Cohomology.pdCoh X A (j + n) :=
  (Work.Thom.pdCohIso X j).hom
    ≫ ModuleCat.ofHom ((LinearMap.applyₗ b).comp (Work.Thom.mixedCupC ℤ A j n))

/-- **The overlap comparison map of the transgression square**: cup with the restriction of `b` to
the overlap, on the relative cohomology of the overlap. -/
noncomputable def Tov (X : TopCat) (A U V : Set X) (n : ℕ) (b : Work.Thom.RelCoh ℤ n X A)
    (k : ℕ) :
    Work.Cohomology.pdCohSub X (∅ : Set X) (U ∩ V) k
      ⟶ Work.Cohomology.pdCohSub X A (U ∩ V) (k + n) :=
  (Work.Thom.pdCohIso ↥(U ∩ V) k).hom
    ≫ ModuleCat.ofHom
        ((LinearMap.applyₗ ((relRestrOvl X A U V n).hom b)).comp
          (Work.Thom.mixedCupC ℤ (Work.Cohomology.interAU A (U ∩ V)) k n))

/-- **The pullback of the absolute cohomology of the base to the total space.** -/
noncomputable def piTop (Z : RealBundle B F ι) (j : ℕ) :
    Work.Cohomology.pdCoh (TopCat.of B) (∅ : Set B) j
      ⟶ Work.Cohomology.pdCoh (TopCat.of Z.TotalSpace) (∅ : Set Z.TotalSpace) j :=
  (Work.Thom.pdCohIso B j).hom
    ≫ Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ j
    ≫ (Work.Thom.pdCohIso Z.TotalSpace j).inv

/-- **The pullback of the absolute cohomology of the overlap to the total space over the
overlap.** -/
noncomputable def piOv (Z : RealBundle B F ι) (U V : Set B) (k : ℕ) :
    Work.Cohomology.pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) k
      ⟶ Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (∅ : Set Z.TotalSpace)
          (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) k :=
  (Work.Thom.pdCohIso ↥(U ∩ V) k).hom
    ≫ Work.Thom.CohMap (Work.Thom.pieceProj Z (U ∩ V)) ℤ k
    ≫ (Work.Thom.pdCohIso ↥(Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) k).inv

end

end TsqH

end Work.Thom
