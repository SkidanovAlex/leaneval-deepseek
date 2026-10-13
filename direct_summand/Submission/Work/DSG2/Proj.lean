import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.Glue
import Submission.Work.DSG2.Surj
import Submission.Work.DSG2.PiUProper

/-!
# DSG2: properness of `π` and projectivity of `X'`

Since `IsProper` is Zariski-local at the target, `Work.DSG2.isProper_piU_alt` (proved in
`Submission/Work/DSG2/PiUProper.lean`) gives `IsProper P.hom` for the glued morphism
`P : GluedPi D`; composing with the proper `f : X ⟶ Spec A` and applying the immersion
`X'Proj : X' ⟶ ℙ^M_A` then gives the final conclusions

* `isProper_hom_comp_f : IsProper (P.hom ≫ f)`, and
* `isProjOver_hom_comp_f : IsProjOver A (P.hom ≫ f)`.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

theorem isProper_hom (D : ChowSetup A X f) [IsSeparated f] (P : GluedPi D) :
    IsProper P.hom := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper)
    (fun i => ((D.U i : X.Opens))) D.hUcover]
  intro i
  exact isProper_piU_alt D P i

theorem isProper_hom_comp_f (D : ChowSetup A X f) [IsSeparated f] (P : GluedPi D)
    [IsProper f] : IsProper (P.hom ≫ f) := by
  haveI : IsProper P.hom := isProper_hom D P
  infer_instance

theorem isProjOver_hom_comp_f (D : ChowSetup A X f) [IsSeparated f] (P : GluedPi D)
    [IsProper f] : DSMap.IsProjOver A (P.hom ≫ f) := by
  haveI : IsProper (P.hom ≫ f) := isProper_hom_comp_f D P
  refine ⟨D.M, X'Proj D, ?_, ?_⟩
  · haveI : IsImmersion (X'Proj D) := D.isImmersion_X'Proj
    haveI : IsProper (X'Proj D) := by
      haveI : IsProper (X'Proj D ≫ DSMap.PSpace.toSpec A D.M) := by
        rw [D.X'Proj_comp, ← piCompF P]
        infer_instance
      haveI : IsSeparated (DSMap.PSpace.toSpec A D.M) := isSeparated_pspace_toSpec D.M
      exact IsProper.of_comp (X'Proj D) (DSMap.PSpace.toSpec A D.M)
    exact isClosedImmersion_of_isImmersion_of_isProper (X'Proj D)
  · rw [D.X'Proj_comp, piCompF P]

end ChowSetup

end Work.DSG2
