import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.SetupExists
import Submission.Work.DSG2.Glue
import Submission.Work.DSG2.GlueExists
import Submission.Work.DSG2.Surj
import Submission.Work.DSG2.Proj
import Submission.Work.DSG2.chow_of_isEmpty_u

/-!
# DSG2: Chow's lemma over a Noetherian base

The main theorem `DSMap.area_G2_chow_proved`: for `A` Noetherian and `X` proper over `Spec A`
there is a projective `X'` dominating `X` surjectively (EGA II 5.6.1, Stacks 0200).

The proof splits on whether `X` is empty:

* `X = ∅` : `Work.DSG2.chow_of_isEmpty_u` (take `X' = X`, `g = 𝟙`);
* otherwise: build the Chow data `D : Work.DSG2.ChowSetup A X f`
  (`Work.DSG2.nonempty_chowSetup`), glue `π : X' ⟶ X` (`Work.DSG2.ChowSetup.nonempty_gluedPi`),
  and use surjectivity (`surjective_hom`), properness (`isProper_hom_comp_f`) and projectivity
  (`isProjOver_hom_comp_f`).
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace DSMap

theorem area_G2_chow_proved.{a} (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∃ (X' : Scheme.{a}) (g : X' ⟶ X), Function.Surjective g ∧ IsProper (g ≫ f) ∧
      IsProjOver A (g ≫ f) := by
  by_cases hX : Nonempty X
  · obtain ⟨D⟩ := Work.DSG2.nonempty_chowSetup A X f hX
    obtain ⟨P⟩ := Work.DSG2.ChowSetup.nonempty_gluedPi D
    exact ⟨Work.DSG2.ChowSetup.X' D, P.hom, Work.DSG2.ChowSetup.surjective_hom D P,
      Work.DSG2.ChowSetup.isProper_hom_comp_f D P,
      Work.DSG2.ChowSetup.isProjOver_hom_comp_f D P⟩
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    exact Work.DSG2.chow_of_isEmpty_u A X f

end DSMap
