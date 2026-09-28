import Mathlib
import Submission.Work.Serre.DiscPair.cylBotTrimDefs
import Submission.Work.Serre.DiscPair.cylBotTrimExcision
import Submission.Work.Serre.DiscPair.cylBotTrimShrink
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Cohomology.cohomologicalExcision

open CategoryTheory

namespace Work.Serre.DiscPair

theorem relCoh_cylBot_trimming {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℚ n
        ↥{x : ↥(Work.Serre.cylPre q V) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
        {y : ↥{x : ↥(Work.Serre.cylPre q V) |
              (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
                (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S} |
          ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}
      ≅ Work.Thom.RelCoh ℚ n
        ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q}
        {y : ↥{x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q} |
          ((y : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  -- Restrict the left-hand pair to the flattened subtype `trimA q S ∩ cylPre q V`.
  obtain ⟨e1⟩ := relCoh_subtype_restrict (Work.Serre.cylPre q V) (trimA q S)
    (Work.Serre.cylPre q S) ℚ n
  -- Excise the top of the mapping cylinder.
  obtain ⟨e2⟩ := cylBotTrimExcision q S V hSV n
  -- Shrink the collar onto the bottom copy.
  obtain ⟨e3⟩ := cylBotTrimShrink q S V hSV n
  -- Flatten the bottom-copy pair.
  obtain ⟨e4⟩ := relCoh_subtype_restrict (Work.Serre.cylPre q V) (Work.Serre.cylBot q)
    (Work.Serre.cylPre q S) ℚ n
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4.symm⟩

end Work.Serre.DiscPair
